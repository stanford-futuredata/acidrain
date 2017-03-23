#!/usr/bin/env python

from enum import Enum

import argparse
import datetime
import re
import sqlparse
import sys
import time

# THINGS TO DO:
# Add all columns to insert WS
# Add all columns to delete WS
# Read the write set of the thing
# see if the column of interest is in it
# if so, add the whole trace to the list of anomalies

# Can be extended with count, sum, etc.
class ReadType(Enum):
    star = 1
    cols = 2

class EdgeType(Enum):
    RW = 1
    WW = 2

class ValueType(Enum):
    unknown = 1
    string = 2
    integer = 3
    floating = 4

class KeyType(Enum):
    pri = 1
    uni = 2
    mul = 3

class DbColType(Enum):
    intlike = 1
    floatlike = 2
    stringlike = 3
    datetimelike = 5

class QueryType(Enum):
    notQuery = 1
    other = 2
    select = 3
    update = 4
    insert = 5
    delete = 6
    startTxn = 7
    endTxn = 8
    startTxnCond = 9 # set autocommit=0 starts a transaction if none is started
    endTxnCond = 10 # set autocommit=1 commits a transaction if there is one

class OpNode:
    def __init__(self, nodeId, logObj, txnNode, apiNode, forUpdates):
        self.edgeMap = {}
        self.nodeId = nodeId
        self.edges = []
        self.txn = txnNode
        self.api = apiNode
        # Should only matter if op1 and op2 of dfs are in select for update, otherwise it will
        # be scope based anomaly.  If they are, cannot go through any ops that have the same
        # select for updates in place, or read or write any of the variables relevant to the select
        # for update
        self.forUpdates = forUpdates
        self.logObj = logObj

class TxnNode:
    def __init__(self, nodeId, apiNode):
        self.edgeMap = {}
        self.nodeId = nodeId
        self.edges = []
        self.ops = []
        self.api = apiNode

class ApiNode:
    def __init__(self, nodeId):
        self.edgeMap = {}
        self.nodeId = nodeId
        self.edges = []
        self.ops = []
        self.txns = []
        # The operations to which this node has an edge, used in our modified
        # multilevel DFS.  Mapping from nodeId to Edge  Note that the op
        # could be in this API node itself.
        self.reachableOps = {}

class Edge:
    def __init__(self, op1, op2, edgeType):
        self.op1 = op1
        self.op2 = op2
        self.txn1 = op1.txn
        self.txn2 = op2.txn
        self.api1 = op1.api
        self.api2 = op2.api
        self.edgeType = edgeType

class AbstractHistory:
    def __init__(self):
        self.nodeMapping = {}
        self.logObjMapping = {}
        self.ops = []
        self.txns = []
        self.apis = []
        self.totalEdges = 0
        self.nextId = 0

    def addOpNode(self, logObj, txnNode, apiNode, forUpdates):
        newOp = OpNode(self.nextId, logObj, txnNode, apiNode, forUpdates)
        self.ops.append(newOp)
        txnNode.ops.append(newOp)
        apiNode.ops.append(newOp)
        self.nextId += 1
        self.nodeMapping[newOp.nodeId] = newOp
        self.logObjMapping[logObj.uniqueId] = newOp
        return newOp

    def addTxnNode(self, apiNode):
        newTxn = TxnNode(self.nextId, apiNode)
        self.txns.append(newTxn)
        apiNode.txns.append(newTxn)
        self.nextId += 1
        self.nodeMapping[newTxn.nodeId] = newTxn
        return newTxn

    def addApiNode(self):
        newApi = ApiNode(self.nextId)
        self.apis.append(newApi)
        self.nextId += 1
        self.nodeMapping[newApi.nodeId] = newApi
        return newApi

    def addEdge(self, op1, op2, edgeType):
        self.totalEdges += 1
        edge1 = Edge(op1, op2, edgeType)
        edge2 = Edge(op2, op1, edgeType)
        txn1 = op1.txn
        txn2 = op2.txn
        api1 = op1.api
        api2 = op2.api
        op1.edges.append(edge1)
        op2.edges.append(edge2)
        op1.edgeMap[op2.nodeId] = edge1
        op2.edgeMap[op1.nodeId] = edge2
        txn1.edges.append(edge1)
        txn2.edges.append(edge2)
        api1.edges.append(edge1)
        api2.edges.append(edge2)
        lst1 = api1.reachableOps.get(op2.nodeId, [])
        lst1.append(edge1)
        api1.reachableOps[op2.nodeId] = lst1
        lst2 = api2.reachableOps.get(op1.nodeId, [])
        lst2.append(edge2)
        api2.reachableOps[op1.nodeId] = lst2

    def addSelfLoop(self, op):
        self.totalEdges += 1
        edge = Edge(op, op, EdgeType.WW)
        op.edges.append(edge)
        op.edgeMap[op.nodeId] = edge
        op.txn.edges.append(edge)
        op.api.edges.append(edge)
        lst = op.api.reachableOps.get(op.nodeId, [])
        lst.append(edge)
        op.api.reachableOps[op.nodeId] = lst

    def getNode(self, nodeId):
        return self.nodeMapping[nodeId]

    # Simplified version of depth first search to find simple anomalies.
    # Focus on interesting to trigger AKA two api calls.  Therefore,
    # Each path of anomalies will consist of at most two ops, so return a list
    # of lists where each inner list is either one or two ops used in the anomaly.
    # The outer list will be empty if no anomaly is possible.
    def find_potential_anomalies(self, op1, op2):
        assert(op1.api == op2.api)
        anomalyCausations = list()
        toCheck = []
        visited = {}
        edgesUsed = []
        reachedBy = {}
        for edge in op1.edges:
            if edge.api2.nodeId not in visited:
                # Tuple of next api node to check, the edge we came from, and whether we
                # should follow the edge by api (1) or by op (0)
                toCheck.append((edge.api2, edge, 0))
                visited[edge.api2.nodeId] = True
        visited = {}
        while len(toCheck) > 0:
            (curApi, reachedByEdge, followOp) = toCheck.pop()
            if curApi.nodeId in visited:
                continue
            reachedBy[curApi.nodeId] = (reachedByEdge, followOp)
            visited[curApi.nodeId] = True
            if op2.nodeId in curApi.reachableOps:
                reachedBy[op2.nodeId] = (curApi.reachableOps[op2.nodeId][0], 1)
                break
            else:
                for edge in curApi.edges:
                    toCheck.append((edge.api2, edge, 1))
        if op2.nodeId in reachedBy:
            (edge, followOp) = reachedBy[op2.nodeId]
            path = [edge]
            while edge.op1.nodeId != op1.nodeId:
                nodeId = edge.api1.nodeId
                if followOp == 0:
                    nodeId = edge.op1.nodeId
                (edge, followOp) = reachedBy[nodeId]
                path.append(edge)
            path = list(reversed(path))
            return path
        else:
            return None

class TableRead:
    def __init__(self):
        self.reads = {}
        self.colsRead = []

    def _strHelper(self):
        strList = []
        if ReadType.star in self.reads:
            strList.append('*')
        strList += self.colsRead
        return str(strList)

    def __str__(self):
        return self._strHelper()

    def __repr__(self):
        return self._strHelper()

class DbSchema:
    def __init__(self):
        self.tables = {}
        self.colTypes = {}
        self.colDefaults = {}
        self.colKeys = {}

    def add(self, tableName, colName, colType, colDefault, colKey):
        colList = self.tables.get(tableName, [])
        colList.append(colName)
        self.tables[tableName] = colList
        key = (tableName, colName)
        if colKey == 'PRI':
            self.colKeys[key] = KeyType.pri
        elif colKey == 'UNI':
            self.colKeys[key] = KeyType.pri
        elif colKey == 'MUL':
            self.colKeys[key] = KeyType.pri
        if 'int' in colType:
            self.colTypes[key] = DbColType.intlike
        elif 'decimal' in colType or 'double' in colType:
            self.colTypes[key] = DbColType.floatlike
        elif 'datetime' in colType:
            self.colTypes[key] = DbColType.datetimelike
        else:
            self.colTypes[key] = DbColType.stringlike
        self.colDefaults[key] = colDefault

class LogObject:
    def __init__(self, timestamp, threadId, command, commArg, dbSchema, uid):
        # Some identifier unique to the log for this program (e.g. it's line number)
        self.uniqueId = uid
        self.dbSchema = dbSchema
        self.timestamp = timestamp
        self.threadId = threadId
        self.command = command
        # Store the original comm arg to not be cleaned as well
        self.origCommArg = commArg
        self.commArg = self._cleanCommArg(commArg)
        self.parsed = self._parseQueryCommArg()
        self.queryType = self._calcQueryType()
        self.writeSet = None
        self.readSet = None
        self.aliases = None
        # The table in a select statement that unprefixed column names refers to
        self.primaryTable = None
        self.lowerCasedPT = False
        self.tables = None
        self.isNoop = None
        self.whereFilter = None

    def isWrite(self):
        return ((self.queryType == QueryType.insert) or
            (self.queryType == QueryType.update) or
            (self.queryType == QueryType.delete))

    def isRead(self):
        return self.queryType == QueryType.select

    # Remove some symbols that may make our string matching not work
    def _cleanCommArg(self, commArg):
        if (self.command == 'Query'):
            commArg = commArg.replace('`', '')
        return commArg

    # Parse the query command arg
    def _parseQueryCommArg(self):
        if (self.command == 'Query'):
            return sqlparse.parse(self.commArg)[0]
        return None

    def _calcQueryType(self):
        if (self.parsed):
            command = self.parsed.tokens[0].value.upper()
            # Some other commands will fail the upper() conversion, but we don't care
            # since the txn commands won't that that's why we need this
            try:
                commandTxnTest = str(self.parsed).upper()
            except:
                pass
            if command == 'SELECT':
                return QueryType.select
            elif command == 'INSERT':
                return QueryType.insert
            elif command == 'UPDATE':
                return QueryType.update
            elif command == 'DELETE':
                return QueryType.delete
            elif (commandTxnTest == 'BEGIN' or
                  commandTxnTest == 'START TRANSACTION'):
                return QueryType.startTxn
            elif (commandTxnTest == 'COMMIT' or
                  commandTxnTest == 'ROLLBACK'):
                return QueryType.endTxn
            elif commandTxnTest == 'SET AUTOCOMMIT=0':
                return QueryType.startTxnCond
            elif commandTxnTest == 'SET AUTOCOMMIT=1':
                return QueryType.endTxnCond
            else:
                return QueryType.other
        return QueryType.notQuery

    def isSelectForUpdate(self):
        if self.queryType != QueryType.select:
            return False
        else:
           return (self.parsed.tokens[-1].value.upper() == 'UPDATE' and
                   self.parsed.tokens[-3].value.upper() == 'FOR')

    def getPrimaryTable(self):
        if (self.primaryTable != None):
            if not self.lowerCasedPT:
                self.lowerCasedPT = True
                self.primaryTable = self.primaryTable.lower()
            return self.primaryTable
        else:
            self.getTables()
            self.lowerCasedPT = True
            self.primaryTable = self.primaryTable.lower()
            return self.primaryTable

    def getAliases(self):
        if (self.aliases != None):
            return self.aliases
        if self.queryType == QueryType.select:
            self.aliases = self._getAliasesSelect()
        else:
            pt = self.getPrimaryTable()
            self.aliases = {pt: pt}
        return self.aliases

    def _getAliasesSelect(self):
        aliases = {}
        addNextIdentifier = False
        foundFrom = False
        for t in self.parsed.tokens:
            if (t.ttype == sqlparse.tokens.Keyword):
                if (t.value.upper() == 'FROM'):
                    foundFrom = True
                    addNextIdentifier = True
                if ('JOIN' in t.value.upper()):
                    addNextIdentifier = True
            if ((t.__class__ == sqlparse.sql.Identifier or
                t.__class__ == sqlparse.sql.IdentifierList) and addNextIdentifier):
                if t.__class__ == sqlparse.sql.IdentifierList:
                    for subToken in t.tokens:
                        if subToken.__class__ == sqlparse.sql.Identifier:
                            # We don't handle subqueries right now, so just skip it
                            if ('SELECT' not in str(t)):
                                aliases[subToken.tokens[-1].value] = subToken.tokens[0].value
                            # We even let the fromTable be a select statement, nothing really goes
                            # wrong but no other queries will match it (saves some extra checks
                            # in getting the read set).  Also this is not technically correct if
                            # there are multiple from tables but that is a rare case
                            if (foundFrom and not self.primaryTable):
                                self.primaryTable = subToken.tokens[0].value
                else:
                    # We don't handle subqueries right now, so just skip it
                    if ('SELECT' not in str(t)):
                        aliases[t.tokens[-1].value] = t.tokens[0].value
                    # We even let the fromTable be a select statement, nothing really goes
                    # wrong but no other queries will match it (saves some extra checks
                    # in getting the read set
                    if (foundFrom):
                        self.primaryTable = t.tokens[0].value
                foundFrom = False
                addNextIdentifier = False
        # This case has only so far occured with FOUND_ROWS()
        if (self.primaryTable == None):
            self.primaryTable = ''
        return aliases

    def getReadSet(self):
        if (self.readSet != None):
            return self.readSet
        if self.queryType == QueryType.select:
            aliases = self.getAliases()
            fromIdx = 0
            idx = 0
            readSet = {}
            for tbl in self.getTables():
                readSet[tbl] = TableRead()
            for t in self.parsed.tokens:
                if (t.ttype == sqlparse.tokens.Keyword and
                        t.value.upper() == 'FROM'):
                    fromIdx = idx
                    break
                idx += 1
            if (fromIdx == 0):
                # This case has only so far occured with FOUND_ROWS()
                self.readSet = lowerCaseKeys(readSet)
                return self.readSet
            curIdx = fromIdx - 1
            while (self.parsed.tokens[curIdx].ttype != sqlparse.tokens.Keyword.DML):
                curIdx -= 1
            acc = ''
            for t in self.parsed.tokens[curIdx+1:fromIdx]:
                acc += str(t)
            readSplit = splitUncaptured(acc, '(', ')')
            # sqlparse captures some sql keywords as part of the first read value
            # so we do a nasty hack - just say all the things we should skip over
            skippableWords = ['ALL', 'DISTINCT', 'DISTINCTION', 'HIGH_PRIORITY',
                    'STRAIGHT_JOIN', 'SQL_SMALL_STATEMENT', 'SQL_BIG_RESULT',
                    'SQL_BUFFER_RESULT', 'SQL_CACHE', 'SQL_NO_CACHE',
                    'SQL_CALC_FOUND_ROWS']
            firstReadHelper = readSplit[0].split(' ')
            idx = 0
            for token in firstReadHelper:
                if token not in skippableWords:
                    break
                idx += 1
            readSplit[0] = ' '.join(firstReadHelper[idx:])
            for read in readSplit:
                # Skip nested queries
                if 'SELECT' in read:
                    continue
                # This filters out functions and control flow.
                # After testing, it only filters out 4 queries we care about so leaving it for now
                if '(' in read:
                    continue
                dotSplit = findFirstNonEmpty(read.split(' '), '', False).split('.')
                if (len(dotSplit) == 2):
                    reads = readSet.get(aliases[dotSplit[0]], TableRead())
                    if '*' == dotSplit[1]:
                        reads.reads[ReadType.star] = '1'
                    else:
                        reads.reads[ReadType.cols] = '1'
                        reads.colsRead.append(dotSplit[1])
                    readSet[aliases[dotSplit[0]]] = reads
                elif (len(dotSplit) == 1):
                    if '*' == dotSplit[0]:
                        for tbl in aliases.values():
                            reads = readSet.get(tbl, TableRead())
                            reads.reads[ReadType.star] = '1'
                            readSet[tbl] = reads
                    else:
                        reads = readSet.get(self.primaryTable, TableRead())
                        reads.reads[ReadType.cols] = '1'
                        reads.colsRead.append(dotSplit[0])
                        readSet[self.primaryTable] = reads
                else:
                    raise Exception('Unexpected number of periods in column identifier')
            self.readSet = readSet
        else:
            self.readSet = {}
        self.readSet = lowerCaseKeys(self.readSet)
        return self.readSet

    # Returns the write set in the form of a mapping from columns to value
    # A mapping to None indicates that the column was set in terms of some other column 
    def getWriteSet(self):
        if (self.writeSet != None):
            return self.writeSet
        writeSet = {}
        if self.queryType == QueryType.insert:
            writeSet = self._getWriteSetInsert()
        elif self.queryType == QueryType.update:
            writeSet = self._getWriteSetUpdate()
        elif self.queryType == QueryType.delete:
            for col in self.dbSchema.tables[self.getPrimaryTable()]:
                writeSet[col] = None
        self.writeSet = writeSet
        return self.writeSet

    def _getWriteSetUpdate(self):
        idxSet = 0
        idxWhere = 0
        for idx in xrange(0, len(self.parsed.tokens)):
            t = self.parsed.tokens[idx]
            if (t.ttype == sqlparse.tokens.Keyword and
                t.value.upper() == 'SET'):
                idxSet = idx
            if (t.__class__ == sqlparse.sql.Where):
                idxWhere = idx
        # All updates in logs we have seen have both SET and WHERE in them
        if (idxSet == 0 or idxWhere == 0):
            raise Exception('This should never be reached in getWriteSetUpdate')
        return self._getWriteSetSETSyntax(self.parsed.tokens[idxSet+1:idxWhere])

    # This handles both the INSERT ... VALUES syntax and INSERT ... SET syntax
    # Due to quirkiness of sqlparse, this does not handle "ON DUPLICATE KEY UPDATE"
    # That can easily be added once we come across and app that uses that feature.
    def _getWriteSetInsert(self):
        writeSet = None
        for idx in xrange(0, len(self.parsed.tokens)):
            t = self.parsed.tokens[idx]
            if (t.ttype == sqlparse.tokens.Keyword and
                t.value.upper() == 'SET'):
                writeSet = self._getWriteSetSETSyntax(self.parsed.tokens[idx + 2:])
            if (t.ttype == sqlparse.tokens.Keyword and
                (t.value.upper() == 'VALUES' or t.value.upper() == 'VALUE')):
                writeSet = self._getWriteSetInsertValueSyntax(
                        self.parsed.tokens[idx + 2:], self.parsed.tokens[idx - 2])
        if writeSet != None:
            try:
                cols =  self.dbSchema.tables[self.getPrimaryTable()]
            except:
                # This happens when writing to a temporary table, which we don't handle for now
                return {}
            for col in cols:
                if col not in writeSet:
                    writeSet[col] = None
            return writeSet
        raise Exception('This should never be reached in getWriteSetInsert')

    def _getWriteSetSETSyntax(self, colsAndVals):
        writeMapping = {}
        acc = ''
        # Stringify the input so that we can parse it ourselves since sqlparse
        # does not appear to do this correctly
        for token in colsAndVals:
            acc += str(token)
        for colAndVal in splitUnquoted(acc, ','):
            eqIdx = colAndVal.index('=')
            col = colAndVal[0:eqIdx].split('.')[-1].strip()
            val = colAndVal[eqIdx+1:].strip()
            self._insertIntoWriteMapWithCast(writeMapping, col, val)
        return writeMapping

    def _getWriteSetInsertValueSyntax(self, vals, cols):
        writeMapping = {}
        # Stringify the input so that we can parse it ourselves since sqlparse
        # does not appear to do this correctly
        accV = ""
        for token in vals:
            accV += token.value
        # The case where the columns are specified, assume that sqlparse will
        # treat this as a function and the columns are the arguments (validated on all apps)
        colOrder = []
        if cols.__class__ == sqlparse.sql.Function:
            colNames = cols.tokens[2].value
            # Strip surrounding parentheses
            colNames = colNames[1:-1]
            for s in colNames.split(','):
                s = s.strip()
                colOrder.append(s)
        else:
            return {}
            # Uncomment below to test new logs for unhandled case
            #raise Exception('Only handle case where cols are specified explicitly')
        if (accV[-1] != ')'):
            raise Exception('not ending in paren')
        accV = accV[1:-1]
        accV = splitUnquoted(accV, ')')[0]
        splitVals = splitUnquoted(accV, ',')
        for idx in xrange(0, len(splitVals)):
            col = colOrder[idx]
            val = splitVals[idx].strip()
            self._insertIntoWriteMapWithCast(writeMapping, col, val)
        return writeMapping

    def _insertIntoWriteMapWithCast(self, writeMapping, col, val):
        pt = self.getPrimaryTable()
        inQuotes = False
        if ((val[0] == "'" and val[-1] == "'")
            or (val[0] == '"' and val[-1] == '"')):
            inQuotes = True
            val = val[1:-1]
        if self.dbSchema.colTypes[(pt, col)] == DbColType.stringlike:
            if not inQuotes and val != 'NULL' and val != '\N':
                val = None
        if self.dbSchema.colTypes[(pt, col)] == DbColType.intlike:
            try:
                val = int(val)
            except:
                val = None
        if self.dbSchema.colTypes[(pt, col)] == DbColType.floatlike:
            try:
                val = float(val)
            except:
                val = None
        writeMapping[col] = val

    # Returns a mapping from columns to values.
    # This allows us to do a very simple analyses where we treat each check in the WHERE
    # as a big OR, which could/should be refined in the future
    # Col -> [] indicates that it is not an equality mapping, so do not check value
    #   when checking overlap.  This can be extended in the future if necessary
    def getWhereFilter(self):
        if self.whereFilter != None:
            return self.whereFilter
        if (self.queryType == QueryType.select or
            self.queryType == QueryType.update or
            self.queryType == QueryType.delete):
            aliases = self.getAliases()
            whereToken = None
            filterMap = {}
            for tbl in self.getTables():
                filterMap[tbl] = {}
            for t in self.parsed.tokens:
                if (t.__class__ == sqlparse.sql.Where):
                    whereToken = t
            # No Where clause
            if (whereToken == None):
                return filterMap
            helperObj = {'waitingForConjunction': False,
                         'skipToNextConjunction': False}
            # Hacky way to remove NOOP queries
            if "1=0" in str(whereToken):
                self.isNoop = True
                return filterMap
            self.isNoop = False
            # Don't include the actual WHERE keyword itself
            self._getWhereFilterHelper(whereToken.tokens[1:], filterMap, helperObj)
            # TODO Add implied information about joined table filtering
            self.whereFilter = lowerCaseKeys(filterMap)
            return self.whereFilter
        else:
            print(self.origCommArg)
            raise Exception('Trying to get where clause for invalid query type')

    # Does the dirty work of parsing a WHERE clause
    # Most assumptions are documented in the code in comments, exceptions,
    # or setting skipToNextConjunction
    def _getWhereFilterHelper(self, clauseTokens, filterMap, helperObj):
        aliases = self.getAliases()
        pt = self.getPrimaryTable()
        foundIdentifier = False
        curComparison = None
        seenIn = False
        seenIs = False
        seenLike = False
        seenValue = False
        seenFunction = False
        seenBetween = False
        seenAnd = False
        # Helps with the case where an identifier is mistaken for a keyword
        expectingIdentifier = True
        stringStart = None
        numStart = None
        for t in clauseTokens:
            tUpperStr = str(t).upper()
            if helperObj['skipToNextConjunction']:
                if tUpperStr == 'AND' or tUpperStr == 'OR':
                    helperObj['waitingForConjunction'] = False
                    foundIdentifier = False
                    curComparison = None
                    seenIn = False
                    seenIs = False
                    seenLike = False
                    seenValue = False
                    seenFunction = False
                    seenBetween = False
                    seenAnd = False
                    expectingIdentifier = True
                    stringStart = None
                    numStart = None
                    helperObj['skipToNextConjunction'] = False
                else:
                    continue
            if t.__class__ == sqlparse.sql.Comparison:
                if foundIdentifier or curComparison != None:
                    raise Exception('Unexpected comparison class placement')
                self._getWhereFilterHelper(t.tokens, filterMap, helperObj)
            elif t.__class__ == sqlparse.sql.Identifier:
                if ((tUpperStr[0] == "'" and tUpperStr[-1] == "'") or
                    (tUpperStr[0] == '"' and tUpperStr[-1] == '"')):
                    seenValue = True
                    if foundIdentifier and curComparison != None:
                        self._insertWhereTblAndCol(filterMap, tbl, col, str(t),
                                curComparison, ValueType.string)
                    elif (foundIdentifier and seenLike) or (seenBetween and seenAnd):
                        self._insertWhereTblAndCol(filterMap, tbl, col, None,
                                None, ValueType.unknown)
                    else:
                        stringStart = str(t)
                        expectingIdentifier = False
                elif ((stringStart != None and (seenLike or seenBetween or curComparison != None)) or
                    (numStart != None and curComparison != None)):
                    if len(t.tokens) == 1:
                        tbl = pt
                        col = str(t.tokens[0])
                    elif len(t.tokens) == 3:
                        tbl = aliases[str(t.tokens[0])]
                        col = str(t.tokens[2])
                    else:
                        raise Exception('Unexpected length of identifier tokens')
                    seenValue = True
                    if stringStart != None:
                        self._insertWhereTblAndCol(filterMap, tbl, col, stringStart,
                                curComparison, ValueType.string)
                    else:
                        self._insertWhereTblAndCol(filterMap, tbl, col, numStart,
                                curComparison, ValueType.integer) # may have to separate int and float here
                    helperObj['waitingForConjunction'] = seenLike or (seenBetween and seenAnd)
                elif foundIdentifier and curComparison != None:
                    seenValue = True
                    self._insertWhereTblAndCol(filterMap, tbl, col, None,
                            curComparison, ValueType.unknown)
                elif not helperObj['waitingForConjunction']:
                    foundIdentifier = True
                    expectingIdentifier = False
                    if len(t.tokens) == 1:
                        tbl = pt
                        col = str(t.tokens[0])
                    elif len(t.tokens) == 3:
                        tbl = aliases[str(t.tokens[0])]
                        col = str(t.tokens[2])
                    else:
                        raise Exception('Unexpected length of identifier tokens')
                else:
                    raise Exception('Unexpected Identifier')
            elif t.__class__ == sqlparse.sql.Parenthesis:
                # Here we assume that anything we could compare to in parentheses is not
                # something we would handle, so add the empty list to the map
                if foundIdentifier and (seenIn or curComparison):
                    self._insertWhereTblAndCol(filterMap, tbl, col, None,
                            None, ValueType.unknown)
                    helperObj['waitingForConjunction'] = True
                    seenValue = True
                elif foundIdentifier or seenIn or curComparison:
                    raise Exception('Only one of foundIdentifier and seenIn are set')
                else:
                    # Chop off the parentheses themselves
                    self._getWhereFilterHelper(t.tokens[1:-1], filterMap, helperObj)
            elif t.__class__ == sqlparse.sql.Function:
                if foundIdentifier and curComparison != None:
                    self._insertWhereTblAndCol(filterMap, tbl, col, None,
                            None, ValueType.unknown)
                    seenValue = True
                    helperObj['waitingForConjunction'] = True
                elif foundIdentifier or curComparison != None:
                    raise Exception('Only one of foundIdentifier and curComparison are set')
                else:
                    seenFunction = True
                    expectingIdentifier = False
                    continue # Don't try to handle what happens inside of a function
            elif t.__class__ == sqlparse.sql.Token:
                if t.ttype == sqlparse.tokens.Whitespace:
                    continue
                elif t.ttype == sqlparse.tokens.Keyword:
                    if helperObj['waitingForConjunction'] and (tUpperStr == 'AND' or tUpperStr == 'OR'):
                        helperObj['waitingForConjunction'] = False
                        foundIdentifier = False
                        curComparison = None
                        seenIn = False
                        seenIs = False
                        seenLike = False
                        seenValue = False
                        seenFunction = False
                        seenBetween = False
                        seenAnd = False
                        expectingIdentifier = True
                        stringStart = None
                        numStart = None
                        helperObj['skipToNextConjunction'] = False
                    elif seenBetween and tUpperStr == 'AND':
                        seenAnd = True
                    elif foundIdentifier:
                        if (tUpperStr not in ['NOT', 'LIKE', 'IS', 'IN', 'NULL', 'NOT NULL', 'BETWEEN'] and
                            not (helperObj['waitingForConjunction'] and tUpperStr in ['AND', 'OR'])):
                            raise Exception('Unexpected keyword following identifier')
                        else:
                            if curComparison != None and not seenValue:
                                raise Exception('Unexpected value for curComparison')
                            helperObj['waitingForConjunction'] = True
                            seenIn = seenIn or tUpperStr == 'IN'
                            seenIs = seenIs or tUpperStr == 'IS'
                            seenLike = seenLike or tUpperStr == 'LIKE'
                            seenBetween = seenBetween or tUpperStr == 'BETWEEN'
                            if tUpperStr in ['NULL', 'NOT NULL']:
                                if not seenIs:
                                    raise Exception('NULL without first seeing IS')
                                self._insertWhereTblAndCol(filterMap, tbl, col, None,
                                        None, ValueType.unknown)
                                seenValue = True
                    elif stringStart != None and not expectingIdentifier:
                        if tUpperStr not in ['NOT', 'LIKE', 'BETWEEN']:
                            raise Exception('Unexpected keyword following string')
                        else:
                            seenLike = seenLike or tUpperStr == 'LIKE'
                            seenBetween = seenBetween or tUpperStr == 'BETWEEN'
                    else:
                        if expectingIdentifier and str(t) != tUpperStr:
                            tbl = pt
                            col = str(t)
                            foundIdentifier = True
                            expectingIdentifier = False
                            if stringStart != None and curComparison != None:
                                self._insertWhereTblAndCol(filterMap, tbl, col, None,
                                        None, ValueType.unknown)
                        else:
                            helperObj['skipToNextConjunction'] = True
                            #raise Exception('Unexpected keyword')
                elif t.ttype == sqlparse.tokens.Operator.Comparison:
                    if not foundIdentifier:
                        if not (seenFunction or stringStart != None or numStart != None):
                            raise Exception('Comparison without identifier')
                        elif seenFunction:
                            # Hacky way to handle unknown functions of unknown cols:
                            # Just don't include them but dont' throw an error
                            helperObj['skipToNextConjunction'] = True
                        elif stringStart != None or numStart != None:
                            expectingIdentifier = True
                    curComparison = tUpperStr
                    if curComparison not in ['=', '<', '<=', '>', '>=', '!=', '<>']:
                        raise Exception('Unknown comparison')
                    helperObj['waitingForConjunction'] = True
                elif t.ttype == sqlparse.tokens.Name.Builtin:
                    # Manual inspection indicates that this is safe to just skip over
                    if tUpperStr == 'BINARY':
                        continue
                    else:
                        raise Exception('Unknown token of Builtin ttype')
                elif t.ttype == sqlparse.tokens.Literal.String.Single:
                    seenValue = True
                    if foundIdentifier and curComparison != None:
                        self._insertWhereTblAndCol(filterMap, tbl, col, str(t),
                                curComparison, ValueType.string)
                    elif (foundIdentifier and seenLike) or (seenBetween and seenAnd):
                        self._insertWhereTblAndCol(filterMap, tbl, col, str(t),
                                None, ValueType.string)
                    else:
                        stringStart = str(t)
                        expectingIdentifier = False
                elif t.ttype == sqlparse.tokens.Literal.Number.Integer:
                    seenValue = True
                    if foundIdentifier and curComparison != None:
                        self._insertWhereTblAndCol(filterMap, tbl, col, str(t),
                                curComparison, ValueType.integer)
                    elif expectingIdentifier:
                        numStart = int(tUpperStr)
                        expectingIdentifier = False
                    else:
                        raise Exception('Unexpected integer literal placement')
                elif t.ttype == sqlparse.tokens.Literal.Number.Float:
                    seenValue = True
                    if foundIdentifier and curComparison != None:
                        self._insertWhereTblAndCol(filterMap, tbl, col, str(t),
                                curComparison, ValueType.floating)
                    else:
                        raise Exception('Unexpected float literal placement')
                elif t.ttype == sqlparse.tokens.Keyword.DML:
                    # Don't handle nested queries
                    helperObj['skipToNextConjunction'] = True
                    return
                else:
                    raise Exception('Unexpected ttype')
            else:
                raise Exception('Unexpected class')

    def _insertWhereTblAndCol(self, filterMap, tbl, col, val, curComparison, valType):
        colMap = filterMap.get(tbl, {})
        # All table names are lower case in schema description
        tbl = tbl.lower()
        if curComparison == '=' and val != None:
            vals = colMap.get(col, [])
            if valType == ValueType.string:
                if (not ((val[0] == "'" and val[-1] == "'")
                    or (val[0] == '"' and val[-1] == '"'))):
                    raise Exception('String does not have expected format')
                val =  val[1:-1]
                if self.dbSchema.colTypes[(tbl, col)] == DbColType.intlike:
                    val = int(val)
                if self.dbSchema.colTypes[(tbl, col)] == DbColType.floatlike:
                    val = float(val)
            elif valType == ValueType.integer:
                val = int(val)
            elif valType == ValueType.floating:
                val = float(val)
            else:
                raise Exception('Should never be reached')
            vals.append(val)
            colMap[col] = vals
        else:
            colMap[col] = []
        filterMap[tbl] = colMap

    # Should also set primaryTable
    def getTables(self):
        if self.tables is not None:
            return self.tables
        tables = None
        if self.queryType == QueryType.select:
            aliases = self.getAliases()
            tables = aliases.values()
        elif self.queryType == QueryType.update:
            tables = self._getTablesUpdate()
        elif self.queryType == QueryType.insert:
            tables = self._getTablesInsert()
        elif self.queryType == QueryType.delete:
            tables = self._getTablesDelete()
        else:
            tables = []
        newTables = []
        for t in tables:
            newTables.append(t.lower())
        self.tables = newTables
        return self.tables

    def _getTablesUpdate(self):
        # tokens will have 'UPDATE', whitespace, table name
        # The second tokens extracts just the name in case of aliasing
        self.primaryTable = self.parsed.tokens[2].tokens[0].value
        return [self.primaryTable]

    def _getTablesInsert(self):
        # tokens will have 'INSERT', whitespace, 'INTO', whitespace, table name
        # or just 'INSERT', whitespace, table name
        # The second tokens extracts just the name in case of aliasing

        for t in self.parsed.tokens:
            if (t.__class__ == sqlparse.sql.Identifier):
                self.primaryTable = t.tokens[0].value
                break
            if (t.__class__ == sqlparse.sql.Function):
                self.primaryTable = t.tokens[0].tokens[0].value
                break
        return [self.primaryTable]

    def _getTablesDelete(self):
        # tokens will have 'DELETE', whitespace, 'FROM', whitespace, table name
        # The second tokens extracts just the name in case of aliasing
        self.primaryTable = self.parsed.tokens[4].tokens[0].value
        return [self.primaryTable]

    def __str__(self):
        return self._printHelper()

    def __repr__(self):
        return self._printHelper()

    def _printHelper(self):
        return '\n'.join([str(self.uniqueId), self.origCommArg])

# Reads the db schema info csv (format is table_name,col_name,col_key)
def readDbSchemaFile(fName):
    dbSchema = DbSchema()
    with open(fName, 'r') as f:
        for line in f:
            # Remove newline at end of string
            line = line[:-1]
            csplit = line.split(',')
            dbSchema.add(csplit[0], csplit[1], csplit[2], csplit[3], csplit[4])
    return dbSchema

# Reads the raw logs and ensures that every line is a single
# log line (no comments, combines lines if formatted strangely)
def readRawLogs(fName):
    logs = []
    with open(fName, 'r') as f:
        currentLine = ''
        for line in f:
            # Skip comments
            if (line[0] == '#'):
                continue
            # Remove newline at end of string
            line = line[:-1]
            continuation = False
            # Check if the line is part of the previous log or a new log
            for i in xrange(len(line)):
                c = line[i]
                if (c == ' ' or c == '\t'):
                    continue
                try:
                    int(c)
                    logs.append(currentLine)
                    currentLine = line
                except ValueError:
                    currentLine += ' ' + line[i:]
                break
        logs.append(currentLine)
    # The first time currentLine is appended, it will be empty; remove that log
    logs = logs[1:]
    return logs

# Read the logs in list and build a list of LogObjects to return
def parseLogsIntoObject(logs, dbSchema):
    logObjs = []
    timestamp = None
    count = 0
    for logLine in logs:
        tabsplit = logLine.split('\t')
        count += 1
        if (tabsplit[0] == '' and tabsplit[1] == ''):
            # This happened at the same time as the previous timestamp
            threadAndCommand =  tabsplit[2]
            commArg = ' '.join(tabsplit[3:])
        elif (tabsplit[0][0] == '1'):
            # There is a new timestamp
            timestamp = time.mktime(
                    datetime.datetime.strptime(tabsplit[0], "%y%m%d %H:%M:%S").timetuple())
            threadAndCommand =  tabsplit[1]
            commArg = ' '.join(tabsplit[2:])
        else:
            # These should be the only two cases, something strange is going on
            print('\n'.join(tabsplit))
            raise Exception
        threadAndCommSplit = threadAndCommand.split(' ')
        logObjs.append(LogObject(timestamp, threadAndCommSplit[-2], threadAndCommSplit[-1], commArg, dbSchema, count))
    return logObjs

def insertWSTest(logObjs):
    for l in logObjs:
        if l.queryType == QueryType.insert:
            print(l.origCommArg)
            print(l.getWriteSet())
            print('')

def updateWSTest(logObjs):
    for l in logObjs:
        if l.queryType == QueryType.update:
            print(l.origCommArg)
            print(l.getWriteSet())
            print('')

def deleteWSTest(logObjs):
    for l in logObjs:
        if l.queryType == QueryType.delete:
            print(l.origCommArg)
            print(l.getWriteSet())
            print('')

def selectRSTest(logObjs):
    for l in logObjs:
        if l.queryType == QueryType.select:
            print(l.origCommArg)
            print(l.getReadSet())
            print('')

def whereTest(logObjs):
    for l in logObjs:
        if (l.queryType == QueryType.select or
            l.queryType == QueryType.delete or
            l.queryType == QueryType.update):
            print(l.origCommArg)
            print(l.getWhereFilter())
            print('')

# We are only interested in reads, writes, and transaction statements
def filterUninterestingLogs(stmts):
    filteredStmts = []
    for stmt in stmts:
        if (stmt.queryType == QueryType.other or
            stmt.queryType == QueryType.notQuery):
            continue
        if (stmt.queryType == QueryType.select and
            stmt.getPrimaryTable() == ''):
            # Simple form of keep alive statements
            continue
        filteredStmts.append(stmt)
    return filteredStmts

# Many frameworks end up inserting a log of empty transactions.
def filterEmptyTxns(stmts):
    filteredStmts = []
    tempList = []
    for stmt in stmts:
        if (stmt.queryType == QueryType.startTxn or
            stmt.queryType == QueryType.startTxnCond):
            tempList.append(stmt)
        elif (stmt.queryType == QueryType.endTxn or
              stmt.queryType == QueryType.endTxnCond):
            if len(tempList) > 0:
                tempList.pop()
            else:
               filteredStmts.append(stmt)
        else:
            filteredStmts = filteredStmts + tempList
            filteredStmts.append(stmt)
            tempList = []
    return filteredStmts

# returns true if the read set and write set could possibly overlap
def overlapWritesetWriteset(log1, log2):
    # Assume that an insertion or deletion will affect the readset
    if (log1.queryType == QueryType.insert or
        log1.queryType == QueryType.delete or
        log2.queryType == QueryType.insert or
        log2.queryType == QueryType.delete):
        return True
    elif (log1.queryType == QueryType.update and
            log1.queryType == QueryType.update):
        ws1 = log1.getWriteSet()
        ws2 = log2.getWriteSet()
        for col in ws1:
            if col in ws2:
                return True
        return False
    else:
        raise Exception("writeLog is not a write")

# returns true if the read set and write set could possibly overlap
def overlapReadsetWriteset(readLog, writeLog):
    # Assume that an insertion or deletion will affect the readset
    if (writeLog.queryType == QueryType.insert or
        writeLog.queryType == QueryType.delete):
        return True
    elif writeLog.queryType == QueryType.update:
        readSet = readLog.getReadSet()[writeLog.getPrimaryTable()]
        writeSet = writeLog.getWriteSet()
        if ReadType.star in readSet.reads:
            return True
        elif ReadType.cols in readSet.reads:
            for col in readSet.colsRead:
                if col in writeSet:
                    return True
            return False
        else:
            # The update may affect a SUM function, but doesn't affect a count
            # right now we don't check for the difference
            return True
    else:
        raise Exception("writeLog is not a write")

# Whether the new values could affect the results of a WHERE clause
def overlapWriteSetAndPredicate(writeLog, predicateLog):
    whereFilter = predicateLog.getWhereFilter()[writeLog.getPrimaryTable()]
    writeSet = writeLog.getWriteSet()
    if writeLog.queryType == QueryType.update:
        # For update, if any column of the where clause is updated
        # then this could cause a change in results, since we don't
        # know the value before
        if len(whereFilter) == 0:
            # no where clause on this table
            return True
        else:
            for col in whereFilter.keys():
                if col in writeSet:
                    return True
            return False
    elif writeLog.queryType == QueryType.delete:
        # delete only changes predicate results if the delete predicate matches
        # which is checked by a different function
        return False
    elif  writeLog.queryType == QueryType.insert:
        # insert we want to check if the actual values match
        if len(whereFilter) == 0:
            # no where clause on this table
            return True
        else:
            for (col, vals) in whereFilter.items():
                # We don't have all the information necessary so assume overlap
                if (len(vals) == 0 or writeSet[col] == None):
                    return True
                else:
                    for val in vals:
                        if writeSet[col] == val:
                            return True
            return False
    else:
        raise Exception("writeLog is not a write")

# Whether two where filters overlap on a given table
def overlapPredicates(log1, log2, targetTbl):
    wfFull1 = log1.getWhereFilter()
    wfFull2 = log2.getWhereFilter()
    if targetTbl not in wfFull1 or targetTbl not in wfFull2:
        raise Exception('Should always find the table')
    wf1 = wfFull1[targetTbl]
    wf2 = wfFull2[targetTbl]
    if (len(wf1) == 0 or len(wf2) == 0):
        # There could be overlap if either is entirely missing a where filter
        # or we could not parse the filter
        return True
    noOverlap = True
    for (col, vals1) in wf1.items():
        if col in wf2:
            noOverlap = False
            vals2 = wf2[col]
            if (len(vals1) == 0 or len(vals2) == 0):
                # There could be overlap if in either case we don't know the possible values
                return True
            for val in vals1:
                if val in vals2:
                    return True
    # If there is no overlap then they could just refer to the same row in different ways
    return noOverlap

# Groups the log objects by their api call
def groupByApiCall(logObjs):
    groups = []
    group = [logObjs[0]]
    prevTimestamp = logObjs[0].timestamp
    for logObj in logObjs[1:]:
        if prevTimestamp < logObj.timestamp - 17:
            groups.append(group)
            group = [logObj]
            prevTimestamp = logObj.timestamp
        else:
            group.append(logObj)
    groups.append(group)
    return groups

# Calculates the type of edge that should be added between log1 and log2
def calcEdge(log1, log2):
    if (log1.isRead() and log2.isRead()):
        return None
    elif (log1.isRead() or log2.isRead()):
        readLog = log1
        writeLog = log2
        if log2.isRead():
            readLog = log2
            writeLog = log1
        writeTbls = writeLog.getTables()
        # Each write should only be to one table
        assert(len(writeTbls) == 1)
        tbl = writeTbls[0]
        readTbls = readLog.getTables()
        if tbl not in readTbls:
            return None
        if writeLog.queryType == QueryType.update:
            if ((overlapReadsetWriteset(readLog, writeLog) and
                overlapPredicates(readLog, writeLog, tbl)) or
                overlapWriteSetAndPredicate(writeLog, readLog)):
                return EdgeType.RW
        elif writeLog.queryType == QueryType.insert:
            if (overlapWriteSetAndPredicate(writeLog, readLog)):
                return EdgeType.RW
        elif writeLog.queryType == QueryType.delete:
            if overlapPredicates(readLog, writeLog, tbl):
                return EdgeType.RW
    else:
        tbl = log1.getPrimaryTable()
        if tbl != log2.getPrimaryTable():
            return None
        if (log1.queryType == QueryType.update and log2.queryType == QueryType.update):
            if (overlapWriteSetAndPredicate(log1, log2) or
                overlapWriteSetAndPredicate(log2, log1) or
                (overlapWritesetWriteset(log1, log2) and
                overlapPredicates(log1, log2, tbl))):
                return EdgeType.WW
        elif (log1.queryType == QueryType.update and log2.queryType == QueryType.insert):
            # Since we assume that inserts affect all predicates, return True here.
            # Should really filter out if write is on primary key/use value of insert
            return EdgeType.WW
        elif (log1.queryType == QueryType.update and log2.queryType == QueryType.delete):
            if (overlapPredicates(log1, log2, tbl) or
                overlapWriteSetAndPredicate(log1, log2)):
                return EdgeType.WW
        elif (log1.queryType == QueryType.insert and log2.queryType == QueryType.update):
            # Since we assume that inserts affect all predicates, return True here.
            # Should really filter out if write is on primary key/use value of insert
            return EdgeType.WW
        elif (log1.queryType == QueryType.insert and log2.queryType == QueryType.insert):
            return EdgeType.WW
        elif (log1.queryType == QueryType.insert and log2.queryType == QueryType.delete):
            if (overlapWriteSetAndPredicate(log1, log2)):
                return EdgeType.WW
        elif (log1.queryType == QueryType.delete and log2.queryType == QueryType.update):
            if (overlapPredicates(log1, log2, tbl) or
                overlapWriteSetAndPredicate(log2, log1)):
                return EdgeType.WW
        elif (log1.queryType == QueryType.delete and log2.queryType == QueryType.insert):
            if (overlapWriteSetAndPredicate(log2, log1)):
                return EdgeType.WW
        else:
            assert(log1.queryType == QueryType.delete and log2.queryType == QueryType.delete)
        return None

# Builds an AH graph from the log objects
def buildGraph(logObjs):
    apiGroups = groupByApiCall(logObjs)
    ahGraph = AbstractHistory()
    for group in apiGroups:
        curApi = ahGraph.addApiNode()
        curTxn = None
        curForUpdates = []
        activeTxns = 0
        for stmt in group:
            if stmt.queryType == QueryType.startTxn:
                activeTxns += 1
                if not curTxn:
                    curTxn = ahGraph.addTxnNode(curApi)
                    curForUpdates = []
            elif stmt.queryType == QueryType.startTxnCond:
                if activeTxns == 0:
                    activeTxns += 1
                    curTxn = ahGraph.addTxnNode(curApi)
                    curForUpdates = []
            elif stmt.queryType == QueryType.endTxn:
                # Appears that some frameworks just randomly commit...
                if activeTxns >= 0:
                    activeTxns -= 1
                if activeTxns == 0:
                    curTxn = None
            elif stmt.queryType == QueryType.endTxnCond:
                assert(activeTxns <= 1)
                if activeTxns > 0:
                    activeTxns -= 1
                    curTxn = None
            else:
                if curTxn:
                    if stmt.isSelectForUpdate():
                        curForUpdates.append(stmt)
                    ahGraph.addOpNode(stmt, curTxn, curApi, curForUpdates)
                else:
                    ahGraph.addOpNode(stmt, ahGraph.addTxnNode(curApi), curApi, [])
    for i in xrange(1, len(ahGraph.ops)):
        op1 = ahGraph.ops[i]
        log1 = op1.logObj
        if ((log1.queryType == QueryType.insert) or
                (log1.queryType == QueryType.update)):
            ahGraph.addSelfLoop(op1)
        for j in xrange(i+1, len(ahGraph.ops)):
            op2 = ahGraph.ops[j]
            log2 = op2.logObj
            if (forUpdatesPrevents(log2, op1.forUpdates)):
                continue
            if (forUpdatesPrevents(log1, op2.forUpdates)):
                continue
            edgeType = calcEdge(log1, log2)
            if edgeType:
                ahGraph.addEdge(op1, op2, edgeType)
    return ahGraph

def forUpdatesPrevents(log, forUpdatesList):
    logTbls = log.getTables()
    for stmt in forUpdatesList:
        stmtTbls = stmt.getTables()
        for tbl in stmtTbls:
            if tbl in logTbls:
                return True
    return False

def printAHGraph(ahGraph, printRead, printWrite, printEdges, printStats):
    reads = []
    writes = []
    edges = []
    nonTrivialTxns = []
    for i in xrange(1, len(ahGraph.ops)):
        op = ahGraph.ops[i]
        log = op.logObj
        if log.isRead():
            reads.append(log)
        elif log.isWrite():
            writes.append(log)
        for edge in op.edges:
            if edge.op2.nodeId >= op.nodeId:
                edges.append((log, edge.op2.logObj))
    for txn in ahGraph.txns:
        numOps = len(txn.ops)
        assert(numOps > 0)
        if numOps > 1:
            nonTrivialTxns.append(txn)
    if printRead:
        print("PRINTING READS")
        for k in reads:
            print(k)
            print('')
    if printWrite:
        print("PRINTING WRITES")
        for k in writes:
            print(k)
            print('')
    if printEdges:
        print("PRINTING EDGES")
        for (l1, l2) in edges:
            print('(' + str(l1.uniqueId) + ', ' + str(l2.uniqueId) + ')')
    if printStats:
        print("PRINTING GRAPH STATS")
        print("Op Nodes: " + str(len(ahGraph.ops)))
        print("Txn Nodes: " + str(len(ahGraph.txns)))
        print("Nontrivial Txn Nodes: " + str(len(nonTrivialTxns)))
        print("API Nodes: " + str(len(ahGraph.apis)))
        print("Edges 1: " + str(len(edges)))
        print("Edges 2: " + str(ahGraph.totalEdges))

def printAnomalyTrace(anomalyTrace):
    print('!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!')
    print(op1.logObj)
    print('')
    print(op2.logObj)
    print('****************************')
    print('')
    for edge in potential_anomaly:
        print(edge.op1.api.nodeId)
        print(edge.op1.logObj)
        print(edge.op2.api.nodeId)
        print(edge.op2.logObj)
        print('')
    print('!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!')
    print('')
    print('')
    print('')

# -----------------------------------------------------------------
# | Utitliy Functions                                             |
# -----------------------------------------------------------------

def splitUncaptured(s, capBegin, capEnd):
    numCaps = 0
    commaIndices = []
    splitList = []
    # Find all commas not captured
    for idx in xrange(0, len(s)):
        c = s[idx]
        if c == capBegin:
            numCaps += 1
        if c == capEnd:
            numCaps -= 1
        if c == "," and numCaps == 0:
            commaIndices.append(idx)
    start = 0
    for idx in commaIndices:
        splitList.append(s[start:idx])
        start = idx + 1
    splitList.append(s[start:])
    return splitList

def splitUnquoted(s, splitChar):
    inQuotes = False
    splitIndices = []
    splitList = []
    # Find all splitChar not in quotes
    for idx in xrange(0, len(s)):
        c = s[idx]
        if c == "'":
            inQuotes = not inQuotes
        if c == splitChar and not inQuotes:
            splitIndices.append(idx)
    start = 0
    for idx in splitIndices:
        splitList.append(s[start:idx])
        start = idx + 1
    splitList.append(s[start:])
    return splitList

def findFirstNonEmpty(lst, empty, fromRight):
    start = 0
    end = len(lst)
    step = 1
    if fromRight:
        start = len(lst) - 1
        end = -1
        step = -1
    for i in xrange(start, end, step):
        if (lst[i] != empty):
            return lst[i]
    raise Exception('Nothing non-empty in the list')

# Spring seems to assume windows = not case sensitive
def lowerCaseKeys(mapping):
    newMapping = {}
    for (key, val) in mapping.items():
        newMapping[key.lower()] = val
    return newMapping

# -----------------------------------------------------------------
# | Beginning of top level of script                              |
# -----------------------------------------------------------------

parser = argparse.ArgumentParser()
parser.add_argument("file_name", help="Name of the file to read")
parser.add_argument("db_schema_file", help="Name of the csv file containing the db_schema in the form table_name, col_name, col_key")
parser.add_argument('--tbl', dest='tbl', default=None,
        help="The table over which to look for anomalies")
parser.add_argument('--col', dest='col', default=None,
        help="The column over which to look for anomalies")
parser.add_argument('--dbname', dest='dbname', default=None,
        help="The db name to remove from the logs because it makes them easier to parse")
args = parser.parse_args()

print("Reading from file " + args.file_name)

dbSchema = readDbSchemaFile(args.db_schema_file)

before_read_time = time.time()
logs = readRawLogs(args.file_name)
post_read_time = time.time()
# Filter out db name
if args.dbname:
    upperName = args.dbname.upper() + '.'
    lowerName = args.dbname.lower() + '.'
    for i in xrange(0, len(logs)):
        logs[i] = logs[i].replace(upperName, '')
        logs[i] = logs[i].replace(lowerName, '')
logObjs = parseLogsIntoObject(logs, dbSchema)

# Many empty transactions from frameworks can be removed, along with log
# messages that we are not worried about.
logObjs = filterUninterestingLogs(logObjs)
logObjs = filterEmptyTxns(logObjs)
graph = buildGraph(logObjs)
post_graph_time = time.time()

print("PRINTING LOG STATS")
print('Num Logs: ' + str(len(logs)))
print('')
printAHGraph(graph, False, False, False, True)

if args.tbl is None:
    for api in graph.apis:
        print(' -------------------------------------------------------')
        print(' API Call: ' + str(api.nodeId))
        print(' -------------------------------------------------------')
        foundTbls = {}
        anomalousTables = []
        for i in xrange(1, len(api.ops)):
            for j in xrange(i+1, len(api.ops)):
                op1 = api.ops[i]
                op2 = api.ops[j]
                tbls1 = op1.logObj.getTables()
                tbls2 = op2.logObj.getTables()
                tablesOverlap = []
                for tbl in tbls1:
                    if tbl in tbls2:
                        tablesOverlap.append(tbl)
                newTables = []
                for tbl in tablesOverlap:
                    if tbl not in foundTbls:
                        foundTbls[tbl] = True
                        newTables.append(tbl)
                if len(newTables) == 0:
                    continue
                potential_anomaly = graph.find_potential_anomalies(op1, op2)
                if potential_anomaly is not None:
                    anomalousTables = anomalousTables + newTables
        for tbl in anomalousTables:
            print(tbl)
        print('')
else:
    for api in graph.apis:
        print(' -------------------------------------------------------')
        print(' API Call: ' + str(api.nodeId))
        print(' -------------------------------------------------------')
        for i in xrange(1, len(api.ops)):
            for j in xrange(i+1, len(api.ops)):
                op1 = api.ops[i]
                op2 = api.ops[j]
                tbls1 = op1.logObj.getTables()
                tbls2 = op2.logObj.getTables()
                if not (args.tbl in tbls1 and args.tbl in tbls2):
                    continue
                potential_anomaly = graph.find_potential_anomalies(op1, op2)
                if potential_anomaly is not None:
                    printAnomalyTrace(potential_anomaly)

post_analysis_time = time.time()

print('')
print('')
print('!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!')
print('Total Time: ' + str(post_analysis_time - before_read_time))
print('Read Data: ' + str(post_read_time - before_read_time))
print('Parse and build graph: ' + str(post_graph_time - post_read_time))
print('Analyze Time: ' + str(post_analysis_time - post_graph_time))
