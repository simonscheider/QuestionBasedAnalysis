#-------------------------------------------------------------------------------
# Name:        Question based Analysis
# Purpose:      This module allows querying and matching
#               SPARQL constraint queries. These are queries consisting of a basic
#               graph pattern with (potentially) FILTER NOT EXISTS statements
#               that can be nested (one level). The purpose is desrcibing GIS tools
#               and querying for them based on the question they answer.
#
# Author:
#
# Created:     04/08/2017
# Copyright:   (c) simon 2017
# Licence:     <your licence>
#-------------------------------------------------------------------------------


__author__      = "Andrea Ballatore; Simon Scheider"
__copyright__   = ""

import rdflib
import rdflib.plugins.sparql as sparql
import glob

def file_to_str(fn):
    """
    Loads the content of a text file into a string
    @return a string
    """
    with open(fn, 'r') as f:
        content=f.read()
    return content

def loadData(g, file ):
    wf = rdflib.Graph()
    gd = wf.parse(file, format='n3') +g
    print "data loaded"
    return gd

def loadQueries(filepattern):
    queries = []
    querystr = glob.glob(filepattern)
    #file = 'questions/maupquery.rq'
    for qi in querystr:
        #print file_to_str(qi)
        q = file_to_str(qi)#file_to_str('rdf_prefixes.txt') +'\n'+
        queries.append(q)
    return queries

class Stack:
     def __init__(self):
         self.items = []

     def isEmpty(self):
         return self.items == []

     def push(self, item):
         self.items.append(item)

     def pop(self):
         return self.items.pop()

     def peek(self):
         return self.items[len(self.items)-1]

     def size(self):
         return len(self.items)

"""This class represents query patterns in a recursive way. That is, subpatterns are stored inside outer patterns.
The method constraintsPatterns() needs to be called after adding all subpatterns and turns the pattern into an explicit SPARQL constraint representation with BGP, NGP and RP."""

class Outpattern():
    goals = []
    variables = set()
    triples=[]
    rules = Stack()
    minus=[]
    completion=[]

    def __init__(self, goals=[], triples=[], rules=Stack(), minus = [], completion = [], variables = []):
        self.goals=goals
        self.triples=triples
        self.rules=rules
        self.minus = minus
        self.completion = completion
        self.variables = variables


    def add(self, state, array=[]):
        if state == 'triples':
            self.triples.extend(array)
        elif state == 'minus':
            o = Outpattern(triples=array, goals=[], rules=Stack(), minus = [], completion = [], variables = set())
            self.rules.push(o)
            #print "write rule body: "+ str(array)
        elif state == 'completion':
            r = Outpattern(triples=array, goals=[], rules=Stack(), minus = [], completion = [], variables = set())
            o = self.rules.pop()
            o.rules.push(r)
            self.rules.push(o)
            #print "write rule head: "+ str(array)
            #print "rule: "+ str(o.triples) + '->'+ str(o.rules.items[0].triples)


    #This generates the constaint patterns (arrays of negations (=minus) and rules (=completion) from the nested graph patterns and fishes out variables of the entire pattern
    def constraintPatterns(self):
        self.minus = []
        self.completion = []
        self.variables = set()

        self.setVariables(self.triples)
        for p in self.rules.items:
            if p.rules.isEmpty():
                self.minus.append(p.triples)
                self.setVariables(p.triples)
            else:
                rule = [p.triples,p.rules.items[0].triples]
                self.setVariables(p.triples)
                self.setVariables(p.rules.items[0].triples)
                self.completion.append(rule)

    def setVariables(self,triples):
        for triple in triples:
            for j in (0,1,2):
                if type(triple[j]) is rdflib.term.Variable:
                    self.variables.add(triple[j])


    def __str__(self):
         #print out
         prtt = (
         '\n SPARQL Constraint Graph Pattern: \n'+
         ' Goals: '+str(self.goals)+'\n'+
         ' Variables: '+str(self.variables)+'\n'+
         ' BGP: \n'+ str(self.triples) +' \n'+
         ' NGPs: ')
         for i,m in enumerate(self.minus):
                prtt += "\n  NGP "+ str(i+1) +': ' +str(m)
         prtt +="\n"+"RPs: "
         for i,m in enumerate(self.completion):
                prtt += "\n  RP "+ str(i+1) +': ' +str(m[0]) +' -> '+str(m[1])
         return prtt



"""Methods to parse a SPARQL query into SPARQL constraint patterns"""

def parseQuery(query):
    #get the SPARQL algebra
    qu=sparql.prepareQuery(query)
    a = qu.algebra
    #print a
    goals=[]
    if 'PV' in a.keys():
        goals = a['PV']
        #print "goals: " +str(goals)
    #initialize output object
    output = Outpattern(goals=goals,  triples=[], rules=Stack(), minus = [], completion = [], variables = set())
    transformP(a.name, a, output, 'triples')
    output.constraintPatterns()
    return output

def transformP(pname, p, output, state):
    print 'parse: ' +pname
    if ((pname == 'part') or (pname=='graph') or (pname == 'GroupGraphPatternSub')):
        transformPart(p, output, state)
    elif pname =='Join':
        transformJoin(p, output, state)
    elif pname == 'TriplesBlock':
        transformTriplesBlock(p, output, state)
    elif pname == 'SelectQuery':
        if p.p:
            transformP(p.p.name,p.p, output, state)
    elif pname == 'Project':
        if p.p:
            transformP(p.p.name,p.p, output, state)
    elif pname == 'Filter':
        transformFilter(p, output, state)
    elif pname == 'BGP':
        transformBGP(p, output, state)
    else:
        print "This query contains the pattern "+pname+" which cannot be transformed!"

def transformTriplesBlock(pattern,output,state):
    triplesnew =[]
    variables = []
    for i in pattern.triples:
        tuple = (i[0],i[1],i[2])
        triplesnew.append(tuple)
    #print 'push basic pattern '+pattern.name+': '+str(triplesnew) +' state:'+state
    output.add(state,triplesnew)

def transformBGP(pattern, output, state):
    #print 'push basic pattern '+pattern.name+': '+str(pattern.triples)+' state:'+state
    output.add(state,pattern.triples)

def transformJoin(pattern, output, state):
    #print 'transform a joined pattern'
    transformP(pattern.p1.name,pattern.p1,output, state)
    transformP(pattern.p2.name,pattern.p2,output, state)

def transformPart(parts, output, state):
    #print "transform parts "#+str(parts)
    for partt in parts['part']:
        transformP(partt.name,partt,output, state)

def transformFilter(pattern, output, state):
    if pattern.p:
        transformP(pattern.p.name, pattern.p,output, state)
    filterexp = pattern.expr
    exname = filterexp.name
    #print 'parse expression: '+exname
    transformExp(exname, filterexp,output, state)

def transformExp(exname,ex, output, state):
    if exname=='Builtin_NOTEXISTS':
        #print "graph: "+ex['graph'].name
        #print "graph alt: "+ex.graph.name
        if state == 'triples':
            state = 'minus'
        elif state =='minus':
            state = 'completion'
        transformP(ex['graph'].name,ex['graph'],output,state)
        if ex.graph.expr:
            #print 'parse expression: '+ex.graph.expr.name
            transformExp(ex.graph.expr.name, ex.graph.expr,output, state)
    elif exname=='Builtin_EXISTS':
        #print "graph: "+ex['graph'].name
        #print "graph alt: "+ex.graph.name
        transformP(ex['graph'].name,ex['graph'],output,state)
        if ex.graph.expr:
            #print 'parse expression: '+ex.graph.expr.name
            transformExp(ex.graph.expr.name, ex.graph.expr,output, state)
    elif exname=='RelationalExpression':
        if ('!' in ex.op or 'not' in ex.expr):
            #ex.op[]
            #print "push relational pattern: " +str((ex.expr, ex.op, ex.other)) + 'state: ' +state
            output.add('minus',[(ex.expr, ex.op, ex.other)])

        print(str(ex.expr)+str(ex.op)+str(ex.other))
    elif exname == 'ConditionalAndExpression':
        #print 'parse expression: '+ex['expr'].name
        transformExp(ex['expr'].name, ex['expr'],output, state)
        for o in ex['other']:
            #print 'parse expression: '+o.name
            transformExp(o.name, o, output, state)
    else:
         print "This query contains expression "+exname+" which cannot be transformed!"



"""Methods for query containment matching"""

'''This method turns a basic graph pattern into a select query string that can be fired against RDF'''
def BGP2ASK(bgp):
    triples = ''
    for t in bgp:
        triples += t[0].n3()+' '+t[1].n3()+' '+t[2].n3()+' . \n'
    q = """\n SELECT * WHERE { \n""" +triples+  """ }"""
    return q
    #bool(results)

'''This method turns a basic graph pattern into RDF. Variables are turned into URIs.'''
def BGP2RDF(bgp):
    output = rdflib.Graph()
    for t in bgp:
        output.add((variable2term(t[0]), variable2term(t[1]),variable2term(t[2])))
    return output

'''This turns variables into blank nodes'''
def variable2term(term):
    if type(term) is rdflib.term.Variable:
        return rdflib.term.URIRef(term)
    else:
        return term

def n_triples( g, n=None ):
    """ Prints the number of triples in graph g """
    if n is None:
        print( '  Triples: '+str(len(g)) )
    else:
        print( '  Triples: +'+str(len(g)-n) )
    return len(g)

def printGraph(graph):
    for s, p, o in graph:
        print s, p,  o

def subBGP(bgp, bgpagainst):
    #mapping from bgpagainst into bgp
    rdf = BGP2RDF(bgp)
    ask = BGP2ASK(bgpagainst)
    result = rdf.query(ask)
    return result

def subNGP(ngp, ngpagainst):
    return subBGP(ngpagainst,ngp)

def subNGPs(ngps, ngpsagainst):
    for pa in ngpsagainst:
        res = False
        for p in ngps:
            if subNGP(p, pa):
                res = True
                break
        if res == False:
            return False
    return True

def subRP(rp, rpagainst):
    body2 = rpagainst[0]
    head2 = rpagainst[1]
    body1 = rp[0]
    head1 = rp[1]
    return subBGP(body2, body1) and subBGP(head1, head2)

def subRPs(rps, rpsagainst):
    for pa in rpsagainst:
        res = False
        for p in rps:
            if subRP(p, pa):
                res = True
                break
        if res == False:
            return False
    return True

#This method generates a mapping from variables into terms based on a query result of a query over all variables. Generates one dictionary per query result to look up mappings
def getVariableMap(querypattern, queryresult):
    varmaps = []
    for row in queryresult:
            varmap = {}
            print row
            for var in querypattern.variables:
                varmap[var] = row[var] #.n3().replace('?','')
            print varmap
            varmaps.append(varmap)
    return varmaps

def substituteVars(bgp,varmap):
     bgpout = []
     for t in bgp:
        tuple = ()
        for j in (0,1,2):
            tuple[j] =(varmap(t[j]) if (type(t[j]) is rdflib.term.Variable and t[j] in varmap.keys) else t[j])
        bgpout.append(tuple)
     return bgpout

def subCGP(cgp, cgpagainst):
    indeed = True
    bgpresult = subBGP(cgp.triples,cgpagainst.triples)
    varmap = None
    if bool(bgpresult):
        varmaps = getVariableMap(cgpagainst,bgpresult)
        varmap = varmaps[0]
    else:
        indeed = False
    if varmap != None:
        cgpagainstm =substituteVars(cgpagainst.minus, varmap)
        #cgpagainstc =substituteVars(cgpagainst.completion, varmap)
    else:
        cgpagainstm = cgpagainst.minus
        #cgpagainstc =cgpagainst.completion

    ngpresult = subNGPs(cgp.minus,cgpagainstm)
    rpresult = subRPs(cgp.completion,cgpagainst.completion)

    return indeed



def matchRequest2tool(requestpt, toolpt):
    return subCGP(toolpt,requestpt)


def searchForTool(request):
    tq = loadQueries('tools/tool*.rq')
    print ''
    print 'Search for corresponding tools \n'
    for i,tqs in enumerate(tq):
        print ''
        print 'Tool '+str(i+1)+':'
        #sparql.algebra.pprintAlgebra(q)
        tool = parseQuery(tqs)
        if matchRequest2tool(request, tool):
            print ''
            print 'Request matches to'
            print tool
            print tqs
            #print tool.query



def main():
    #g = rdflib.ConjunctiveGraph()
    rq = loadQueries('requests/request*.rq')
    for rqs in rq:
        print 'Request: '
        print rqs
        request = parseQuery(rqs)
        searchForTool(request)






if __name__ == '__main__':
    main()
