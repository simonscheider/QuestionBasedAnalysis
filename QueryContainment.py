
"""
Question based Analysis.

This module allows matching of SPARQL constraint queries, based on determining wether a given query is a subquery of another.
The purpose is desrcibing GIS tools and querying for them based on the question they answer.

SPARQL constraint queries consist of a basic
graph pattern with (potentially many) FILTER NOT EXISTS statements
that can also be nested (one level).

SPARQL Constraint is equivalent to a constrained graph pattern (CGP), consisting of:
- BGP = A Basic graph pattern
- NS = A negation set , i.e., a set of n negated graph patterns  {not BGP1, not BGP2, ...., not BGPn}
- NS = A rule set , i.e. a set of m rules {BGP1b -> BGP1h, BGP2b -> BGP2h, ...., BGPmb -> BGPmh}

The code is written in Python 2.7 and depends on:

* RDFLib (# pip install rdflib)

"""



__author__      = "Andrea Ballatore; Simon Scheider"
__copyright__   = ""

import rdflib
import rdflib.plugins.sparql as sparql
import glob
import RDFClosure
from rdflib.namespace import RDFS, RDF

"""Reasoning stuff"""
def run_inferences( g ):
    #print('run_inferences')
    # expand deductive closure
    RDFClosure.DeductiveClosure(RDFClosure.RDFS_Semantics).expand(g)
    #RDFClosure.DeductiveClosure(RDFClosure.OWLRL_Semantics).expand(g)
    n_triples(g)
    return g

def load_ontologies( g ):
    #print("load_ontologies")
    ontos = ["ontologies/GISConcepts.rdf","ontologies/Workflow.rdf","ontologies/AnalysisData.rdf"]#,"ontologies/Workflow.rdf","ontologies/AnalysisData.rdf"]
    for fn in ontos:
        #print("  Load RDF file: "+fn)
        g.parse( fn )
    #n_triples(g)
    return g


"""Helper stuff"""
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

def file_to_str(fn):
    """
    Loads the content of a text file into a string
    @return a string
    """
    with open(fn, 'r') as f:
        content=f.read()
    return content

def loadQueries(filepattern):
    queries = []
    querystr = glob.glob(filepattern)
    print "\n Queries loaded:"
    print querystr
    #file = 'questions/maupquery.rq'
    for qi in querystr:
        #print file_to_str(qi)
        q = file_to_str(qi)#file_to_str('rdf_prefixes.txt') +'\n'+
        queries.append([qi,q])
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
    goals = [] #These are the selected variables
    variables = set() #These are all variables appearing in the query
    construct = [] #The graph pattern in the construct clause
    triples=[] #This contains BGP triples (in the where clause) of the query
    rules = Stack() #Only needed to collect negations and rules
    minus=[] #This contains all NGP patterns (in FILTER NOT EXISTS clause) of the query
    completion=[] #This contains all RP patterns (rules) (in nested FILTER NOT EXISTS clause) of the query

    def __init__(self, goals=[], triples=[], rules=Stack(), minus = [], completion = [], variables = [], construct = []):
        self.goals=goals
        self.construct=construct
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
            if not self.rules.isEmpty():
                o = self.rules.pop()
            else:
                o = Outpattern(triples=[], goals=[], rules=Stack(), minus = [], completion = [], variables = set())
            o.rules.push(r)
            self.rules.push(o)
            #print "write rule head: "+ str(array)
            #print "rule: "+ str(o.triples) + '->'+ str(o.rules.items[0].triples)


    #This generates the constaint patterns (arrays of negations (=minus) and rules (=completion) from the nested graph patterns and fishes out variables of the entire pattern. Should be called after a query is parsed.
    def constraintPatterns(self):
        self.minus = []
        self.completion = []
        self.variables = set()

        self.setVariables(self.triples)
        if self.construct!= None:
            self.setVariables(self.construct)
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
         'SPARQL Constraint Graph Pattern: \n'+
         ' Goals: '+str(self.goals)+'\n'+
         ' Variables in query: '+str(self.variables)+'\n'+
         ' Construct clause: '+str(self.construct)+'\n'+
         ' BGP: \n'+ str(self.triples) +' \n'+
         ' NGPs: ')
         for i,m in enumerate(self.minus):
                prtt += "\n  NGP "+ str(i+1) +': ' +str(m)
         prtt +="\n"+" RPs: "
         for i,m in enumerate(self.completion):
                prtt += "\n  RP "+ str(i+1) +': ' +str(m[0]) +' -> '+str(m[1])
         return prtt



"""Methods to parse a SPARQL query into SPARQL constraint patterns"""

"""This method is the entry point for parsing. It takes a query string, turns it into SPARQL algebra and then generates a SPARQL constraint pattern"""
def parseQuery(query):
    print ''
    print 'Start parsing the query:'
    #print query
    #get the SPARQL algebra
    qu=sparql.prepareQuery(query)
    #print qu.prologue
    a = qu.algebra
    goals=[]
    if 'PV' in a.keys():
        goals = a['PV']
        print "goals: " +str(goals)
    #initialize output object
    #print a.template
    #Prepare output pattern object
    output = Outpattern(goals=goals,  triples=[], rules=Stack(), minus = [], completion = [], variables = set(), construct=(a.template if a.template !=None else []))
    #start filling the pattern recursively
    transformP(a.name, a, output, 'triples')
    #prepare pattern summaries
    output.constraintPatterns()
    #print output
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
    elif pname == 'ConstructQuery':
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

'''This method turns a basic graph pattern into RDF. Variables are turned into (fake) URIs to fix their meaning.'''
def BGP2RDF(bgp):
    output = rdflib.Graph()
    for t in bgp:
        output.add((variable2term(t[0]), variable2term(t[1]),variable2term(t[2])))
    output = load_ontologies(output)
    output = run_inferences(output)
    return output

'''This turns variables into URIs in order to keep their bindings fixed'''
def variable2term(term):
    if type(term) is rdflib.term.Variable:
        return rdflib.term.URIRef(term)
    else:
        return term


"""Main methods for query containment"""

'''This determines whether a basic graph pattern (BGP) is contained in another'''
def subBGP(bgp, bgpagainst):
    #mapping from bgpagainst into bgp
    if bgp ==[]: #The empty pattern is always a subpattern of any pattern
        return True
    rdf = BGP2RDF(bgp)
    ask = BGP2ASK(bgpagainst)
    result = rdf.query(ask)
    return result

'''This determines whether a negated graph pattern (NGP) is contained in another'''
def subNGP(ngp, ngpagainst):
    return subBGP(ngpagainst,ngp)

'''This determines whether a negation set (NS) is contained in another'''
def subNGPs(ngps, ngpsagainst):
    resultlist = []
    for pa in ngpsagainst:
        res = False
        for p in ngps:
            result = subNGP(p, pa)
            if bool(result):
                resultlist.append(result)
                res = True
                break
        if not res:
            return False
    return resultlist

'''This determines whether a rule pattern (RP) is contained in another'''
def subRP(rp, rpagainst):
    body2 = rpagainst[0]
    head2 = rpagainst[1]
    body1 = rp[0]
    head1 = rp[1]
##    print 'subrule: '
##    print str(body1) + ' -> '+str(head1)
##    print 'superrule: '
##    print str(body2) + ' -> '+str(head2)
    res = [subBGP(body2, body1),subBGP(head1, head2)]
    return res

'''This determines whether a rule set (RS) is contained in another'''
def subRPs(rps, rpsagainst):
    resultlist = []
    for pa in rpsagainst:
        res = False
        for p in rps:
            result = subRP(p, pa)
            if bool(result[0] and result[1]):
                resultlist.append(result)
                res = True
                break
        if not res:
            return False
    return resultlist

'''This determines whether a Constrained Graph Pattern (CGP) is contained in another'''
def subCGP(cgp, cgpagainst):
    varmaps = []

    #Check query containment for BGPs (plus construct clause if available)
    bgpresult = subBGP(cgp.triples+cgp.construct,cgpagainst.triples+cgpagainst.construct)
    if bool(bgpresult):
        print 'BGP Match!'
        varmaps = getVariableMap(cgpagainst,bgpresult)
    else:
        print 'BGP does not Match!'
        return False

    #Check query containment for NGPs
    #First substitute variables with terms obtained from the BGP query result to link pattern queries.
    cgpagainstm = cgpagainst.minus
    varmapk = []
    if varmaps != []:
        for varmap in varmaps:
                cgpagainstm = []
                for triples in cgpagainst.minus:
                    cgpagainstm.append(substituteVars(triples, varmap))
                ngpresults = subNGPs(cgp.minus,cgpagainstm)
                if ngpresults != False:
                    print 'NGPs Match! '
                    for ngpresult in ngpresults:
                        varmap.update(invertmap(getVariableMap(cgp,ngpresult)[0]))
                    varmapk.append(varmap)
                    break
                else:
                    print 'NGPs do not Match!'
                    return False
    else:
        ngpresults = subNGPs(cgp.minus,cgpagainstm)
    #If check is successful, then get potentially new variables and add them to the variable map
        if ngpresults != False:
            print 'NGPs Match!'
            for ngpresult in ngpresults:
                varmapk.append(invertmap(getVariableMap(cgp,ngpresult)[0]))
        else:
            print 'NGPs do not Match!'
            return False

    if varmapk == []: varmapk = varmaps

    #Check query containment for RPs
    #First substitute variables with terms obtained from the BGP and NGP query results to link pattern queries.
    cgpagainstc =cgpagainst.completion
    if varmapk != []:
        for varmap in varmapk:
                cgpagainstc = []
                for rule in cgpagainst.completion:
                    cgpagainstc.append([substituteVars(rule[0], varmap),substituteVars(rule[1], varmap)])
                rpresults = subRPs(cgp.completion,cgpagainstc)
                if rpresults != False: break
    else:
        rpresults = subRPs(cgp.completion,cgpagainstc)

    if rpresults == False:
        print 'RPs do not Match!'
        return False
    else:
        print 'RPs Match!'

    return True

def invertmap(map):
    return dict((v, k) for k, v in map.iteritems())

def matchRequest2tool(requestpt, toolpt):
    print ''
    print 'Start matching procedure'
    return subCGP(toolpt,requestpt)


#This method generates a mapping from variables into terms based on result variable bindings. Generates one dictionary per query result, in order to look up bindings
def getVariableMap(querypattern, queryresult):
    varmaps = []
    print 'Get variable bindings'
    print "Number of bindings:" +str(len(queryresult))
    for row in queryresult:
            varmap = {}
            #print querypattern.variables
            #print row
            for var in querypattern.variables:
                #store the variables together with their bindings in a dictionary
                if  hasattr(row,var):
                    varmap[var] = row[var]
            print varmap
            varmaps.append(varmap)
    return varmaps

#This method takes a bgp and substitutes terms for variables given a variable binding
def substituteVars(bgp,varmap):
     bgpout = []
     for t in bgp:
        tu = []
        for j in (0,1,2):
            tu.append((varmap[t[j]] if (type(t[j]) is rdflib.term.Variable and t[j] in varmap.keys()) else t[j]))
        bgpout.append(tuple(tu))
     return bgpout

'''This method takes a parsed request query and searches for matching tools in the tools folder'''
def searchForTool(request):
    tq = loadQueries('tools/def*.rq')
    #tq = loadQueries('tools/defArealInterpolation.rq')
    matches = []
    print ''
    print 'Search for corresponding tools'
    for tqs in tq:
        print ''
        print 'Tool '+str(tqs[0])+':'
        #sparql.algebra.pprintAlgebra(q)
        tool = parseQuery(tqs[1])
        if matchRequest2tool(request, tool):
            print ''
            print 'Request matches!'
            #print tool
            matches.append(tqs)
            print ''
            #print tool.query
    return matches


def main():
    #g = rdflib.ConjunctiveGraph()
    rq = loadQueries('requests/r*.rq')
    results= {}
    for rqs in rq:
        print 'SPARQL Request: '+rqs[0]
        request = parseQuery(rqs[1])
        matches = searchForTool(request)
        results[rqs[0]]=[rqs[1],matches]

    print '############################################################'
    print "Results: "
    for (k,v) in results.iteritems():
        print "\n Request : "+k
        #print v[0]
        print "\n matches to "+str(len(v[1]))+" tools: \n"
        for t in v[1]:
            print 'Tool '+(t[0]) +'\n'
            #print t[1]





if __name__ == '__main__':
    main()
