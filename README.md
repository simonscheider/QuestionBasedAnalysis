# QuestionBasedAnalysis

SPARQL query matching

This module allows matching SPARQL constraint queries, based on determining wether a given query is a subquery of another.
The purpose is describing GIS tools and querying for them based on the question they answer.

SPARQL constraint queries consist of a basic
graph pattern with (potentially many) FILTER NOT EXISTS statements
that can also be nested (one level).

SPARQL Constraint is equivalent to a constrained graph pattern (CGP), consisting of:
- BGP = A Basic graph pattern
- NS = A negation set , i.e., a set of n negated graph patterns  {not BGP1, not BGP2, ...., not BGPn}, where n can be 0
- NS = A rule set , i.e. a set of m rules {BGP1b -> BGP1h, BGP2b -> BGP2h, ...., BGPmb -> BGPmh} , where m can be 0

The code is written in Python 2.7 and depends on:

* RDFLib (# pip install rdflib)
