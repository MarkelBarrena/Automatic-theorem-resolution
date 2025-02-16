/************************
INSTANCE TYPE DECLARATION
************************/

datatype Graph = G(V: nat, E: set<(nat, nat)>)
// Note: The nodes of the graph are natural numbers from 1 to |V|
// The edges (u, v) in E always satisfy that u < v

/*************************
TYPE DEFINITION PREDICATES
*************************/

// This predicate guarantees that the nodes of the edges are nodes of the graph
ghost predicate valid_graph(g: Graph)
{
    forall u, v :: (u, v) in g.E ==> 0 < u < v <= g.V
}

/******************
PROBLEM DEFINITIONS
*******************/

//// CLIQUE ////
ghost predicate clique(g: Graph, k: nat)
    requires valid_graph(g)
{
    exists cl: set<nat> :: |cl| == k && 
    (
        forall u, v :: 0 < u < v <= g.V ==> u in cl && v in cl ==> (u, v) in g.E 
    )
}


//// INDEPENDENT-SET ////
ghost predicate independentSet(g: Graph, k: nat)
    requires valid_graph(g)
{
    exists ins: set<nat> :: |ins| == k && 
    (
        forall u, v :: 0 < u < v <= g.V ==> u in ins && v in ins ==> (u, v) !in g.E 
    )
}


/***************
REDUCTION: CLIQUE <=p INDEPENDENT-SET
****************/


//// REDUCTION FUNCTION ////

// This function calculates the complementary set of edges
function complementary_edges(g: Graph): set<(nat, nat)>
    requires valid_graph(g)
    ensures forall u, v:: (u, v) in complementary_edges(g) ==> 0 < u < v <= g.V
    ensures forall u, v :: 0 < u < v <= g.V ==> 
        (
            (u, v) in g.E <==> (u, v) !in complementary_edges(g)
        )
{
   
    set u, v | 0 < u < v <= g.V && (u,v) !in g.E :: (u, v)    
} 


// The reduction function only transforms the initial graph G(V,E) into G(V,E')
// where E' is the complementary set of E  
function inverse_graph(g: Graph): Graph
    requires valid_graph(g)
    ensures valid_graph(inverse_graph(g))
    ensures g.V == inverse_graph(g).V
    ensures forall u, v :: 0 < u < v <= g.V ==> 
        (
            (u, v) in g.E <==> (u, v) !in inverse_graph(g).E
        )
{
    if g.V == 0 then g else G(g.V, complementary_edges(g))
}


//// REDUCTION CORRECTNESS ////

lemma reduction_lemma(g: Graph, k: nat)
    requires valid_graph(g)
    ensures clique(g, k) <==> independentSet(inverse_graph(g), k)
{
    if clique(g, k)
    {
        forward_lemma(g, k);
    }
    if independentSet(inverse_graph(g), k)
    {
        backward_lemma(g, k);
    }
}

lemma forward_lemma(g: Graph, k: nat)
    requires valid_graph(g)
    requires clique(g, k)
    ensures independentSet(inverse_graph(g), k)
{}

lemma backward_lemma(g: Graph, k: nat)
    requires valid_graph(g)
    requires independentSet(inverse_graph(g), k)
    ensures clique(g, k)
{}

