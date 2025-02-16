
module Definitions
{
    /************************
    INSTANCE TYPE DECLARATION
    ************************/

    type Graph = seq<seq<bool>>

    /*************************
    TYPE DEFINITION PREDICATES
    *************************/

    //squared and triangular superior matrix
    ghost predicate validUndirectedGraph(g: Graph)
    {
        (forall s :: s in g ==> |s|==|g|) &&
        (forall n :: 0<=n<|g| ==> (forall v :: 0<=v<=n  ==> !g[n][v])) //under diagonal -> false
    }

    //squared matrix
    ghost predicate validGraph(g: Graph)
    {
        forall s :: s in g ==> |s|==|g|
    }

    /******************
    PROBLEM DEFINITIONS
    *******************/

    /////// DIRECTED HAMILTONIAN CIRCUIT ///////

    //Definition predicates:

    ghost predicate directedHamiltonianCircuit(g: Graph)
        requires validGraph(g)
    {
        exists hc :: isDirectedHamiltonianCircuit(g, hc)
    }

    ghost predicate isDirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
        requires validGraph(g)
    {
        hamiltonianCircuitPartialCorrectness(g, circuit) && isDirectedHamiltonianCircuit3(g, circuit)
    }

    ghost predicate isDirectedHamiltonianCircuit3(g: Graph, circuit: seq<nat>)
        requires validGraph(g)
        requires hamiltonianCircuitPartialCorrectness(g, circuit)
    {
        |g|>0 &&
        (forall i :: 0<i<|g| ==> g[circuit[i-1]][circuit[i]]) && (g[circuit[|g|-1]][circuit[0]])
    }
    /////// UNDIRECTED HAMILTONIAN CIRCUIT ///////

    //Definition predicates:

    ghost predicate undirectedHamiltonianCircuit(g: Graph)
        requires validUndirectedGraph(g)
    {
        exists hc :: isUndirectedHamiltonianCircuit(g, hc)
    }

    ghost predicate isUndirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
        requires validUndirectedGraph(g)
    {
        hamiltonianCircuitPartialCorrectness(g, circuit) && isUndirectedHamiltonianCircuit3(g, circuit)
    }

    ghost predicate isUndirectedHamiltonianCircuit3(g: Graph, circuit: seq<nat>)
        requires validUndirectedGraph(g)
        requires hamiltonianCircuitPartialCorrectness(g, circuit)
    {
        |g|>0 &&
        (forall i :: 0<i<|g| ==> (g[circuit[i-1]][circuit[i]] || g[circuit[i]][circuit[i-1]])) &&  (g[circuit[|g|-1]][circuit[0]] || g[circuit[0]][circuit[|g|-1]])
    }

    // Both problems common lemma:
    //Hamiltonian circuit property: ensures that it contains every node of the graph exactly once
    ghost predicate hamiltonianCircuitPartialCorrectness(g: Graph, circuit: seq<nat>)
    {
        |circuit| == |g| && (forall i :: 0<=i<|g| ==> 0<=circuit[i]<|g| && !(exists j :: 0<=j<|g| && j!=i && circuit[i]==circuit[j]))
    }

}