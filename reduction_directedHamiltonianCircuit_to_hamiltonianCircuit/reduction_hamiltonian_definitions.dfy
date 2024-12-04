
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
        |g|>2 && exists hc :: isDirectedHamiltonianCircuit(g, hc)
    }

    ghost predicate isDirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
        requires validGraph(g)
        requires |g|>2
        // ensures forall i :: 0<i<|g| ==> g[circuit[i-1]][circuit[i]]
    {
        hamiltonianCircuitPartialCorrectness(g, circuit) && isDirectedHamiltonianCircuit3(g, circuit)
    }

    // ghost predicate isDirectedHamiltonianCircuit_(g: Graph, circuit: seq<nat>, c: int, i: int)
    //     requires validGraph(g)
    //     requires hamiltonianCircuitPartialCorrectness(g, circuit)
    //     requires 0<=c<=|g|
    //     requires 0<=i<|g|
    //     // ensures forall j :: 0<j<|g| ==> g[circuit[j-1]][circuit[j]]
    // {
    //     c==0
    //     ||
    //     (
    //         (i==|g|-1 && g[circuit[i]][circuit[0]] && isDirectedHamiltonianCircuit_(g, circuit, c-1, 0))
    //         ||
    //         (i<|g|-1 && g[circuit[i]][circuit[i+1]] && isDirectedHamiltonianCircuit_(g, circuit, c-1, i+1))
    //     )
    // }

    // least predicate isDirectedHamiltonianCircuit2_(g: Graph, circuit: seq<nat>, i: int)
    //     requires validGraph(g)
    //     requires hamiltonianCircuitPartialCorrectness(g, circuit)
    //     requires 0<=i<|g|
    // {
    //     (i==|g|-1 && g[circuit[i]][circuit[0]] && isDirectedHamiltonianCircuit2_(g, circuit, 0))
    //     ||
    //     (i<|g|-1 && g[circuit[i]][circuit[i+1]] && isDirectedHamiltonianCircuit2_(g, circuit, i+1))
    // }

    ghost predicate isDirectedHamiltonianCircuit3(g: Graph, circuit: seq<nat>)
        requires validGraph(g)
        requires |g|>2
        requires hamiltonianCircuitPartialCorrectness(g, circuit)
    {
        (forall i :: 0<i<|g| ==> g[circuit[i-1]][circuit[i]]) && (g[circuit[|g|-1]][circuit[0]])
    }

    //Problem's auxiliar lemmas:

    // lemma directedHamiltonianCircuitProperty_lemma(g: Graph, circuit: seq<nat>)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires isDirectedHamiltonianCircuit(g, circuit)
    //     ensures (forall i :: 0<i<|g| ==> g[circuit[i-1]][circuit[i]]) && (g[circuit[|g|-1]][circuit[0]])
    // {
    //     forall i | 0<i<|g|
    //     {
    //         directedHamiltonianaCircuitProperty_local_lemma(g, circuit, i);
    //     }
    //     directedHamiltonianCircuitProperty_aux_lemma(g, circuit);
    // }

    // lemma directedHamiltonianCircuitProperty_aux_lemma(g: Graph, circuit: seq<nat>)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires isDirectedHamiltonianCircuit(g, circuit)
    //     ensures g[circuit[|g|-1]][circuit[0]]
    // {
    //     directedHamiltonianCircuitProperty_aux_inductive_lemma(g, circuit, 1);
    // }

    // lemma directedHamiltonianCircuitProperty_aux_inductive_lemma(g: Graph, circuit: seq<nat>, i: int)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires 0<i<|g|
    //     requires hamiltonianCircuitPartialCorrectness(g, circuit)
    //     requires isDirectedHamiltonianCircuit2_(g, circuit, i)
    //     decreases |g|-i
    //     ensures g[circuit[|g|-1]][circuit[0]]
    // {}

    // lemma directedHamiltonianaCircuitProperty_local_lemma(g: Graph, circuit: seq<nat>, i: int)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires isDirectedHamiltonianCircuit(g, circuit)
    //     requires 0<i<|g|
    //     ensures g[circuit[i-1]][circuit[i]]
    // {
    //     if i>1
    //     {
    //         directedHamiltonianaCircuitProperty_local_lemma(g, circuit, i-1);
    //         assert g[circuit[i-2]][circuit[i-1]];   //H.I
    //         directedHamiltonianCircuitModularity_lemma(g, circuit);
    //         assert isDirectedHamiltonianCircuit2_(g, circuit, i-1); //no se muy bien cómo
    //     }
    // }

    // lemma directedHamiltonianCircuitModularity_lemma(g: Graph, circuit: seq<nat>)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires isDirectedHamiltonianCircuit(g, circuit)
    //     ensures forall i :: 0<=i<|g| ==> isDirectedHamiltonianCircuit2_(g, circuit, i)
    // {
    //     forall i | 0<=i<|g|
    //     {
    //         directedHamiltonianCircuitModularity_local_lemma(g, circuit, i);
    //     }
    // }

    // lemma directedHamiltonianCircuitModularity_local_lemma(g: Graph, circuit: seq<nat>, i: int)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires 0<=i<|g|
    //     requires isDirectedHamiltonianCircuit(g, circuit)
    //     ensures isDirectedHamiltonianCircuit2_(g, circuit, i)
    // {
    //     if i>0
    //     {
    //         directedHamiltonianCircuitModularity_local_lemma(g, circuit, i-1);
    //     }
    // }

    /////// UNDIRECTED HAMILTONIAN CIRCUIT ///////

    //Definition predicates:

    ghost predicate undirectedHamiltonianCircuit(g: Graph)
        requires validUndirectedGraph(g)
    {
        |g|>2 && exists hc :: isUndirectedHamiltonianCircuit(g, hc)
    }

    ghost predicate isUndirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2
    {
        hamiltonianCircuitPartialCorrectness(g, circuit) && isUndirectedHamiltonianCircuit3(g, circuit)
    }

    // least predicate isUndirectedHamiltonianCircuit2_(g: Graph, circuit: seq<nat>, i: int)
    //     requires validUndirectedGraph(g)
    //     requires hamiltonianCircuitPartialCorrectness(g, circuit)
    //     requires 0<=i<|g|
    // {
    //     (i==|g|-1 && (g[circuit[i]][circuit[0]] || g[circuit[0]][circuit[i]]) && isUndirectedHamiltonianCircuit2_(g, circuit, 0))
    //     ||
    //     (i<|g|-1 && (g[circuit[i]][circuit[i+1]] || g[circuit[i+1]][circuit[i]]) && isUndirectedHamiltonianCircuit2_(g, circuit, i+1))
    // }

    ghost predicate isUndirectedHamiltonianCircuit3(g: Graph, circuit: seq<nat>)
        requires validUndirectedGraph(g)
        requires hamiltonianCircuitPartialCorrectness(g, circuit)
        requires |g|>2
    {
        (forall i :: 0<i<|g| ==> (g[circuit[i-1]][circuit[i]] || g[circuit[i]][circuit[i-1]])) &&  (g[circuit[|g|-1]][circuit[0]] || g[circuit[0]][circuit[|g|-1]])
    }

    //Problem's auxiliar lemmas:

    // lemma undirectedHamiltonianCircuitProperty_lemma(g: Graph, circuit: seq<nat>)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2
    //     requires isUndirectedHamiltonianCircuit(g, circuit)
    //     ensures (forall i :: 0<i<|g| ==> (g[circuit[i-1]][circuit[i]] || g[circuit[i]][circuit[i-1]])) &&  (g[circuit[|g|-1]][circuit[0]] || g[circuit[0]][circuit[|g|-1]])
    // {
    //     forall i | 0<i<|g|
    //     {
    //         undirectedHamiltonianaCircuitProperty_local_lemma(g, circuit, i);
    //     }
    //     undirectedHamiltonianCircuitProperty_aux_lemma(g, circuit);
    // }

    // lemma undirectedHamiltonianCircuitProperty_aux_lemma(g: Graph, circuit: seq<nat>)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2
    //     requires isUndirectedHamiltonianCircuit(g, circuit)
    //     ensures g[circuit[|g|-1]][circuit[0]] || g[circuit[0]][circuit[|g|-1]]
    // {
    //     undirectedHamiltonianCircuitProperty_aux_inductive_lemma(g, circuit, 1);
    // }

    // lemma undirectedHamiltonianCircuitProperty_aux_inductive_lemma(g: Graph, circuit: seq<nat>, i: int)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2
    //     requires 0<i<|g|
    //     requires hamiltonianCircuitPartialCorrectness(g, circuit)
    //     requires isUndirectedHamiltonianCircuit2_(g, circuit, i)
    //     decreases |g|-i
    //     ensures g[circuit[|g|-1]][circuit[0]] || g[circuit[0]][circuit[|g|-1]]
    // {}

    // lemma undirectedHamiltonianaCircuitProperty_local_lemma(g: Graph, circuit: seq<nat>, i: int)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2
    //     requires isUndirectedHamiltonianCircuit(g, circuit)
    //     requires 0<i<|g|
    //     ensures g[circuit[i-1]][circuit[i]] || g[circuit[i]][circuit[i-1]]
    // {
    //     if i>1
    //     {
    //         undirectedHamiltonianaCircuitProperty_local_lemma(g, circuit, i-1);
    //         assert g[circuit[i-2]][circuit[i-1]] || g[circuit[i-1]][circuit[i-2]];   //H.I
    //         undirectedHamiltonianCircuitModularity_lemma(g, circuit);
    //         assert isUndirectedHamiltonianCircuit2_(g, circuit, i-1);
    //     }
    // }

    // lemma undirectedHamiltonianCircuitModularity_lemma(g: Graph, circuit: seq<nat>)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2
    //     requires isUndirectedHamiltonianCircuit(g, circuit)
    //     ensures forall i :: 0<=i<|g| ==> isUndirectedHamiltonianCircuit2_(g, circuit, i)
    // {
    //     forall i | 0<=i<|g|
    //     {
    //         undirectedHamiltonianCircuitModularity_local_lemma(g, circuit, i);
    //     }
    // }

    // lemma undirectedHamiltonianCircuitModularity_local_lemma(g: Graph, circuit: seq<nat>, i: int)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2
    //     requires 0<=i<|g|
    //     requires isUndirectedHamiltonianCircuit(g, circuit)
    //     ensures isUndirectedHamiltonianCircuit2_(g, circuit, i)
    // {
    //     if i>0
    //     {
    //         undirectedHamiltonianCircuitModularity_local_lemma(g, circuit, i-1);
    //     }
    // }

    // Both problems common lemma:
    //Hamiltonian circuit property: ensures that it contains every node of the graph exactly once
    ghost predicate hamiltonianCircuitPartialCorrectness(g: Graph, circuit: seq<nat>)
    {
        |circuit| == |g| && (forall i :: 0<=i<|g| ==> 0<=circuit[i]<|g| && !(exists j :: 0<=j<|g| && j!=i && circuit[i]==circuit[j]))
    }

}