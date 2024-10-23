datatype Graph = G(V: nat, E: set<(nat, nat)>)

ghost predicate validNonDirectedGraph(g: Graph)
{
    forall e :: e in g.E ==> 0<e.0<e.1<=g.V
}

ghost predicate validDirectedGraph(g: Graph)
{
    forall e:: e in g.E ==> 0<e.0<=g.V && 0<e.1<=g.V && e.0!=e.1
}

ghost predicate nonDirectedHamiltonianCircuit(g: Graph)
    requires validNonDirectedGraph(g)
{
    g.V>=3 && exists circuit: seq<nat> :: |circuit|==g.V && isNonDirectedHamiltonianCircuit(g, circuit)
}

ghost predicate directedHamiltonianCircuit(g: Graph)
    requires validDirectedGraph(g)
{
    g.V>=3 && exists circuit: seq<nat> :: |circuit|==g.V && isDirectedHamiltonianCircuit(g, circuit)
}

ghost predicate isNonDirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
    requires validNonDirectedGraph(g)
    requires g.V>=3
    requires |circuit| == g.V
{
    isNonDirectedHamiltonianCircuit_(g, circuit, 1)
}

ghost predicate isNonDirectedHamiltonianCircuit_(g: Graph, circuit: seq<nat>, i: int)
    requires validNonDirectedGraph(g)
    requires g.V>=3
    requires 0<i<|circuit|==g.V
    decreases |circuit|-i
{
    (i==g.V-1 && ((circuit[i], circuit[0]) in g.E || (circuit[0], circuit[i]) in g.E))
    ||
    (
        i< g.V-1
        &&
        (
            ((circuit[i-1], circuit[i]) in g.E || (circuit[i], circuit[i-1]) in g.E) &&
            (forall j :: (0<=j<|circuit| && j!=i) ==> circuit[j]!=circuit[i])
        )
        &&
        isNonDirectedHamiltonianCircuit_(g, circuit, i+1)
    )
}

ghost predicate isDirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
    requires validDirectedGraph(g)
    requires g.V>=3
    requires |circuit| == g.V
{
    isDirectedHamiltonianCircuit_(g, circuit, 1)
}

ghost predicate isDirectedHamiltonianCircuit_(g: Graph, circuit: seq<nat>, i: int)
    requires validDirectedGraph(g)
    requires g.V>=3
    requires 0<i<|circuit|==g.V
    decreases |circuit|-i
{
    (i==g.V-1 && (circuit[i], circuit[0]) in g.E)
    ||
    (
        i< g.V-1
        &&
        (
            (circuit[i-1], circuit[i]) in g.E &&
            (forall j :: (0<=j<|circuit| && j!=i) ==> circuit[j]!=circuit[i])
        )
        &&
        isDirectedHamiltonianCircuit_(g, circuit, i+1)
    )
}

/**
The reduction: directedHamiltonianCircuit <=p nonDirectedHamiltonianCircuit
 */

//reduction function
ghost function directed_to_nonDirected_graph(g: Graph): Graph
    requires validDirectedGraph(g)
    ensures validNonDirectedGraph(directed_to_nonDirected_graph(g))
    // ensures 