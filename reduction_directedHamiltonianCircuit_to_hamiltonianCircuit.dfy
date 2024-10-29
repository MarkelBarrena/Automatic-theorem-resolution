datatype Graph = G(V: set<nat>, E: set<(nat, nat)>)

ghost predicate validUndirectedGraph(g: Graph)
{
    forall n :: n in g.V ==> 0<n<|g.V| &&
    forall e :: e in g.E ==> 0<e.0<e.1<=|g.V|
}

ghost predicate validDirectedGraph(g: Graph)
{
    forall n :: n in g.V ==> 0<n<=|g.V| &&
    forall e:: e in g.E ==> 0<e.0<=|g.V| && 0<e.1<=|g.V| && e.0!=e.1
}

ghost predicate undirectedHamiltonianCircuit(g: Graph)
    requires validUndirectedGraph(g)
{
    |g.V|>=3 && exists circuit: seq<nat> :: |circuit|==|g.V| && isUndirectedHamiltonianCircuit(g, circuit)
}

ghost predicate directedHamiltonianCircuit(g: Graph)
    requires validDirectedGraph(g)
{
    |g.V|>=3 && exists circuit: seq<nat> :: |circuit|==|g.V| && isDirectedHamiltonianCircuit(g, circuit)
}

ghost predicate isUndirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
    requires validUndirectedGraph(g)
    requires |g.V|>=3
    requires |circuit| == |g.V|
{
    isUndirectedHamiltonianCircuit_(g, circuit, 1)
}

ghost predicate isUndirectedHamiltonianCircuit_(g: Graph, circuit: seq<nat>, i: int)
    requires validUndirectedGraph(g)
    requires |g.V|>=3
    requires 0<i<|circuit|==|g.V|
    decreases |circuit|-i
{
    (i==|g.V|-1 && ((circuit[i], circuit[0]) in g.E || (circuit[0], circuit[i]) in g.E))
    ||
    (
        i< |g.V|-1
        &&
        (
            ((circuit[i-1], circuit[i]) in g.E || (circuit[i], circuit[i-1]) in g.E) &&
            (forall j :: (0<=j<|circuit| && j!=i) ==> circuit[j]!=circuit[i])
        )
        &&
        isUndirectedHamiltonianCircuit_(g, circuit, i+1)
    )
}

ghost predicate isDirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
    requires validDirectedGraph(g)
    requires |g.V|>=3
    requires |circuit| == |g.V|
{
    isDirectedHamiltonianCircuit_(g, circuit, 1)
}

ghost predicate isDirectedHamiltonianCircuit_(g: Graph, circuit: seq<nat>, i: int)
    requires validDirectedGraph(g)
    requires |g.V|>=3
    requires 0<i<|circuit|==|g.V|
    decreases |circuit|-i
{
    (i==|g.V|-1 && (circuit[i], circuit[0]) in g.E)
    ||
    (
        i< |g.V|-1
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
The reduction: directedHamiltonianCircuit <=p undirectedHamiltonianCircuit
 */

//reduction function
ghost function directed_to_undirected_graph(g: Graph): Graph
    requires validDirectedGraph(g)
    ensures validUndirectedGraph(directed_to_undirected_graph(g))
    ensures |directed_to_undirected_graph(g).V| == |g.V|+(2*|g.V|)
    ensures var g':= directed_to_undirected_graph(g);
    (
        (
            forall n :: n in g.V ==> exists nIn, nOut :: (nIn in g'.V && nOut in g'.V) && ((n, nIn) in g'.E && (n, nOut) in g'.E)
        )
        &&
        (
            forall u, v :: u in g.V && v in g.V ==>
                (u, v) 
        )
    )
