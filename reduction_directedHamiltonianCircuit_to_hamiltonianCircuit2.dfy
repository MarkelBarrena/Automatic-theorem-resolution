type Graph = seq<seq<bool>>

//squared and symetric matrix
ghost predicate validUndirectedGraph(g: Graph)
{
    (forall s :: s in g ==> |s|==|g|) &&
    (forall n :: 0<=n<|g| ==> (forall v :: 0<=v<|g| && v!=n ==> (g[n][v] <==> g[v][n])))
}

//squared matrix
ghost predicate validGraph(g: Graph)
{
    forall s :: s in g ==> |s|==|g|
}

ghost predicate hamiltonianCircuit(g: Graph)
    requires validGraph(g)
{
    |g|>3 && exists hc :: isHamiltonianCircuit(g, hc)
}

ghost predicate isHamiltonianCircuit(g: Graph, circuit: seq<nat>)
    requires validGraph(g)
    requires |g|>3
{
    hamiltonianCircuitPartialCorrectness(g, circuit) && isHamiltonianCircuit_(g, circuit, 1)
}

//it is valid for directed and undirected graphs
ghost predicate isHamiltonianCircuit_(g: Graph, circuit: seq<nat>, i: int)
    requires validGraph(g)
    requires hamiltonianCircuitPartialCorrectness(g, circuit)
    requires 0<i<|g|
{
    (i==|g|-1 && g[circuit[i]][circuit[0]])
    ||
    (i<|g|-1 && g[circuit[i-1]][circuit[i]])
}

//ensures that it contains every node of the graph exactly once
ghost predicate hamiltonianCircuitPartialCorrectness(g: Graph, circuit: seq<nat>)
{
    |circuit| == |g| && (forall i :: 0<=i<|g| ==> 0<=circuit[i]<|g| && !(exists j :: 0<=j<|g| && j!=i && circuit[i]==circuit[j]))
}

/**
The reduction:
 */

ghost function directed_to_undirected_graph(g: Graph): Graph
    requires validGraph(g)
    // ensures directed(validUndirectedGraph(g))
{
    directed_to_undirected_graph_(g, 0)
}

ghost function extend_graph(g: Graph): Graph
    requires validGraph(g)
    requires |g|>0
    ensures validGraph(extend_graph(g))
    ensures |extend_graph(g)|==|g|*3    //original nodes +2 nodes per original node (nodeIn and nodeOut)
    ensures forall f :: 0<=f<|g| ==> (forall c :: 0<=c<|g| ==> extend_graph(g)[f][c] == g[f][c])
    ensures forall f :: 0<=f<|g| ==> (forall c :: |g|<=c<|g|*3 ==> !extend_graph(g)[f][c])
    ensures forall f :: |g|<=f<|g|*3 ==> (forall c :: 0<=c<|g|*3 ==> !extend_graph(g)[f][c])
{
    var g':= add_columns(g, |g|-1);
    add_columns_aux_Lemma(g, |g|-1);
    g' + seq(|g|*2, i => seq(|g|*3, i => false))
}

ghost function add_columns(g: Graph, i: int): Graph
    requires -1<=i<|g|
    requires validGraph(g)
    ensures |g|==|add_columns(g, i)|
    ensures forall j :: i< j<|g| ==> |add_columns(g, i)[j]| == |g|
    ensures forall j :: 0<=j<=i ==> |add_columns(g, i)[j]| == |g|*3
    ensures forall f :: 0<=f<=i ==> (forall c :: |g|<=c<|g|*3 ==> !add_columns(g,i)[f][c])
    // ensures i>=0 ==> (add_columns(g, i)[i][0..|g|] == g[i])
{
    if i==-1 then g else
        var g':= add_columns(g, i-1);
        var s: seq<bool> := g'[i]+ seq(|g|*2, i => false);
        g'[i:= s]
}

lemma add_columns_aux_Lemma(g: Graph, i: int)
    requires 0<=i<|g|
    requires validGraph(g)
    ensures forall f :: 0<=f<=i ==> (add_columns(g, i)[f][0..|g|] == g[f])
{
    if i>0
    {
        add_columns_aux_Lemma(g, i-1);
        add_columns_aux_Lemma2(g, i);
    }
}

lemma add_columns_aux_Lemma2(g: Graph, i: int)
    requires 0<=i<|g|
    requires validGraph(g)
    ensures add_columns(g, i)[i][0..|g|]==g[i]
{
    if i>0
    {
        add_columns_aux_Lemma2(g, i-1);
        assert add_columns(g, i-1)[i-1][0..|g|]==g[i-1];

    }
}

lemma playground()
{
    var m1 :=
        [
            [1,2,3],
            [4,5,6],
            [7,8,9]
        ];
    var m2 :=
        [
            [1,2,3,0,0,0,0,0,0],
            [4,5,6,0,0,0,0,0,0],
            [7,8,9,0,0,0,0,0,0],
            [0,0,0,0,0,0,0,0,0],
            [0,0,0,0,0,0,0,0,0],
            [0,0,0,0,0,0,0,0,0],
            [0,0,0,0,0,0,0,0,0],
            [0,0,0,0,0,0,0,0,0],
            [0,0,0,0,0,0,0,0,0]
        ];
    assert forall f :: 0<=f<|m1| ==> m2[f][0..|m1|]==m1[f];
}

ghost function directed_to_undirected_graph_(g: Graph, i: int): Graph
    requires validGraph(g)
    requires 0<=i<=|g|
{
    if i==|g| then g else
        var g' := g;
        g'
        // in_nodes(g, i)
}