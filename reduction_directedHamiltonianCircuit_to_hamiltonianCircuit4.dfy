type Graph = seq<seq<bool>>

//squared and triangular matrix
ghost predicate validUndirectedGraph(g: Graph)
{
    (forall s :: s in g ==> |s|==|g|) &&
    (forall n :: 0<=n<|g| ==> (forall v :: 0<=v<=n  ==> !g[n][v])) //por debajo de la diagonal -> false
}

//squared matrix
ghost predicate validGraph(g: Graph)
{
    forall s :: s in g ==> |s|==|g|
}

ghost predicate directedHamiltonianCircuit(g: Graph)
    requires validGraph(g)
{
    |g|>3 && exists hc :: isDirectedHamiltonianCircuit(g, hc)
}

ghost predicate isDirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
    requires validGraph(g)
    requires |g|>3
{
    hamiltonianCircuitPartialCorrectness(g, circuit) && isDirectedHamiltonianCircuit_(g, circuit, 1)
}

ghost predicate isDirectedHamiltonianCircuit_(g: Graph, circuit: seq<nat>, i: int)
    requires validGraph(g)
    requires hamiltonianCircuitPartialCorrectness(g, circuit)
    requires 0<i<|g|
    decreases |g|-i
{
    (i==|g|-1 && g[circuit[i]][circuit[0]])
    ||
    (i<|g|-1 && g[circuit[i-1]][circuit[i]] && isDirectedHamiltonianCircuit_(g, circuit, i+1))
}

ghost predicate undirectedHamiltonianCircuit(g: Graph)
    requires validGraph(g)
{
    |g|>3 && exists hc :: isUndirectedHamiltonianCircuit(g, hc)
}

ghost predicate isUndirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
    requires validGraph(g)
    requires |g|>3
{
    hamiltonianCircuitPartialCorrectness(g, circuit) && isUndirectedHamiltonianCircuit_(g, circuit, 1)
}

ghost predicate isUndirectedHamiltonianCircuit_(g: Graph, circuit: seq<nat>, i: int)
    requires validGraph(g)
    requires hamiltonianCircuitPartialCorrectness(g, circuit)
    requires 0<i<|g|
    decreases |g|-i
{
    (i==|g|-1 && (g[circuit[i]][circuit[0]] || g[circuit[0]][circuit[i]]))
    ||
    (i<|g|-1 && (g[circuit[i-1]][circuit[i]] || g[circuit[i]][circuit[i-1]]) && isUndirectedHamiltonianCircuit_(g, circuit, i+1))
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
    requires |g|>0
    requires validGraph(g)
    // ensures directed(validUndirectedGraph(g))
{
    var eg := extended_graph(g);
    var io := in_out_nodes(eg, |g|);
    direction_equivalence(g, io)
}

ghost function extended_graph(g: Graph): Graph
    requires validGraph(g)
    requires |g|>0
    ensures validUndirectedGraph(extended_graph(g))
    ensures |extended_graph(g)|==|g|*3    //original nodes +2 nodes per original node (nodeIn and nodeOut)
    ensures unconnected_graph(extended_graph(g))
{
    seq(|g|*3, i => seq(|g|*3, i => false))
}

ghost function in_out_nodes(g: Graph, s: int): Graph
    requires validUndirectedGraph(g)
    requires unconnected_graph(g)
    // requires |g|>0
    requires |g|==s*3
    ensures |in_out_nodes(g, s)| == |g|
    ensures validUndirectedGraph(in_out_nodes(g, s))
    ensures unconnected_in_out_graph(in_out_nodes(g, s), s)
    ensures forall f :: s<=f<|g| ==> (forall c :: 0<=c<|g| ==> !in_out_nodes(g, s)[f][c])
{
    in_out_nodes_(g, s, s-1)
}

ghost function in_out_nodes_(g: Graph, s: int, i: int): Graph
    requires validUndirectedGraph(g)
    requires forall f :: 0<=f<|g| ==> (forall c :: 0<=c<|g| ==> !g[f][c])
    // requires |g|>0
    requires |g|==s*3
    requires -1<=i< s
    decreases i
    ensures |in_out_nodes_(g, s, i)| == |g|
    ensures validUndirectedGraph(in_out_nodes_(g, s , i))
    // ensures forall f :: 0<=f<=i ==> in_out_nodes_(g, s, i)[f][f+s] && in_out_nodes_(g, s, i)[f][f+s*2]
    // ensures forall f :: 0<=f<=i ==> !(exists c :: 0<=c<|g| && c!=f+s && c!=f+s*2 && !in_out_nodes_(g, s, i)[f][c])
    ensures forall f :: i< f<|g| ==> (forall c :: 0<=c<|g| ==> !in_out_nodes_(g, s, i)[f][c])
    ensures forall f :: 0<=f<=i ==> (forall c :: 0<=c<|g| ==>
        (
            ((c==f+s || c==f+s*2) ==> in_out_nodes_(g, s, i)[f][c])     //in node: i+s, out node: i+s*2
            &&
            ((c!=f+s && c!=f+s*2) ==> !in_out_nodes_(g, s, i)[f][c])    //rest: false
        )
    )
{
    if i==-1 then g else
        var g' := in_out_nodes_(g, s, i-1);
        var f := g'[i];
        var f' := f[..i+s] + [true] + f[i+s+1..];           //out node
        var f'' := f'[..i+s*2] + [true] + f'[i+s*2+1..];    //in node
        g'[i:=f'']
}

//auxiliar predicates:
ghost predicate unconnected_graph(g: Graph)
    requires validGraph(g)
{
    forall f :: 0<=f<|g| ==> (forall c :: 0<=c<|g| ==> !g[f][c])
}

ghost predicate unconnected_in_out_graph(g: Graph, s: int)
    requires validUndirectedGraph(g)
    requires |g|==s*3
{
    forall f :: 0<=f< s ==> (forall c :: 0<=c<|g| ==>
        (
            ((c==f+s || c==f+s*2) ==> g[f][c])     //out node: i+s*2, in node: i+s
            &&
            ((c!=f+s && c!=f+s*2) ==> !g[f][c])    //rest: false
        )
    )
    &&
    forall f :: s<=f<|g| ==> (forall c :: 0<=c<|g| ==> !g[f][c])
}

ghost predicate in_out_nodes_unconnected(g: Graph, s: int, n: int)
    requires validUndirectedGraph(g)
    requires |g|==s*3
{
    forall c :: 0<=c<|g| ==> !g[]
}

ghost function direction_equivalence(g: Graph, g': Graph): Graph
    requires |g|>0
    requires validGraph(g)
    requires validUndirectedGraph(g')
    requires |g'|==|g|*3
    requires unconnected_in_out_graph(g', |g|)
{
    direction_equivalence_(g, g', |g|-1)
}

ghost function direction_equivalence_(g: Graph, g': Graph, i: int): Graph
    requires |g|>0
    requires validGraph(g)
    requires validUndirectedGraph(g')
    requires |g'|==|g|*3
    requires -1<=i<|g|
{
    if i==-1 then g' else
        var g'' := direction_equivalence_(g, g', i-1);
        //recorrer fila: si columna es true entonces [columna+s](out)[fila+s*2](in) := true
        g''
}

ghost function direction_equivalence_node(g: Graph, g': Graph, n: int): Graph
    requires |g|>0
    requires validGraph(g)
    requires validUndirectedGraph(g')
    requires |g'|==|g|*3
    requires 0<=n<|g|
{
    // direction_equivalence_node_(g, g', n, |g|-1)
    g'
}

/**
columna i del nodo n en g:
    si [n][i] true : hay una arista de n a i -> [n_out][i_in] := true : [n+s][i+s*2]:=true
    Nota:
        es importante el orden [n_out][n_in] porque los nodos out tienen un valor menor que los nodos in
        (n_out: n+s y n_in n+s*2 siendo n su nodo central) por lo que si fuese a la inversa no se conservaría
        la propiedad de matriz triangular superior utilizada, en este caso, para categorizar grafos no dirigidos.
 */
ghost function direction_equivalence_node_(g: Graph, g': Graph, n: int, i: int): Graph
    requires |g|>0
    requires validGraph(g)
    requires validGraph(g')
    requires |g'|==|g|*3
    requires validUndirectedGraph(g')
    requires 0<=n<|g|
    requires -1<=i<|g|
    ensures |direction_equivalence_node_(g, g', n, i)| == |g'|
    ensures validUndirectedGraph(direction_equivalence_node_(g, g', n, i))
    // ensures forall 
    ensures i>=0 ==> (g[n][i] <==> direction_equivalence_node_(g, g', n, i)[n+|g|][i+|g|*2])
    // ensures forall c :: 0<=c<=i ==>
    // (
    //     g[n][c] <==> direction_equivalence_node_(g, g', n, i)[n+|g|][c+|g|*2]
    // )
{
    if i==-1 then g' else
        var g'' := direction_equivalence_node_(g, g', n, i-1);
        //recorrer fila: si columna es true entonces [n+s](n_out)[i+s*2](i_in) := true
        if g[n][i] then
            var f_aux1 := g''[n+|g|];
            var f_aux2 := f_aux1[..i+|g|*2]+[true]+f_aux1[i+|g|*2+1..];
            g''[n+|g| := f_aux2]
        else
            g''
}
