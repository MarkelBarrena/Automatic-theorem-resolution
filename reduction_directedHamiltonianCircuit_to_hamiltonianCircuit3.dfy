type Graph = seq<seq<bool>>

//squared and triangular superior matrix
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
    // ensures forall i :: 0<i<|g| ==> g[circuit[i-1]][circuit[i]]
{
    hamiltonianCircuitPartialCorrectness(g, circuit) && isDirectedHamiltonianCircuit_(g, circuit, 1)
}

ghost predicate isDirectedHamiltonianCircuit_(g: Graph, circuit: seq<nat>, i: int)
    requires validGraph(g)
    requires hamiltonianCircuitPartialCorrectness(g, circuit)
    requires 0<i<|g|
    decreases |g|-i
    // ensures forall j :: 0<j<|g| ==> g[circuit[j-1]][circuit[j]]
{
    (i==|g|-1 && g[circuit[i]][circuit[0]])
    ||
    (i<|g|-1 && g[circuit[i-1]][circuit[i]] && isDirectedHamiltonianCircuit_(g, circuit, i+1))
}

lemma provePostconditionIsDirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
    requires validGraph(g)
    requires |g| > 3
    requires hamiltonianCircuitPartialCorrectness(g, circuit)
    requires isDirectedHamiltonianCircuit_(g, circuit, 1)
    ensures forall i :: 0 < i < |g| ==> g[circuit[i-1]][circuit[i]]
{}

ghost predicate undirectedHamiltonianCircuit(g: Graph)
    requires validUndirectedGraph(g)
{
    |g|>3 && exists hc :: isUndirectedHamiltonianCircuit(g, hc)
}

ghost predicate isUndirectedHamiltonianCircuit(g: Graph, circuit: seq<nat>)
    requires validUndirectedGraph(g)
    requires |g|>3
{
    hamiltonianCircuitPartialCorrectness(g, circuit) && isUndirectedHamiltonianCircuit_(g, circuit, 1)
}

ghost predicate isUndirectedHamiltonianCircuit_(g: Graph, circuit: seq<nat>, i: int)
    requires validUndirectedGraph(g)
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

/////// AUXILIAR PREDICATES //////

ghost predicate unconnected_graph(g: Graph)
    requires validGraph(g)
{
    forall f :: 0<=f<|g| ==> (forall c :: 0<=c<|g| ==> !g[f][c])
}

//original nodes are only adjacent to their respective out and in nodes and there are only out->in vertex
ghost predicate in_out_graph(g: Graph, s: int)
    requires validUndirectedGraph(g)
    requires |g|==s*3
{
    forall f :: 0<=f< s ==> (forall c :: 0<=c<|g| ==>
        (
            ((c==f+s || c==f+s*2) ==> g[f][c])     //out node: i+s, in node: i+s*2
            &&
            ((c!=f+s && c!=f+s*2) ==> !g[f][c])    //rest: false (original nodes are not interconnected)
        )
    )
    &&
    (forall f :: s<=f< s*2 ==> (forall c :: s<=c< s*2 ==> !g[f][c]))    //no vertex from out to out
    &&
    (forall f :: s*2<=f< s*3 ==> (forall c :: s*2<=c< s*3 ==> !g[f][c]))    //no vertex from in to in
}

ghost predicate unconnected_in_out_graph(g: Graph, s: int)
    requires validUndirectedGraph(g)
    requires |g|==s*3
{
    in_out_graph(g, s)
    &&
    forall f :: s<=f<|g| ==> (forall c :: 0<=c<|g| ==> !g[f][c])
}

ghost predicate out_node_unconnected(g: Graph, g0: Graph, n: int)
    requires validUndirectedGraph(g)
    requires |g|==|g0|*3
    requires 0<=n< |g0|
{
    forall c :: 0<=c< |g| ==> !g[n+|g0|][c] //no vertex for n_out node
}

/////// REDUCTION FUNCTION ///////

ghost function directed_to_undirected_graph(g: Graph): Graph
    requires validGraph(g)
    //size relation
    ensures |directed_to_undirected_graph(g)| == |g|*3
    //squared and triangular superior matrix
    ensures validUndirectedGraph(directed_to_undirected_graph(g))
    //original nodes are only adjacent to their respective out and in nodes and there are only out->in vertex
    ensures in_out_graph(directed_to_undirected_graph(g), |g|)
    //direction relation: n1->n2 in g only and only if n1_out-n2_in in g'
    ensures forall f :: 0<=f<|g| ==> (forall c :: 0<=c<|g| ==> (g[f][c] <==> directed_to_undirected_graph(g)[f+|g|][c+|g|*2]))
{
    if |g|==0 then g else direction_equivalence(g, in_out_nodes(extended_graph(g), |g|))
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

ghost function direction_equivalence(g: Graph, g': Graph): Graph
    requires |g|>0
    requires validGraph(g)
    requires validUndirectedGraph(g')
    requires |g'|==|g|*3
    requires unconnected_in_out_graph(g', |g|)
    //size persistence
    ensures |direction_equivalence(g, g')| == |g'|
    //squared and triangular superior matrix
    ensures validUndirectedGraph(direction_equivalence(g, g'))
    //original nodes are only adjacent to their respective out and in nodes and there are only out->in vertex
    ensures in_out_graph(direction_equivalence(g, g'), |g|)
    //modifying property: n1->n2 in g only and only if n1_out-n2_in in g'
    ensures forall f :: 0<=f<|g| ==> (forall c :: 0<=c<|g| ==> (g[f][c] <==> direction_equivalence(g, g')[f+|g|][c+|g|*2]))
{
    direction_equivalence_(g, g', |g|-1)
}

ghost function direction_equivalence_(g: Graph, g': Graph, i: int): Graph
    requires |g|>0
    requires validGraph(g)
    requires validUndirectedGraph(g')
    requires |g'|==|g|*3
    requires -1<=i<|g|
    requires unconnected_in_out_graph(g', |g|)
    ensures |direction_equivalence_(g, g', i)| == |g'|
    ensures validUndirectedGraph(direction_equivalence_(g, g', i))
    //only out nodes are modified (original nodes and in nodes stay the same)
    ensures forall f :: 0<=f<|g| ==> (g'[f] == direction_equivalence_(g, g', i)[f])
    ensures forall f :: |g|*2<=f<|g'| ==> (g'[f] == direction_equivalence_(g, g', i)[f])
    //only out to in vertex are modified so vertex in the range [0]..[|g|*2-1] stay the same
    ensures forall f :: |g|<=f<|g|*2 ==> (forall c :: 0<=c<|g|*2 ==> (g'[f][c] == direction_equivalence_(g, g', i)[f][c]))
    //inductive postconditions
    //every row yet to process stay the same
    ensures forall f :: i+|g|< f<|g'| ==> (g'[f] == direction_equivalence_(g, g', i)[f])
    //modifying property: for every processed row: n_out to c_in in g' if and only if n to c in g
    ensures forall f :: 0<=f<=i ==> (forall c :: 0<=c<|g| ==> (g[f][c] <==> direction_equivalence_(g, g', i)[f+|g|][c+|g|*2]))
{
    if i==-1 then g' else
        var g'' := direction_equivalence_(g, g', i-1);
        //recorrer fila: si columna es true entonces [fila+s](out)[columna+s*2](in) := true
        var gF := direction_equivalence_node(g, g'', i);
        gF
}

ghost function direction_equivalence_node(g: Graph, g': Graph, n: int): Graph
    requires |g|>0
    requires validGraph(g)
    requires validUndirectedGraph(g')
    requires |g'|==|g|*3
    requires 0<=n<|g|
    requires out_node_unconnected(g', g, n)
    ensures |direction_equivalence_node(g, g', n)| == |g'|
    ensures validUndirectedGraph(direction_equivalence_node(g, g', n))
    //only n_out's row is modified
    ensures forall f :: 0<=f<|g'| && f!=n+|g| ==> (g'[f] == direction_equivalence_node(g, g', n)[f])
    //only n_out to x_in vertex are modified, so columns below n+|g|*2 stay the same (set to false)
    ensures forall c :: 0<=c<|g|*2 ==> (g'[n+|g|][c] == direction_equivalence_node(g, g', n)[n+|g|][c])
    ensures forall c :: 0<=c<|g|*2 ==> !direction_equivalence_node(g, g', n)[n+|g|][c]
    //modifying property: n_out to c_in in g' if and only if n to c in g
    ensures forall c :: 0<=c<|g| ==> (g[n][c] <==> direction_equivalence_node(g, g', n)[n+|g|][c+|g|*2])
{
    direction_equivalence_node_(g, g', n, |g|-1)
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
    requires validUndirectedGraph(g')
    requires |g'|==|g|*3
    requires 0<=n<|g|
    requires -1<=i<|g|
    requires out_node_unconnected(g', g, n)
    ensures |direction_equivalence_node_(g, g', n, i)| == |g'|
    ensures validUndirectedGraph(direction_equivalence_node_(g, g', n, i))
    //only n_out's row is modified
    ensures forall f :: 0<=f<|g'| && f!=n+|g| ==> (g'[f] == direction_equivalence_node_(g, g', n, i)[f])
    //only n_out -> x_in vertex are modified, so columns below n+|g|*2 stay the same
    ensures forall c :: 0<=c<|g|*2 ==> (g'[n+|g|][c] == direction_equivalence_node_(g, g', n, i)[n+|g|][c])
    //inductive postconditions:
    //every column yet to process stays the same (set to false)
    ensures forall f :: i+|g|*2< f<|g'| ==> (g'[n+|g|][f] == direction_equivalence_node_(g, g', n, i)[n+|g|][f])
    ensures forall f :: i< f<|g| ==> (g'[n+|g|][f+|g|*2] == direction_equivalence_node_(g, g', n, i)[n+|g|][f+|g|*2])
    ensures forall f :: i< f<|g| ==> !direction_equivalence_node_(g, g', n, i)[n+|g|][f+|g|*2]
    //modifying property: n_out to i_in in g' if and only if n to c in g
    ensures forall c :: 0<=c<=i ==>
    (
        g[n][c] <==> direction_equivalence_node_(g, g', n, i)[n+|g|][c+|g|*2]
    )
{
    if i==-1 then
        g'
    else
        var g'' := direction_equivalence_node_(g, g', n, i-1);
        if g[n][i] then
            var f_aux1 := g''[n+|g|];
            var f_aux2 := f_aux1[..i+|g|*2]+[true]+f_aux1[i+|g|*2+1..];
            var gF := g''[n+|g| := f_aux2];
            gF
        else
            g''
}


///// REDUCTION COMPLETNESS /////

lemma reduction_lemma(g: Graph)
    requires validGraph(g)
    ensures directedHamiltonianCircuit(g) <==> undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
{
    if directedHamiltonianCircuit(g)
    {
        reduction_lemma_right(g);
    }
    if undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
    {
        reduction_lemma_left(g);
    }
}

lemma reduction_lemma_right(g: Graph)
    requires validGraph(g)
    requires directedHamiltonianCircuit(g)
    ensures undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
{
    var g' := directed_to_undirected_graph(g);
    var dhc := directedHamiltonianCircuit_witness(g);
    assert isDirectedHamiltonianCircuit_(g, dhc, 1);
    assert forall i :: 0<i<|g| ==> g[dhc[i-1]][dhc[i]];
}

lemma reduction_lemma_left(g: Graph)
    requires validGraph(g)
    requires undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
    ensures directedHamiltonianCircuit(g)
{

}

ghost function directedHamiltonianCircuit_witness(g: Graph): seq<nat>
    requires validGraph(g)
    requires directedHamiltonianCircuit(g)
    ensures isDirectedHamiltonianCircuit(g, (directedHamiltonianCircuit_witness(g)))

ghost function undirectedHamiltonianCircuit_witness(g: Graph): seq<nat>
    requires validUndirectedGraph(g)
    requires undirectedHamiltonianCircuit(g)
    ensures isUndirectedHamiltonianCircuit(g, (undirectedHamiltonianCircuit_witness(g)))
