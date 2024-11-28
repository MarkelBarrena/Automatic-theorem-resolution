
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

/***************
REDUCTION: DIRECTED HAMILTONIAN <p UNDIRECTED HAMILTONIAN
****************/

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
    //size relation: 2 extra nodes (node_in and node_out) per node
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
            ((c==f+s || c==f+s*2) ==> in_out_nodes_(g, s, i)[f][c])     //out node: i+s, in node: i+s*2
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

// Reduction to the right: directedHamiltonian(g) ==> undirectedHamiltonian(f(g))

lemma reduction_lemma_right(g: Graph)
    requires validGraph(g)
    requires directedHamiltonianCircuit(g)
    ensures undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
{
    var g' := directed_to_undirected_graph(g);

    assert |g'|>2;
    var dhc :| isDirectedHamiltonianCircuit(g, dhc);

    // directedHamiltonianCircuitProperty_lemma(g, dhc);
    assert forall i :: 0<i<|g| ==> g[dhc[i-1]][dhc[i]] && g[dhc[|g|-1]][dhc[0]];

    var dhc_eq := circuit_equivalence(g, g', dhc);

    // var dhc_uEq := circuit_equivalence(g, g', dhc);
    // circuit_equivalent_lemma(g, g', dhc, dhc_uEq);

    // assert forall i :: 0<i<|g| ==> (g[dhc[i-1]][dhc[i]] ==> g'[dhc[i-1]+|g|][dhc[i]+|g|*2]);
    // assert forall i :: 0<i<|g| ==> (g[dhc[i-1]][dhc[i]] ==> g'[dhc[i-1]+|g|][dhc[i]+|g|*2]);
    // assert g[dhc[|g|-1]][dhc[0]] ==> g'[dhc[|g|-1]+|g|][dhc[0]+|g|*2];
    
}

// ghost predicate circuit_equivalent(g: Graph, g': Graph, circuit: seq<nat>, circuit': seq<nat>)
//     requires validGraph(g)
//     requires |g|>2
//     requires isDirectedHamiltonianCircuit(g, circuit)
//     requires g' == directed_to_undirected_graph(g)
//     // ensures forall i :: (0<=i<|circuit'| && i % 3 ==1)  ==> circuit'[i] == circuit[(i-1)/3]
// {
//     |circuit'|==|g|*3
//     &&
//     (
//         forall i :: 0<=i<|g| ==>    //giving the index of the original node i, the index of the same node in circuit': f(i)=3i+1
//         (
//             circuit'[i*3]==circuit[i]+|g|*2 //in node
//             &&
//             circuit'[i*3+1]==circuit[i] //central (original) node
//             &&
//             circuit'[i*3+2]==circuit[i]+|g| //out node
//         )
//     )
// }

// lemma circuit_equivalent_aux1_lemma(g: Graph, g': Graph, circuit: seq<nat>, circuit': seq<nat>)
//     requires validGraph(g)
//     requires |g|>2
//     requires isDirectedHamiltonianCircuit(g, circuit)
//     requires g' == directed_to_undirected_graph(g)
//     requires circuit_equivalent(g, g', circuit, circuit')
//     ensures forall i :: 0<=i<|circuit'| ==> circuit'[i]<|g'|
// {
//     forall i | 0<=i<|circuit'|
//     {
//         circuit_equivalent_aux1_local_lemma(g, g', circuit, circuit', i);
//     }
// }

// lemma circuit_equivalent_aux1_local_lemma(g: Graph, g': Graph, circuit: seq<nat>, circuit': seq<nat>, i: int)
//     requires validGraph(g)
//     requires |g|>2
//     requires isDirectedHamiltonianCircuit(g, circuit)
//     requires g' == directed_to_undirected_graph(g)
//     requires circuit_equivalent(g, g', circuit, circuit')
//     requires 0<=i<|circuit'|
//     ensures circuit'[i]<|g'|
// {
//     assert circuit'[i*3]==circuit[i]+|g|*2;
//     assert circuit'[i*3+1]==circuit[i];
//     assert circuit'[i*3+2]==circuit[i]+|g|;
// }

// lemma circuit_equivalent_lemma(g: Graph, g': Graph, circuit: seq<nat>, circuit': seq<nat>)
//     requires validGraph(g)
//     requires |g|>2
//     requires isDirectedHamiltonianCircuit(g, circuit)
//     requires g' == directed_to_undirected_graph(g)
//     requires circuit_equivalent(g, g', circuit, circuit')
//     ensures isUndirectedHamiltonianCircuit(g', circuit')
// {
//     if !isUndirectedHamiltonianCircuit(g', circuit')
//     {
//         reveal circuit_equivalent(g, g', circuit, circuit');
//         directedHamiltonianCircuitProperty_lemma(g, circuit);
//         assert forall i :: 0<i<|g| ==> g[circuit[i-1]][circuit[i]]; //property_lemma definition
//         assert forall i :: 0<=i<|g| ==> circuit'[i*3+1]==circuit[i] && circuit'[i*3]==circuit[i]+|g|*2 && circuit'[i*3+2]==circuit[i]+|g|;  //equivalence property
//         assert forall i :: 0<=i<|g| ==> 0<=circuit[i]<|g|;
//         assert forall i :: 0<=i<|g| ==> g'[circuit'[i*3+1]][circuit'[i*3]];
//     }
// }

//returns the directed circuit's undirected equivalence
ghost function circuit_equivalence(g: Graph, g': Graph, circuit: seq<nat>): seq<nat>
    requires validGraph(g)
    requires |g|>2
    requires isDirectedHamiltonianCircuit(g, circuit)
    requires g' == directed_to_undirected_graph(g)
    ensures isUndirectedHamiltonianCircuit(g', circuit_equivalence(g, g', circuit))
{
    circuit_equivalence_connectivity_lemma(g, g', circuit, |g|-1);
    circuit_equivalence_(g, g', circuit, |g|-1)
}

ghost function circuit_equivalence_(g: Graph, g': Graph, circuit: seq<nat>, i: int): seq<nat>
    requires validGraph(g)
    requires |g|>2
    requires isDirectedHamiltonianCircuit(g, circuit)
    requires g' == directed_to_undirected_graph(g)
    requires -1<=i<|circuit|
    //size relation
    ensures |circuit_equivalence_(g, g', circuit, i)| == (i+1)*3
    //central, in and out nodes position relation
    ensures forall j :: 0<=j<= i ==> 
    (
        circuit_equivalence_(g, g', circuit, i)[3*j] == circuit[j]+|g|*2
        &&
        circuit_equivalence_(g, g', circuit, i)[3*j+1] == circuit[j]
        &&
        circuit_equivalence_(g, g', circuit, i)[3*j+2] == circuit[j]+|g|
    )
    ensures forall j :: 0<=j<|circuit_equivalence_(g, g', circuit, i)| ==>
    (
        j % 3 == 1 ==> (circuit_equivalence_(g, g', circuit, i)[j] == circuit[(j-1)/3]) //reverse relation
    )
    //nodes boundaries
    ensures forall j :: 0<j<|circuit_equivalence_(g, g', circuit, i)| ==> circuit_equivalence_(g, g', circuit, i)[j]<|g'|
    //connectivity
    // ensures var circuit' := circuit_equivalence_(g, g', circuit, i);
        // forall j :: 0<j<|circuit'| ==> g'[circuit'[j-1]][circuit'[j]]
{
    if i==-1 then [] else
        var circuit' := circuit_equivalence_(g, g', circuit, i-1);
        circuit' + [circuit[i]+|g|*2] + [circuit[i]] + [circuit[i]+|g|]
}

lemma circuit_equivalence_connectivity_lemma(g: Graph, g': Graph, circuit: seq<nat>, i: int)
    requires validGraph(g)
    requires |g|>2
    requires isDirectedHamiltonianCircuit(g, circuit)
    requires g' == directed_to_undirected_graph(g)
    requires 0<=i<|circuit|
    ensures var circuit' := circuit_equivalence_(g, g', circuit, i);
        (forall j :: 0<j<|circuit'| ==> g'[circuit'[j-1]][circuit'[j]]) && g'[circuit'[|circuit'|-1]][circuit'[0]]
{
    var circuit' := circuit_equivalence_(g, g', circuit, i);
    forall j | 0<j<|circuit'|
    {
        circuit_equivalence_connectivity_local_lemma(g, g', circuit, i, circuit', j);
    }
}

lemma circuit_equivalence_connectivity_local_lemma(g: Graph, g': Graph, circuit: seq<nat>, i: int, circuit': seq<nat>, j: int)
    requires validGraph(g)
    requires |g|>2
    requires isDirectedHamiltonianCircuit(g, circuit)
    requires g' == directed_to_undirected_graph(g)
    requires 0<=i<|circuit|
    requires circuit' == circuit_equivalence_(g, g', circuit, i)
    requires 0<j<|circuit'|
    ensures g'[circuit'[j-1]][circuit'[j]]
{
    
}

// Reduction to the left: undirectedHamiltonian(f(g)) ==> directedHamiltonian(g)

lemma reduction_lemma_left(g: Graph) //TODO
    requires validGraph(g)
    requires undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
    ensures directedHamiltonianCircuit(g)
// {}


// ghost function directedHamiltonianCircuit_witness(g: Graph): seq<nat>
//     requires validGraph(g)
//     requires directedHamiltonianCircuit(g)
//     ensures isDirectedHamiltonianCircuit(g, (directedHamiltonianCircuit_witness(g)))

// ghost function undirectedHamiltonianCircuit_witness(g: Graph): seq<nat>
//     requires validUndirectedGraph(g)
//     requires undirectedHamiltonianCircuit(g)
//     ensures isUndirectedHamiltonianCircuit(g, (undirectedHamiltonianCircuit_witness(g)))