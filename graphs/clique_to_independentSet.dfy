
type Graph = (int, set<(int, int)>)
//Nota: se asume que los pares de nodos son de menor a mayor
ghost predicate validGraph(G: Graph)
    ensures forall n :: 0<n<=G.0 ==> !(exists n' :: n< n'<=n && (n, n') in G.1)
{
    forall u, v :: (u, v) in G.1 ==> u< v
}

//clique
ghost predicate clique(G: Graph, k: nat)
{
    exists N: set<int> :: (forall u, v :: (u in N && v in N) ==> (u, v) in G.1) && |N|==k
}

//independentSet
ghost predicate independentSet(G: Graph, k: nat)
{
    exists N: set<int> :: (forall u, v :: (u in N && v in N) ==> !((u, v) in G.1)) && |N|==k
}

/**
Reduction clique->independentSet
 */

//reduction function
function inverse_graph(G: Graph): Graph
    requires validGraph(G)
    requires G.0>0
    ensures forall u, v :: 0<u< v<=G.0 ==> ((u, v) in G.1 <==> !((u, v) in inverse_graph(G).1))
{
    inverse_graph_recursive(G, G.0)
}

function inverse_graph_recursive(G: Graph, n: int): Graph
    requires validGraph(G)
    requires 0<=n<=G.0
    decreases n
    ensures validGraph(inverse_graph_recursive(G, n))
    ensures inverse_graph_recursive(G, n).0 == G.0
    ensures forall n', n'' :: n< n'< n''<=G.0 ==> ((n', n'') in G.1 <==> (n', n'') in inverse_graph_recursive(G, n).1)
    ensures n==0 || (forall n' :: n< n'<=G.0 ==> ((n, n') in G.1 <==> !((n, n') in inverse_graph_recursive(G, n).1)))

    ensures forall n' :: 0<n'<=n ==> (forall n'' :: n' <n''<=G.0 ==> ((n', n'') in G.1 <==> !((n', n'') in inverse_graph_recursive(G, n).1)))
    // ensures forall n' :: 0<n'<=n ==> (forall n'' :: 0<n''<=G.0 ==> ((n', n'') in G.1 <==> !((n', n'') in inverse_graph_recursive(G, n).1)))
{
    if n==0 then G else
        var rG := inverse_graph_recursive(G, n-1);
        assert forall n' :: 0<n'< n ==> (forall n'' :: n' <n''<=G.0 ==> ((n', n'') in G.1 <==> !((n', n'') in rG.1)));
        var nG := inverse_node(rG, n, G.0);
        assert forall n', n'' :: 0< n'< n''< n ==> ((n', n'') in rG.1 <==> (n', n'') in nG.1);
        assert (set e | e in rG.1 && 0<e.0<n) == (set e | e in nG.1 && 0<e.0<n);
        inverse_graph_recursive_aux_lemma(n, G, rG);
        assert forall n' :: 0<n'< n ==> (forall n'' :: n' <n''<=G.0 ==> ((n', n'') in G.1 <==> !((n', n'') in nG.1))); //lo pillé
        assert forall n' :: n< n'<=G.0 ==> ((n, n') in G.1 <==> !((n, n') in nG.1));

        nG
}

lemma inverse_graph_recursive_aux_lemma(n: int, G1: Graph, G2: Graph)   //TODO
    requires validGraph(G1) && validGraph(G2)
    requires G1.0 == G2.0
    requires 0<n<=G1.0
    //los nodos anteriores a n están invertidos de G1 a G2
    requires forall n' :: 0<n'< n ==> (forall n'' :: n' <n''<=G1.0 ==> ((n', n'') in G1.1 <==> !((n', n'') in G2.1)))
    //entonces: aún llamando a inverse_node con n, todos los nodos anteriores permanecerán invertidos respecto al grafo original
    ensures var G3 := inverse_node(G2, n, G1.0);
        forall n' :: 0<n'< n ==> (forall n'' :: n' <n''<=G1.0 ==> ((n', n'') in G1.1 <==> !((n', n'') in G3.1)))
{
    forall n' | 0<n'< n
    {
        inverse_graph_recursive_aux_local_lemma(n, n', G1, G2);
    }
}

lemma inverse_graph_recursive_aux_local_lemma(n: int, nL: int, G1: Graph, G2: Graph)   //TODO
    requires validGraph(G1) && validGraph(G2)
    requires G1.0 == G2.0
    requires 0<nL< n<=G1.0
    //el nodo nL está invertido
    requires forall n' :: nL <n'<=G1.0 ==> ((nL, n') in G1.1 <==> !((nL, n') in G2.1))
    //entonces: aún llamando a inverse_node con n, el nodo nL permanece invertido
    ensures var G3 := inverse_node(G2, n, G1.0);
        forall n' :: nL <n'<=G1.0 ==> ((nL, n') in G1.1 <==> !((nL, n') in G3.1))
{
    forall n' | nL< n'<=G1.0
    {
        inverse_graph_recursive_aux_local_local_lemma(n, nL, n', G1, G2);
    }
}

lemma inverse_graph_recursive_aux_local_local_lemma(n: int, nL: int, nLL: int, G1: Graph, G2: Graph)
    requires validGraph(G1) && validGraph(G2)
    requires G1.0 == G2.0
    requires 0<nL< n<= G1.0
    requires 0<nL< nLL<= G1.0
    //esta arista está invertida
    requires (nL, nLL) in G1.1 <==> !((nL, nLL) in G2.1)
    ensures var G3 := inverse_node(G2, n, G1.0);
        (nL, nLL) in G1.1 <==> !((nL, nLL) in G3.1)
{
    var G3 := inverse_node(G2, n, G1.0);
    assert forall n':: 0< n'< n ==> (forall n'' :: n'< n''<=G2.0 ==> ((n', n'') in G2.1 <==> (n', n'') in G3.1));
    assert 0<nL< n;
    assert nL< nLL<= G2.0;
    if (nL, nLL) in G2.1
    {
        assert (nL, nLL) in G3.1;
    }
    if !((nL, nLL) in G2.1)
    {
        assert !((nL, nLL) in G3.1);
    }
}

function inverse_node(G: Graph, n: int, v: int): Graph
    requires validGraph(G)
    requires 0<n<= v<=G.0
    decreases v-n
    ensures validGraph(inverse_node(G, n, v))
    ensures inverse_node(G, n, v).0 == G.0
    ensures v==n || ((n, v) in G.1 <==> !((n, v) in inverse_node(G, n, v).1))
    //persistencia de aristas para nodos antes y después de n
    ensures forall n', n'' :: n< n'< n''<=G.0 ==> ((n', n'') in G.1 <==> (n', n'') in inverse_node(G, n, v).1)
    ensures forall n', n'' :: 0< n'< n''< n ==> ((n', n'') in G.1 <==> (n', n'') in inverse_node(G, n, v).1)
    ensures forall n':: 0< n'< n ==> (forall n'' :: n'< n''<=G.0 ==> ((n', n'') in G.1 <==> (n', n'') in inverse_node(G, n, v).1))
    //dicho de otra manera...
    ensures (set e | e in G.1 && n <e.0<G.0) == (set e | e in inverse_node(G, n, v).1 && n <e.0<G.0)
    ensures (set e | e in G.1 && 0<e.0<n) == (set e | e in inverse_node(G, n, v).1 && 0<e.0<n)

    ensures forall n' :: n< n'<=v ==> ((n, n') in G.1 <==> !((n, n') in inverse_node(G, n, v).1))
{
    if v == n then G else
        var nG:= inverse_node(G, n, v-1);
        if (n, v) in G.1 then
            (nG.0, nG.1-{(n, v)})
        else
            (nG.0, nG.1+{(n, v)})
}