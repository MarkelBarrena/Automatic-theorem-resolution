
type Graph = (int, set<(int, int)>)


//clique
ghost predicate clique(G: Graph, k: nat)
{
    exists N: set<int> :: (forall u :: u in N ==> 0<u<=G.0) && ((forall u, v :: (u in N && v in N) ==> (u, v) in G.1) && |N|==k)
}

//independentSet
ghost predicate independentSet(G: Graph, k: nat)
{
    exists N: set<int> :: (forall u :: u in N ==> 0<u<=G.0) && ((forall u, v :: (u in N && v in N) ==> !((u, v) in G.1)) && |N|==k)
}

/**
Reduction clique->independentSet
 */

//reduction function
function inverse_graph(G: Graph): Graph
    // ensures forall n :: 0<n<=G.0 ==>
    //     (
    //         forall n' :: ((n, n') in G.1 || (n', n) in G.1) <==> !((n, n') in inverse_graph(G).1 || (n', n) in inverse_graph(G).1)
    //     )
{
    inverse_graph_recursive(G, 1)
}

function inverse_graph_recursive(G: Graph, n: int): Graph
    requires 0<n<=G.0
{
    if n>G.0 then G else
        inverse_graph_recursive(inverse_node(G, n, n), n+1)
}

function inverse_node(G: Graph, n: int, v: int): Graph
    requires 0<n<=G.0
    // ensures forall n' :: ((n, n') in G.1 || (n', n) in G.1) <==> !((n, n') in inverse_graph(G).1 || (n', n) in inverse_graph(G).1)
{
    if v > G.0 then G else
        if (n, v) in G.1 then
            inverse_node((G.0, G.1-{(n, v)}), n, v+1)
        else
            inverse_node((G.0, G.1+{(n, v)}), n, v+1)
}