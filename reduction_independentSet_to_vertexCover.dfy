datatype Graph = G(V: set<nat>, E: set<(nat, nat)>)
// The nodes of the graph are natural numbers

// The nodes of the edge are nodes of the graph and every edge (u, v) always satisfy u<v
ghost predicate validGraph(g: Graph)
{
    forall e :: e in g.E ==> (e.0 in g.V && e.1 in g.V) && e.0 < e.1
}

// This predicate is the decision problem known as the Independent-Set problem
ghost predicate independentSet(g: Graph, k: nat)
    requires validGraph(g)
{
    exists ins: set<nat> :: |ins| == k && ins<=g.V &&
    (
        forall u, v :: u in g.V && v in g.V && u!=v ==> u in ins && v in ins ==> (u, v) !in g.E
    )
}

// This predicate is true if 'ins' is an independent set of size 'k' in the graph 'g'
ghost predicate is_independentSet(g: Graph, k: nat, ins: set<nat>)
    requires validGraph(g)
    ensures is_independentSet(g, k, ins) ==> independentSet(g, k)
{
    |ins| == k && ins<=g.V && (forall u, v :: u in g.V && v in g.V && u!=v ==> u in ins && v in ins ==> (u, v) !in g.E)
}

// This predicate is the decision problem known as the Vertex-Cover problem
ghost predicate vertexCover(g: Graph, k: nat)
    requires validGraph(g)
{
    exists vc: set<nat> :: |vc| == k && vc<=g.V &&
    (
        forall e :: e in g.E ==> (e.0 in vc || e.1 in vc)
    )
}

// This predicate is true if 'vc' is a vertex cover of size 'k' in the graph 'g'
ghost predicate is_vertexCover(g: Graph, k: nat, vc: set<nat>)
    requires validGraph(g)
    ensures is_vertexCover(g, k, vc) ==> vertexCover(g, k)
{
    |vc| == k && vc<=g.V && (forall e :: e in g.E ==> (e.0 in vc || e.1 in vc))
}

/**
The reduction: independentSet <=p vertexCover
 */

// Reduction correctness
lemma independentSet_to_vertexCover_Lemma(g: Graph, k: nat)
    requires validGraph(g)
    requires |g.V| >= k //
    ensures independentSet(g, k) <==> vertexCover(g, |g.V|-k)
{
    if independentSet(g, k)
    {
        var ins: set<nat> :| is_independentSet(g, k, ins);
        independentSet_to_vertexCover_sub_Lemma(g, k, ins);
    }
    if vertexCover(g, |g.V|-k)
    {
        var ins: set<nat> :| is_vertexCover(g, |g.V|-k, g.V-ins);
    }
}

lemma independentSet_to_vertexCover_sub_Lemma(g: Graph, k: nat, ins: set<nat>)
    requires validGraph(g)
    requires |g.V| >= k //sino dafny se queja en la llamada del ensures
    requires ins <= g.V //hasta qué punto es trampa?
    ensures is_independentSet(g, k, ins) <==> is_vertexCover(g, |g.V|-k, g.V-ins)
{}
