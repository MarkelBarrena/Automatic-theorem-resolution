
/************************
INSTANCE TYPE DECLARATION
************************/
datatype Graph = G(V: set<nat>, E: set<(nat, nat)>)
// The nodes of the graph are natural numbers

/*************************
TYPE DEFINITION PREDICATES
*************************/

// The nodes of the edge are nodes of the graph and every edge (u, v) always satisfy u<v
ghost predicate validGraph(g: Graph)
{
    forall e :: e in g.E ==> (e.0 in g.V && e.1 in g.V) && e.0 < e.1
}

/******************
PROBLEM DEFINITIONS
*******************/

//// INDEPENDENT-SET ////
ghost predicate independentSet(g: Graph, k: nat)
    requires validGraph(g)
{
    exists ins: set<nat> :: |ins| == k && ins<=g.V &&
    (
        forall u, v :: u in g.V && v in g.V && u!=v ==> u in ins && v in ins ==> (u, v) !in g.E
    )
}

// True if 'ins' is an independent set of size 'k' in the graph 'g'
ghost predicate is_independentSet(g: Graph, k: nat, ins: set<nat>)
    requires validGraph(g)
    ensures is_independentSet(g, k, ins) ==> independentSet(g, k)
{
    |ins| == k && ins<=g.V && (forall u, v :: u in g.V && v in g.V && u!=v ==> u in ins && v in ins ==> (u, v) !in g.E)
}

//// VERTEX-COVER ////
ghost predicate vertexCover(g: Graph, k: nat)
    requires validGraph(g)
{
    exists vc: set<nat> :: |vc| == k && vc<=g.V &&
    (
        forall e :: e in g.E ==> (e.0 in vc || e.1 in vc)
    )
}

// True if 'vc' is a vertex cover of size 'k' in the graph 'g'
ghost predicate is_vertexCover(g: Graph, k: nat, vc: set<nat>)
    requires validGraph(g)
    ensures is_vertexCover(g, k, vc) ==> vertexCover(g, k)
{
    |vc| == k && vc<=g.V && (forall e :: e in g.E ==> (e.0 in vc || e.1 in vc))
}

/***************
REDUCTION: INDEPENDENT-SET <=p VERTEX-COVER
****************/

//(There is no explicit reduction funcion).

//// REDUCTION CORRECTNESS ////
lemma reduction_lemma(g: Graph, k: nat)
    requires validGraph(g)
    requires |g.V| >= k
    ensures independentSet(g, k) <==> vertexCover(g, |g.V|-k)
{
    if independentSet(g, k)
    {
        forward_lemma(g, k);
    }
    if vertexCover(g, |g.V|-k)
    {
        backward_lemma(g, k);
    }
}

//Forward reduction: IS(g) ==> VC(f(g))
lemma forward_lemma(g: Graph, k: nat)
    requires validGraph(g)
    requires |g.V| >= k
    requires independentSet(g, k)
    ensures vertexCover(g, |g.V|-k)
{
    var ins: set<nat> :| is_independentSet(g, k, ins);
    assert is_vertexCover(g, |g.V|-k, g.V-ins);
}

//Backward reduction: VC(f(g)) ==> IS(g)
lemma backward_lemma(g: Graph, k: nat)
    requires validGraph(g)
    requires |g.V| >= k
    requires vertexCover(g, |g.V|-k)
    ensures independentSet(g, k)
{
    var vc: set<nat> :| is_vertexCover(g, |g.V|-k, vc);
    var ins: set<nat> := g.V - vc;
    assert is_vertexCover(g, |g.V|-k, g.V-ins) ==> is_independentSet(g, k, ins);
}
