include "reduction_hamiltonian_definitions.dfy"
include "reduction_hamiltonian_rFunction.dfy"
include "permutation_property.dfy"
include "reduction_hamiltonian_rCorrectness.dfy"

module LeftLemma
{
    import opened Definitions
    import opened ReductionFunction
    import opened PermutationProperty
    import opened ReductionCorrectness

    lemma reduction_lemma_left(g: Graph)
        requires validGraph(g)
        requires undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
        ensures directedHamiltonianCircuit(g)
    {
        var g' := directed_to_undirected_graph(g);

        var g_rev := reverse_rFunction(g');
        reverse_function_firsStep_lemma(g', g_rev);
        reverse_function_secondStep_lemma(g, g_rev);
    }

    //hamilton f(g) ==> hamilton reverse(f(g))
    lemma reverse_function_firsStep_lemma(g: Graph, g': Graph)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires g' == reverse_rFunction(g)
        requires undirectedHamiltonianCircuit(g)
        ensures directedHamiltonianCircuit(g')
    {
        var g' := reverse_rFunction(g);

        assert |g'|>0;
        var uhc :| isUndirectedHamiltonianCircuit(g, uhc);

        var dhc_eq := circuit_reverse_equivalence(g, g', uhc);
        
    }

    //hamilton reverse(f(g)) ==> hamilton g
    lemma reverse_function_secondStep_lemma(g: Graph, g': Graph)
        requires validGraph(g)
        requires |g|>0
        requires g' == reverse_rFunction(directed_to_undirected_graph(g))
        requires directedHamiltonianCircuit(g')
        ensures directedHamiltonianCircuit(g)
    {
        var g_inter := directed_to_undirected_graph(g);
        assert g_inter == directed_to_undirected_graph(g);
        assert g' == reverse_rFunction(g_inter);

        assert |g|==|g'|;
        assert forall f :: 0<=f<|g| ==> (forall c :: 0<=c<|g| ==> (g[f][c] <==> g'[f][c]));
        reverse_function_secondStep_aux_lemma(g, g');
    }

    lemma reverse_function_secondStep_aux_lemma(g: Graph, g': Graph)
        requires validGraph(g) && validGraph(g')
        requires |g|==|g'|
        requires forall f :: 0<=f<|g| ==> (forall c :: 0<=c<|g| ==> (g[f][c] <==> g'[f][c]))
        requires directedHamiltonianCircuit(g')
        ensures directedHamiltonianCircuit(g)
    {
        var dhc :| isDirectedHamiltonianCircuit(g', dhc);
        assert forall i :: 0<i<|g| ==> g'[dhc[i-1]][dhc[i]] && g[dhc[i-1]][dhc[i]];
        assert forall i :: 0<i<|g| ==> g[dhc[i-1]][dhc[i]];
        assert g[dhc[|g|-1]][dhc[0]];
        assert isDirectedHamiltonianCircuit(g, dhc);
    }

    ghost function reverse_rFunction(g: Graph): Graph
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        //remove in and out nodes
        ensures |reverse_rFunction(g)| == |g|/3
        //squared matrix
        ensures validGraph(reverse_rFunction(g))
        //direction relation: n1->n2 only and only if n1_out->n2_in
        ensures forall f :: 0<=f<|g|/3 ==> (forall c :: 0<=c<|g|/3 ==> (g[f+|g|/3][c+(|g|/3)*2] <==> reverse_rFunction(g)[f][c]))
    {
        var g_aux := collapsed_graph(g);
        reverse_rFunction_(g, g_aux, |g_aux|-1)
    }

    ghost function collapsed_graph(g: Graph): Graph
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        ensures validGraph(collapsed_graph(g))
        ensures |collapsed_graph(g)|==|g|/3
        ensures unconnected_graph(collapsed_graph(g))
    {
        seq(|g|/3, i => seq(|g|/3, i => false))
    }

    ghost function reverse_rFunction_(g: Graph, g': Graph, i: int): Graph
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires validGraph(g')
        requires |g'|==|g|/3
        requires unconnected_graph(g')
        requires -1<=i<|g'|
        ensures validGraph(reverse_rFunction_(g, g', i))
        ensures |reverse_rFunction_(g, g', i)| == |g'|
        //every row yet to process stay the same
        ensures forall f :: i< f<|g'| ==> (g'[f] == reverse_rFunction_(g, g', i)[f])
        //modifying property: for every processed row: n to c in g' if and only if n_out to c_in in g
        ensures forall f :: 0<=f<=i ==>
        (
            forall c :: 0<=c<|g'| ==> (g[f+|g|/3][c+(|g|/3)*2] <==> reverse_rFunction_(g, g', i)[f][c])
        )
    {
        if i==-1 then g' else
            var g'' := reverse_rFunction_(g, g', i-1);
            process_out_node_connections(g, g'', i, |g'|-1)
    }

    //for n and for every other node i: if n_out->i_in ==> n->i
    ghost function process_out_node_connections(g: Graph, g': Graph, n: int, i: int): Graph
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires validGraph(g')
        requires |g'|==|g|/3
        requires 0<=n<|g'|
        requires -1<=i<|g'|
        //row set to false
        requires forall c :: 0<=c<|g'| ==> !g'[n][c]
        ensures validGraph(process_out_node_connections(g, g', n, i))
        ensures |process_out_node_connections(g, g', n, i)| == |g'|
        //only n's row is modified
        ensures forall f :: 0<=f<|g'| && f!=n ==> (g'[f] == process_out_node_connections(g, g', n, i)[f])
        //only n->x vertex are modified,
        // ensures forall c :: 0<=c<|g'| ==> (g'[n][c] == direction_equivalence_node_(g, g', n, i)[n][c])
        //inductive postconditions:
        //every column yet to process stays the same (set to false)
        ensures forall c :: i< c<|g'| ==> (g'[n][c] == process_out_node_connections(g, g', n, i)[n][c])
        //modifying property: n to i in g' if and only if n_out to i_in in g
        ensures forall c :: 0<=c<=i ==>
        (
            g[n+|g|/3][c+(|g|/3)*2] <==> process_out_node_connections(g, g', n, i)[n][c]
        )
    {
        if i==-1 then g' else
            var g'' := process_out_node_connections(g, g', n, i-1);
            if g[n+|g|/3][i+(|g|/3)*2] then
                var f_aux1 := g''[n];
                var f_aux2 := f_aux1[..i]+[true]+f_aux1[i+1..];
                var gF := g''[n := f_aux2];
                gF
            else
                g''
    }


    ghost function circuit_reverse_equivalence(g: Graph, g': Graph, circuit: seq<nat>): seq<nat>
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, circuit)
        requires g' == reverse_rFunction(g)
        ensures isDirectedHamiltonianCircuit(g', circuit_reverse_equivalence(g, g', circuit))
    {
        var std_circuit := standarize_in_out_circuit(g, circuit);
        var cTriplets := triplets(std_circuit);
        var cre := circuit_reverse_equivalence_(g, g', std_circuit, cTriplets, |g'|-1);
        assert cre == circuit_reverse_equivalence_(g, g', std_circuit, cTriplets, |g'|-1);
        
        triplets_property3_lemma(g, g', std_circuit, cTriplets);
        assert g'[cTriplets[|cTriplets|-1][1]][cTriplets[0][1]];

        circuit_reverse_equivalence_post_lemma(g, g', std_circuit, cTriplets, |g'|-1);
        // assume UniqueElements(cre); //TODO
        cre
    }

    ghost function circuit_reverse_equivalence_(g: Graph, g': Graph, c: seq<nat>, cT: seq<seq<nat>>, i: int): seq<nat>
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        requires g' == reverse_rFunction(g)
        requires -1<=i<|cT|
        requires standarized_in_out_circuit(g, c)
        requires cT == triplets(c)
        decreases i
        ensures |circuit_reverse_equivalence_(g, g', c, cT, i)| == i+1
        ensures forall j :: 0<=j<= i ==> circuit_reverse_equivalence_(g, g', c, cT, i)[j] == cT[j][1]
        ensures forall j :: 0<=j<= i ==> isOgNode(g, circuit_reverse_equivalence_(g, g', c, cT, i)[j])
        ensures var c' := circuit_reverse_equivalence_(g, g', c, cT, i);
            (forall j :: 0<j<= i ==> g'[c'[j-1]][c'[j]])
        // ensures UniqueElements(circuit_reverse_equivalence_(g, g', c, cT, i))
    {
        triplets_property1_lemma(g, c, cT);
        triplets_property2_lemma(g, g', c, cT);
        if i==-1 then [] else
            var c' := circuit_reverse_equivalence_(g, g', c, cT, i-1);
            c'+[cT[i][1]]
    }

    lemma circuit_reverse_equivalence_post_lemma(g: Graph, g': Graph, c: seq<nat>, cT: seq<seq<nat>>, i: int)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        requires g' == reverse_rFunction(g)
        requires -1<=i<|cT|
        requires standarized_in_out_circuit(g, c)
        requires cT == triplets(c)
        ensures UniqueElements(circuit_reverse_equivalence_(g, g', c, cT, i))
    {
        var c' := circuit_reverse_equivalence_(g, g', c, cT, i);
        if !UniqueElements(c')
        {
            assert exists i, j :: 0<=i< j<|c'| && c'[i]==c'[j];
            assert exists i, j :: 0<=i< j<|c'| && cT[i][1]==cT[j][1];
            var i, j :| 0<=i< j<|c'| && cT[i][1]==cT[j][1];
            var exploded_cT := boom(cT);
            assert cT[i][1] == exploded_cT[i*3+1];
            assert cT[j][1] == exploded_cT[j*3+1];
            assert !UniqueElements(exploded_cT);
            assert !UniqueElements(c);
            // assert exists i, j :: 0<=i< j<|c'| && exploded_cT[i]==exploded_cT[j];
            // assume !isUndirectedHamiltonianCircuit(g, c);
        }
    }


    //triplets have [in, og, out] structure
    //out and in nodes are connected: out]->[in
    lemma triplets_property1_lemma(g: Graph, p: seq<nat>, pT: seq<seq<nat>>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires forall i :: 0<=i<|p| ==> 0<=p[i]<|g|
        requires UniqueElements(p)
        requires 0<|p|<=|g|
        requires |p|%3==0
        requires isOneWayPath(g, p)
        requires pT == triplets(p)
        requires isInNode(g, p[0])
        decreases |pT|
        ensures forall t :: t in pT ==> (isInNode(g, t[0]) && isOgNode(g, t[1]) && isOutNode(g, t[2]))
        ensures forall t :: t in pT ==> (t[0]==t[1]+(|g|/3)*2 && t[2]==t[1]+|g|/3)
        ensures forall i :: 0<i<|pT| ==> g[pT[i-1][2]][pT[i][0]]
    {
        if |pT|==1
        {
            assert |p|==3 && |pT[0]|==3;
            assert isInNode(g, pT[0][0]);
            assert isOgNode(g, pT[0][1]);
            assert pT[0][0]==pT[0][1]+(|g|/3)*2;
            assert pT[0][2]==pT[0][1]+|g|/3;
        }
        else
        {
            assert p == [p[0]] + p[1..];
            assert pT == [pT[0]] + pT[1..];

            assert isInNode(g, p[0]);
            assert isOgNode(g, p[1]);
            assert isOutNode(g, p[2]);
            triplets_property1_lemma(g, p[3..], pT[1..]);
        }
    }

    //if out]->[in then og -> og
    //ergo og->og
    lemma triplets_property2_lemma(g: Graph, g': Graph, p: seq<nat>, pT: seq<seq<nat>>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires forall i :: 0<=i<|p| ==> 0<=p[i]<|g|
        requires UniqueElements(p)
        requires 0<|p|<=|g|
        requires |p|%3==0
        requires isOneWayPath(g, p)
        requires pT == triplets(p)
        requires isInNode(g, p[0])
        requires g' == reverse_rFunction(g)
        requires forall i :: 0<i<|pT| ==> (isInNode(g, pT[i][0]) && isOgNode(g, pT[i][1]) && isOutNode(g, pT[i][2])) //property1
        requires forall i :: 0<i<|pT| ==> (pT[i][0]==pT[i][1]+(|g|/3)*2 && pT[i][2]==pT[i][1]+|g|/3) //property1
        requires forall i :: 0<i<|pT| ==> g[pT[i-1][2]][pT[i][0]] //property1
        decreases |pT|
        ensures forall i :: 0<i<|pT| ==> (g[pT[i-1][2]][pT[i][0]] <==> g'[pT[i-1][1]][pT[i][1]])
        ensures forall i :: 0<i<|pT| ==> g'[pT[i-1][1]][pT[i][1]]
    {
        // assert forall f :: 0<=f<|g|/3 ==> (forall c :: 0<=c<|g|/3 ==> (g[f+|g|/3][c+(|g|/3)*2] <==> g'[f][c]));
        forall i | 0<i<|pT|
            ensures g[pT[i-1][2]][pT[i][0]] <==> g'[pT[i-1][1]][pT[i][1]]
            ensures g'[pT[i-1][1]][pT[i][1]] || g'[pT[i][1]][pT[i-1][1]]
        {
            var out0, in1, og0, og1 := pT[i-1][2], pT[i][0], pT[i-1][1], pT[i][1];
            assert g[out0][in1];
            assert out0 == og0 + |g|/3;
            assert in1 == og1 + (|g|/3)*2;
            assert g'[og0][og1] by {assert forall f :: 0<=f<|g|/3 ==> (forall c :: 0<=c<|g|/3 ==> (g[f+|g|/3][c+(|g|/3)*2] <==> g'[f][c]));}
        }
    }

    //if p is a circuit then og_final -> og_initial
    lemma triplets_property3_lemma(g: Graph, g': Graph, c: seq<nat>, cT: seq<seq<nat>>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        requires g' == reverse_rFunction(g)
        requires standarized_in_out_circuit(g, c)
        requires cT == triplets(c)
        requires 0<=cT[|cT|-1][1]<|g'| && 0<=cT[0][1]<|g'|
        ensures g'[cT[|cT|-1][1]][cT[0][1]]
    {
        triplets_property1_lemma(g, c, cT);
        var outF, inI, ogF, ogI := cT[|cT|-1][2], cT[0][0], cT[|cT|-1][1], cT[0][1];
        assert g[outF][inI] ==> g'[ogF][ogI] by {triplets_property3_aux2_lemma(g, g', outF, inI, ogF, ogI);}
        assert g[outF][inI] by
        {
            triplets_property3_aux1_lemma(c, cT);
            assert outF == c[|c|-1];
            assert inI == c[0];
        }
        assert g'[ogF][ogI];
        assert ogF==cT[|cT|-1][1];
        assert ogI==cT[0][1];
        assert g'[cT[|cT|-1][1]][cT[0][1]];
    }

    lemma triplets_property3_aux1_lemma(s: seq<nat>, sT: seq<seq<nat>>)
        requires |s|>0 && |s|%3==0
        requires sT==triplets(s)
        ensures sT[|sT|-1][2]==s[|s|-1]
    {
        if |s|>3
        {
            triplets_property3_aux1_lemma(s[3..], sT[1..]);
        }
    }

    lemma triplets_property3_aux2_lemma(g: Graph, g': Graph, outF: nat, inI: nat, ogF: nat, ogI: nat)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires g' == reverse_rFunction(g)
        requires 0<=ogF<|g|/3
        requires 0<=ogI<|g|/3
        requires outF == ogF + |g|/3
        requires inI == ogI + (|g|/3)*2
        ensures g[outF][inI]==>g'[ogF][ogI]
    {
        assert forall f :: 0<=f<|g|/3 ==> (forall c :: 0<=c<|g|/3 ==> (g[f+|g|/3][c+(|g|/3)*2] <==> g'[f][c]));
    }

    ghost function triplets(s: seq<nat>): seq<seq<nat>>
        requires |s|%3==0
        ensures |triplets(s)| == |s| / 3
        ensures forall i :: 0 <= i < |triplets(s)| ==> |triplets(s)[i]| == 3
        ensures s == boom(triplets(s))
        //postcondition for equivalence_post_lemma
        ensures forall i :: 0<= i <|triplets(s)| ==> triplets(s)[i][1] == s[i*3+1]
    {
        if |s| == 0 then [] else
            [s[0..3]] + triplets(s[3..])
    }

    function boom(seqs: seq<seq<nat>>): seq<nat>
        decreases seqs
    {
        if |seqs| == 0 then [] else seqs[0] + boom(seqs[1..])
    }

    ghost predicate standarized_in_out_circuit(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
    {
        oneWay(g, c) && isInNode(g, c[0])
    }

    ghost predicate isOneWayPath(g: Graph, p: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires forall i :: 0<=i<|p| ==> 0<=p[i]<|g|
        requires UniqueElements(p)
        requires 0<|p|<=|g|
        requires |p|%3==0
    {
        (forall i :: 0<i<|p| ==> (g[p[i-1]][p[i]]) || (g[p[i]][p[i-1]])) &&
        (forall i :: 0<=i<|p|-1 ==>
        (
            (isInNode(g, p[i]) ==> isOgNode(g, p[i+1]))   //if this in next og
            &&
            (isOgNode(g, p[i]) ==> isOutNode(g, p[i+1]))   //if this og next out
            &&
            (isOutNode(g, p[i]) ==> isInNode(g, p[i+1]))   //if this out next in
        ))
    }

    lemma lema(g: Graph, c: seq<nat>)   //
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        requires standarized_in_out_circuit(g, c)
        ensures isOneWayPath(g, c)
    {}

    //in->og->out
    ghost predicate oneWay(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
    {
        (forall i :: 0<i<|c| ==> (g[c[i-1]][c[i]]) || (g[c[i]][c[i-1]])) &&
        (forall i :: 0<=i<|g|-1 ==>
        (
            (isInNode(g, c[i]) ==> isOgNode(g, c[i+1]))   //if this in next og
            &&
            (isOgNode(g, c[i]) ==> isOutNode(g, c[i+1]))   //if this og next out
            &&
            (isOutNode(g, c[i]) ==> isInNode(g, c[i+1]))   //if this out next in
        ))
    }

    //out->og->in
    ghost predicate otherWay(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
    {
        (forall i :: 0<i<|c| ==> (g[c[i-1]][c[i]]) || (g[c[i]][c[i-1]])) &&
        (forall i :: 0<=i<|g|-1 ==>
        (
            (isOutNode(g, c[i]) ==> isOgNode(g, c[i+1]))   //if this out next og
            &&
            (isOgNode(g, c[i]) ==> isInNode(g, c[i+1]))   //if this og next in
            &&
            (isInNode(g, c[i]) ==> isOutNode(g, c[i+1]))   //if this in next out
        ))
    }

    ghost predicate isInNode(g: Graph, n: nat)
        requires |g|>2 && |g|%3==0
    {
        (|g|/3)*2<=n<|g|
    }

    ghost predicate isOgNode(g: Graph, n: nat)
        requires |g|>2 && |g|%3==0
    {
        0<=n<|g|/3
    }

    ghost predicate isOutNode(g: Graph, n: nat)
        requires |g|>2 && |g|%3==0
    {
        |g|/3<=n<(|g|/3)*2
    }

    ghost function standarize_in_out_circuit(g: Graph, c: seq<nat>): seq<nat>
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        ensures isUndirectedHamiltonianCircuit(g, standarize_in_out_circuit(g, c))
        ensures standarized_in_out_circuit(g, standarize_in_out_circuit(g, c))
    //TODO

}