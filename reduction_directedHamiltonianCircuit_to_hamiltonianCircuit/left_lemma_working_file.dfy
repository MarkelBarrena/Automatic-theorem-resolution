include "reduction_hamiltonian_definitions.dfy"
include "reduction_hamiltonian_rFunction.dfy"
include "permutation_property.dfy"
include "reduction_hamiltonian_rCompletness.dfy"

module LeftLemma
{
    import opened Definitions
    import opened ReductionFunction
    import opened PermutationProperty
    import opened ReductionCompletness

    lemma reduction_lemma_left(g: Graph)
        requires validGraph(g)
        requires undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
        ensures directedHamiltonianCircuit(g)
    {

    }

    function rSeq(s: seq<int>): seq<int>
    {
        if |s| == 0 then
            []
        else
            rSeq(s[1..]) + [s[0]]
    }

    lemma circuit_reverse_property_lemma(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2
        requires isUndirectedHamiltonianCircuit(g, c)
        ensures isUndirectedHamiltonianCircuit(g, c)
    {}

    ghost function cicle_sequence(s: seq<nat>, i: int): seq<nat>
        requires 0<=i<|s|
    {
        s[i..|s|] + s[0..i]
    }

    lemma circuit_circular_property_lemma(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2
        requires isUndirectedHamiltonianCircuit(g, c)
        ensures forall i :: 0<=i<|c| ==> isUndirectedHamiltonianCircuit(g, cicle_sequence(c, i))
    {}

    // ghost predicate in_out_circuit(g: Graph, c: seq<nat>)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires in_out_graph(g)
    //     // requires isUndirectedHamiltonianCircuit(g, uc)
    // {
    //     isUndirectedHamiltonianCircuit(g, c)
    //     &&
    //     (
    //         (forall i :: 0<i<|c|-1 ==> way1(g, c, i))
    //         ||
    //         (forall i :: 0<i<|c|-1 ==> way2(g, c, i))
    //     )
    // }

    // //circuit has structure in->og->out
    // ghost predicate way1(g: Graph, c: seq<nat>, i: int)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires in_out_graph(g)
    //     requires 0<i<|c|-1
    // {
    //     (0<=c[i]<|g|/3 ==>  //case og node
    //     (
    //         c[i-1]==c[i]+(|g|/3)*2  //before: in
    //         &&
    //         c[i+1]==c[i]+|g|/3    //next: out
    //     ))
    //     &&
    //     (|g|/3<=c[i]<(|g|/3)*2 ==>  //case out node
    //     (
    //         c[i-1]==c[i]-|g|/3   //before: og
    //         &&
    //         (|g|/3)*2<=c[i+1]<|g|   //next: in (range)
    //     ))
    //     &&
    //     ((|g|/3)*2<=c[i]<|g| ==>  //case in node
    //     (
    //         |g|/3<=c[i-1]<(|g|/3)*2   //before: out (range)
    //         &&
    //         c[i+1]==c[i]-(|g|/3)*2    //next: og
    //     ))
    // }

    // //circuit has structure out->og->in
    // ghost predicate way2(g: Graph, c: seq<nat>, i: int)
    // requires validUndirectedGraph(g)
    // requires |g|>2 && |g|%3==0
    // requires in_out_graph(g)
    // requires 0<i<|c|-1
    // {
    //     (0<=c[i]<|g|/3 ==>  //case og node
    //     (
    //         c[i-1]==c[i]+|g|/3    //before: out
    //         &&
    //         c[i+1]==c[i]+(|g|/3)*2  //next: in
    //     ))
    //     &&
    //     (|g|/3<=c[i]<(|g|/3)*2 ==>  //case out node
    //     (
    //         (|g|/3)*2<=c[i-1]<|g|   //before: in (range)
    //         &&
    //         c[i+1]==c[i]-|g|/3   //next: og
    //     ))
    //     &&
    //     ((|g|/3)*2<=c[i]<|g| ==>  //case in node
    //     (
    //         c[i-1]==c[i]-(|g|/3)*2    //before: og
    //         &&
    //         |g|/3<=c[i+1]<(|g|/3)*2   //next: out (range)
    //     ))
    // }

    // lemma in_out_circuit_lemma(g: Graph, c: seq<nat>)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires isUndirectedHamiltonianCircuit(g, c)
    //     requires in_out_graph(g)
    //     ensures in_out_circuit(g, c)
    // {
    //     assert (forall i :: 0<i<|c|-1 ==> way2(g, c, i)) ==> (forall i :: 0<i<|c|-1 ==> way1(g, rSeq(c), i));
    //     forall i | 0<i<|c|-1
    //     {
    //         in_out_circuit_local_lemma(g, c, i);
    //     }
    // }

    // lemma in_out_circuit_local_lemma(g: Graph, c: seq<nat>, i: int)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires isUndirectedHamiltonianCircuit(g, c)
    //     requires in_out_graph(g)
    //     requires 0<i<|c|-1
    //     ensures way1(g, c, i)
    // {
    //     if 0<=c[i]<|g|/3
    //     {
    //         in_out_circuit_1_lemma(g, c, i);
    //         // assume c[i-1]==c[i]+(|g|/3)*2 && c[i+1]==c[i]+|g|/3;
    //     }
    //     if |g|/3<=c[i]<(|g|/3)*2
    //     {
    //         in_out_circuit_2_lemma(g, c, i);
    //         // assume c[i-1]==c[i]-|g|/3 && (|g|/3)*2<=c[i+1]<|g|;
    //     }
    //     if (|g|/3)*2<=c[i]<|g|
    //     {
    //         in_out_circuit_3_lemma(g, c, i);
    //         // assume |g|/3<=c[i-1]<(|g|/3)*2 && c[i+1]==c[i]-(|g|/3)*2;
    //     }
    // }


    // lemma in_out_circuit_1_lemma(g: Graph, c: seq<nat>, i: int)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires isUndirectedHamiltonianCircuit(g, c)
    //     requires in_out_graph(g)
    //     requires 0<i<|c|-1
    //     requires 0<=c[i]<|g|/3
    //     ensures c[i-1]==c[i]+(|g|/3)*2 || c[i+1]==c[i]+(|g|/3)*2
    // {}
    
    // lemma in_out_circuit_2_lemma(g: Graph, c: seq<nat>, i: int)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires isUndirectedHamiltonianCircuit(g, c)
    //     requires in_out_graph(g)
    //     requires 0<i<|c|-1
    //     requires |g|/3<=c[i]<(|g|/3)*2
    //     ensures c[i-1]==c[i]-|g|/3 && (|g|/3)*2<=c[i+1]<|g|
    // {}

    // lemma in_out_circuit_3_lemma(g: Graph, c: seq<nat>, i: int)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires isUndirectedHamiltonianCircuit(g, c)
    //     requires in_out_graph(g)
    //     requires 0<i<|c|-1
    //     requires (|g|/3)*2<=c[i]<|g|
    //     ensures |g|/3<=c[i-1]<(|g|/3)*2 && c[i+1]==c[i]-(|g|/3)*2 
    // {}

    // ghost function in_out_to_directed(g: Graph): Graph
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires isUndirectedHamiltonianCircuit(g, c)
    //     requires in_out_graph(g)
    // {
    //     in_out_to_directed_(g, 0)
    // }

    // ghost function in_out_to_directed_(g: Graph): Graph
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires isUndirectedHamiltonianCircuit(g, c)
    //     requires in_out_graph(g)




    // //starts with in_node -> og_node -> out_node ...and so on...
    // ghost predicate in_out_circuit_std(g: Graph, uc: seq<nat>)
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires in_out_graph(g)
    //     // requires isUndirectedHamiltonianCircuit(g, uc)
    //     ensures in_out_circuit_std(g, uc) ==> in_out_circuit(g, uc)
    // {
    //     isUndirectedHamiltonianCircuit(g, uc)
    //     &&
    //     forall i :: 0<=i<|uc| && i%3==1 ==>
    //     (
    //         0<=uc[i]<|g|/3  //this: og_node
    //         &&
    //         uc[i-1]==uc[i]+(|g|/3)*2    //prev: *in_node
    //         &&
    //         uc[i+1]==uc[i]+|g|/3    //next: *out_node
    //     )
    // }

    // ghost function standarize_in_out_circuit(g: Graph, uc: seq<nat>): seq<nat>
    //     requires validUndirectedGraph(g)
    //     requires |g|>2 && |g|%3==0
    //     requires in_out_graph(g)
    //     requires in_out_circuit(g, uc)
    //     // ensures in_out_circuit_std(g, standarize_in_out_circuit(g, uc))
    // {
    //     if |g|/3<=uc[0]<(|g|/3)*2 then cicle_sequence(uc, 0)    //0: out -> put [0] at the end
    //     else if 0<=uc[0]<|g|/3 then cicle_sequence(uc, 1)   //0: og -> put [0,1] at the end
    //     else uc //0: in -> already std
    // }

    // lemma lem(g: Graph, g': Graph)
    //     requires validGraph(g)
    //     requires |g|>0
    //     requires g' == directed_to_undirected_graph(g)
    //     requires directedHamiltonianCircuit(reverse_rFunction(g'))
    //     ensures directedHamiltonianCircuit(g)
    // {}

    lemma lem(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires undirectedHamiltonianCircuit(g)
        ensures directedHamiltonianCircuit(reverse_rFunction(g))
    {
        var g' := reverse_rFunction(g);

        assert |g'|>0;
        var uhc :| isUndirectedHamiltonianCircuit(g, uhc);

        var dhc_eq := circuit_reverse_equivalence(g, g', uhc);
        
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
        circuit_reverse_equivalence_(g, g', circuit, |g'|-1)
    }

    ghost function circuit_reverse_equivalence_(g: Graph, g': Graph, c: seq<nat>, i: int): seq<nat>
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        requires g' == reverse_rFunction(g)
        requires -1<=i<|c|
        decreases i
        ensures |circuit_reverse_equivalence_(g, g', c, i)| == (i+1)/3
    {
        if i==-1 then [] else
            var c' := circuit_reverse_equivalence_(g, g', c, i-1);
            if 0<c[i]<|g'| then c'+[c[i]] else c'
    }

    lemma in_out_circuit_property_lemma(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        requires (|g|/3)*2<=c[0]<|g| && 0<=c[1]<|g|/3
    {
        assert |c|%3==0;
        var triplets := partition_into_triplets(c);
        assert forall t :: t in triplets ==> ((|g|/3)*2<=t[0]<|g| && 0<=t[1]<|g|/3 && |g|/3<=t[2]<(|g|/3*2));
    }

    ghost function partition_into_triplets(s: seq<nat>): seq<seq<nat>>
        requires |s|%3==0
        ensures |partition_into_triplets(s)| == |s| / 3
        ensures forall i :: 0 <= i < |partition_into_triplets(s)| ==> |partition_into_triplets(s)[i]| == 3
        ensures s == boom(partition_into_triplets(s))
    {
        if |s| == 0 then [] else
            [s[0..3]] + partition_into_triplets(s[3..])
    }

    function boom(seqs: seq<seq<nat>>): seq<nat>
        decreases seqs
    {
        if |seqs| == 0 then [] else seqs[0] + boom(seqs[1..])
    }

}