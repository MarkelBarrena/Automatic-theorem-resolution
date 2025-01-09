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

    ghost predicate in_out_circuit(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        // requires isUndirectedHamiltonianCircuit(g, uc)
    {
        isUndirectedHamiltonianCircuit(g, c)
        &&
        (
            (forall i :: 0<i<|c|-1 ==> way1(g, c, i))
            ||
            (forall i :: 0<i<|c|-1 ==> way2(g, c, i))
        )
    }

    //circuit has structure in->og->out
    ghost predicate way1(g: Graph, c: seq<nat>, i: int)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires 0<i<|c|-1
    {
        (0<=c[i]<|g|/3 ==>  //case og node
        (
            c[i-1]==c[i]+(|g|/3)*2  //before: in
            &&
            c[i+1]==c[i]+|g|/3    //next: out
        ))
        &&
        (|g|/3<=c[i]<(|g|/3)*2 ==>  //case out node
        (
            c[i-1]==c[i]-|g|/3   //before: og
            &&
            (|g|/3)*2<=c[i+1]<|g|   //next: in (range)
        ))
        &&
        ((|g|/3)*2<=c[i]<|g| ==>  //case in node
        (
            |g|/3<=c[i-1]<(|g|/3)*2   //before: out (range)
            &&
            c[i+1]==c[i]-(|g|/3)*2    //next: og
        ))
    }

    //circuit has structure out->og->in
    ghost predicate way2(g: Graph, c: seq<nat>, i: int)
    requires validUndirectedGraph(g)
    requires |g|>2 && |g|%3==0
    requires in_out_graph(g)
    requires 0<i<|c|-1
    {
        (0<=c[i]<|g|/3 ==>  //case og node
        (
            c[i-1]==c[i]+|g|/3    //before: out
            &&
            c[i+1]==c[i]+(|g|/3)*2  //next: in
        ))
        &&
        (|g|/3<=c[i]<(|g|/3)*2 ==>  //case out node
        (
            (|g|/3)*2<=c[i-1]<|g|   //before: in (range)
            &&
            c[i+1]==c[i]-|g|/3   //next: og
        ))
        &&
        ((|g|/3)*2<=c[i]<|g| ==>  //case in node
        (
            c[i-1]==c[i]-(|g|/3)*2    //before: og
            &&
            |g|/3<=c[i+1]<(|g|/3)*2   //next: out (range)
        ))
    }

    lemma in_out_circuit_lemma(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires isUndirectedHamiltonianCircuit(g, c)
        requires in_out_graph(g)
        ensures in_out_circuit(g, c)
    {
        assert (forall i :: 0<i<|c|-1 ==> way2(g, c, i)) ==> (forall i :: 0<i<|c|-1 ==> way1(g, rSeq(c), i));
        forall i | 0<i<|c|-1
        {
            in_out_circuit_local_lemma(g, c, i);
        }
    }

    lemma in_out_circuit_local_lemma(g: Graph, c: seq<nat>, i: int)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires isUndirectedHamiltonianCircuit(g, c)
        requires in_out_graph(g)
        requires 0<i<|c|-1
        ensures way1(g, c, i)
    {
        if 0<=c[i]<|g|/3
        {
            in_out_circuit_1_lemma(g, c, i);
            // assume c[i-1]==c[i]+(|g|/3)*2 && c[i+1]==c[i]+|g|/3;
        }
        if |g|/3<=c[i]<(|g|/3)*2
        {
            in_out_circuit_2_lemma(g, c, i);
            // assume c[i-1]==c[i]-|g|/3 && (|g|/3)*2<=c[i+1]<|g|;
        }
        if (|g|/3)*2<=c[i]<|g|
        {
            in_out_circuit_3_lemma(g, c, i);
            // assume |g|/3<=c[i-1]<(|g|/3)*2 && c[i+1]==c[i]-(|g|/3)*2;
        }
    }


    lemma in_out_circuit_1_lemma(g: Graph, c: seq<nat>, i: int)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires isUndirectedHamiltonianCircuit(g, c)
        requires in_out_graph(g)
        requires 0<i<|c|-1
        requires 0<=c[i]<|g|/3
        ensures c[i-1]==c[i]+(|g|/3)*2 || c[i+1]==c[i]+(|g|/3)*2
    {}
    
    lemma in_out_circuit_2_lemma(g: Graph, c: seq<nat>, i: int)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires isUndirectedHamiltonianCircuit(g, c)
        requires in_out_graph(g)
        requires 0<i<|c|-1
        requires |g|/3<=c[i]<(|g|/3)*2
        ensures c[i-1]==c[i]-|g|/3 && (|g|/3)*2<=c[i+1]<|g|
    {}

    lemma in_out_circuit_3_lemma(g: Graph, c: seq<nat>, i: int)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires isUndirectedHamiltonianCircuit(g, c)
        requires in_out_graph(g)
        requires 0<i<|c|-1
        requires (|g|/3)*2<=c[i]<|g|
        ensures |g|/3<=c[i-1]<(|g|/3)*2 && c[i+1]==c[i]-(|g|/3)*2 
    {}

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

}