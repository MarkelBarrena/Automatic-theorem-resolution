include "reduction_hamiltonian_definitions.dfy"
include "reduction_hamiltonian_rFunction.dfy"
include "permutation_property.dfy"
include "reduction_hamiltonian_rCompletness.dfy"
include "left_lemma_working_file.dfy"

module LeftLemmaAux
{
    import opened Definitions
    import opened ReductionFunction
    import opened PermutationProperty
    import opened ReductionCompletness
    import opened LeftLemma

    /**
    We must ensure a standard circuit (oneWay and starting on in).
        1. Verify that every circuit in the graph is either oneWay or otherWay (oneWayOrAnother_lemma).
        2. For a circuit otherWay reverse it to make it oneWay (reverse_way_property_lemma).
        3. For a circuit oneWay starting in other node cicle the sequence to start at an in_node (circuit_circular_property_lemma).
     */

    ghost function std_in_out_circuit(g: Graph): seq<nat>
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires undirectedHamiltonianCircuit(g)
        ensures isUndirectedHamiltonianCircuit(g, std_in_out_circuit(g))
        ensures standarized_in_out_circuit(g, std_in_out_circuit(g))
    {
        var c :| isUndirectedHamiltonianCircuit(g, c);
        startAtIn(g, makeOneWay(g, c))
    }

    ghost function makeOneWay(g: Graph, c: seq<nat>): seq<nat>
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        ensures isUndirectedHamiltonianCircuit(g, makeOneWay(g, c))
        ensures oneWay(g, makeOneWay(g, c))
    {
        oneWayOrAnother_lemma(g, c);
        if oneWay(g, c) then c else circuit_reverse_property_lemma(g, c); reverse_way_property_lemma(g, c); rSeq(c)
    }

    ghost function startAtIn(g: Graph, c: seq<nat>): seq<nat>
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        requires oneWay(g, c)
        ensures isUndirectedHamiltonianCircuit(g, startAtIn(g, c))
        ensures oneWay(g, c)
        ensures isInNode(g, startAtIn(g, c)[0])

    //if there is a node k that doesn't satisfy in->og->out order then neither of the nodes satisfy that order
    lemma aux_lemma(g: Graph, p: seq<nat>, k: nat)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        // requires isUndirectedHamiltonianCircuit(g, c)
        // requires !isOneWayPath(g, p)
        requires 0<=k<|p|-1
        requires
            !(
                (isInNode(g, p[k]) ==> isOgNode(g, p[k+1]))   //if this in next og
                &&
                (isOgNode(g, p[k]) ==> isOutNode(g, p[k+1]))   //if this og next out
                &&
                (isOutNode(g, p[k]) ==> isInNode(g, p[k+1]))   //if this out next in
            )
        ensures forall i :: 0<=i<|p|-1 ==>
                !(
                    (isInNode(g, p[i]) ==> isOgNode(g, p[i+1]))   //if this in next og
                    &&
                    (isOgNode(g, p[i]) ==> isOutNode(g, p[i+1]))   //if this og next out
                    &&
                    (isOutNode(g, p[i]) ==> isInNode(g, p[i+1]))   //if this out next in
                )
    {}

    lemma oneWayOrAnother_lemma(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        ensures oneWay(g, c) || otherWay(g, c)
    {

        if !oneWay(g, c)
            //must ensure otherWay(g, c)
        {
            // assert forall i :: 0<i<|c| ==> (g[c[i-1]][c[i]]) || (g[c[i]][c[i-1]]);
            // assert
            //     !(forall i :: 0<=i<|g|-1 ==>
            //     (
            //         (isInNode(g, c[i]) ==> isOgNode(g, c[i+1]))   //if this in next og
            //         &&
            //         (isOgNode(g, c[i]) ==> isOutNode(g, c[i+1]))   //if this og next out
            //         &&
            //         (isOutNode(g, c[i]) ==> isInNode(g, c[i+1]))   //if this out next in
            //     ));
            // var k :| 0<=k<|g|-1 && //use later at the forall /////
            //     !(
            //         (isInNode(g, c[k]) ==> isOgNode(g, c[k+1]))   //if this in next og
            //         &&
            //         (isOgNode(g, c[k]) ==> isOutNode(g, c[k+1]))   //if this og next out
            //         &&
            //         (isOutNode(g, c[k]) ==> isInNode(g, c[k+1]))   //if this out next in
            //     );
            
            // forall i /*{:trigger i}*/ | 0<=i<|g|-1
            //     ensures otherWay(g, c)
            // {
            //     assert (g[c[i]][c[i+1]] || g[c[i+1]][c[i]]);
            //     if isInNode(g, c[i])
            //     {
            //         //in_out definition:
            //         reveal in_out_graph(g);
                    
            //         assert (|g|/3)*2<=c[i]< |g|;
            //         assert forall f :: 0<=f<|g|/3 ==> (forall c :: 0<=c<|g| ==> (c==f+(|g|/3)*2 ==> g[f][c]));
            //         var n :| 0<=n<|g| && g[n][c[i]];

            //         assert g[n][c[i]];
            //         // assert g[c[i]-|g|/3][c[i]];
            //         // assert g[c[i]-(|g|/3)*2][c[i]];
            //         // assert isOgNode(g, c[i+1]) || isOutNode(g, c[i+1]);
            //     }
            }

            assume otherWay(g, c);
        }

        // if !(oneWay(g, c) || otherWay(g, c))
        // {
        //     assert !oneWay(g, c) && !otherWay(g, c);
        //     assert forall i :: 0<i<|c| ==> (g[c[i-1]][c[i]]) || (g[c[i]][c[i-1]]);
        //     assert
        //         !(forall i :: 0<=i<|g|-1 ==>
        //         (
        //             (isInNode(g, c[i]) ==> isOgNode(g, c[i+1]))   //if this in next og
        //             &&
        //             (isOgNode(g, c[i]) ==> isOutNode(g, c[i+1]))   //if this og next out
        //             &&
        //             (isOutNode(g, c[i]) ==> isInNode(g, c[i+1]))   //if this out next in
        //         ))
        //         &&
        //         !(forall i :: 0<=i<|g|-1 ==>
        //         (
        //             (isOutNode(g, c[i]) ==> isOgNode(g, c[i+1]))   //if this out next og
        //             &&
        //             (isOgNode(g, c[i]) ==> isInNode(g, c[i+1]))   //if this og next in
        //             &&
        //             (isInNode(g, c[i]) ==> isOutNode(g, c[i+1]))   //if this in next out
        //         ))
        //         ;
        //     assert exists i :: 0<=i<|g|-1 &&
        //         !(
        //             (isInNode(g, c[i]) ==> isOgNode(g, c[i+1]))   //if this in next og
        //             &&
        //             (isOgNode(g, c[i]) ==> isOutNode(g, c[i+1]))   //if this og next out
        //             &&
        //             (isOutNode(g, c[i]) ==> isInNode(g, c[i+1]))   //if this out next in
        //         );
        //     // assert exists i :: 0<=i<|g|-1 &&
        //     //     !(
        //     //         (isOutNode(g, c[i]) ==> isOgNode(g, c[i+1]))   //if this out next og
        //     //         &&
        //     //         (isOgNode(g, c[i]) ==> isInNode(g, c[i+1]))   //if this og next in
        //     //         &&
        //     //         (isInNode(g, c[i]) ==> isOutNode(g, c[i+1]))   //if this in next out
        //     //     );
            
        //     var i :| 0<=i<|g|-1 &&
        //         !(
        //             (isInNode(g, c[i]) ==> isOgNode(g, c[i+1]))   //if this in next og
        //             &&
        //             (isOgNode(g, c[i]) ==> isOutNode(g, c[i+1]))   //if this og next out
        //             &&
        //             (isOutNode(g, c[i]) ==> isInNode(g, c[i+1]))   //if this out next in
        //         );
            
        //     assert (g[c[i]][c[i+1]] || g[c[i+1]][c[i]]);
        //     // (forall f :: (|g|/3)*2<=f<|g| ==> (forall c :: (|g|/3)*2<=c<|g| ==> !g[f][c]));    //no vertex from in to in


        //     assume !isUndirectedHamiltonianCircuit(g, c);
        // }
    // }

    ghost function rSeq(s: seq<nat>): seq<nat>
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

    lemma reverse_way_property_lemma(g: Graph, c: seq<nat>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        requires otherWay(g, c)
        ensures oneWay(g, rSeq(c))
    //TODO

}