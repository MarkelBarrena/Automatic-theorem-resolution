include "reduction_hamiltonian_definitions.dfy"
include "reduction_hamiltonian_rFunction.dfy"
include "permutation_property.dfy"
include "reduction_hamiltonian_rCompletness.dfy"
include "left_lemma_working_file.dfy"

module mod
{
    import opened Definitions
    import opened ReductionFunction
    import opened PermutationProperty
    import opened ReductionCompletness
    import opened LeftLemma

    lemma triplets_property3_lemmaAux(g: Graph, g': Graph, c: seq<nat>, cT: seq<seq<nat>>)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        requires g' == reverse_rFunction(g)
        requires standarized_in_out_circuit(g, c)
        requires cT == triplets(c)
        requires 0<=cT[|cT|-1][1]<|g'| && 0<=cT[0][1]<|g'|
        // requires forall i :: 0<i<|cT| ==> (isInNode(g, cT[i][0]) && isOgNode(g, cT[i][1]) && isOutNode(g, cT[i][2])) //property1
        // requires forall i :: 0<i<|cT| ==> (cT[i][0]==cT[i][1]+(|g|/3)*2 && cT[i][2]==cT[i][1]+|g|/3) //property1
        // requires forall i :: 0<i<|cT| ==> g[cT[i-1][2]][cT[i][0]] //property1
        // requires forall i :: 0<i<|cT| ==> (g[cT[i-1][2]][cT[i][0]] <==> g'[cT[i-1][1]][cT[i][1]]) //property2
        ensures g'[cT[|cT|-1][1]][cT[0][1]]
    {
        triplets_property1_lemma(g, c, cT);
        // triplets_property2_lemma(g, g', c, cT);
        // assert forall i :: 0<i<|cT| ==> (g[cT[i-1][2]][cT[i][0]] <==> g'[cT[i-1][1]][cT[i][1]]);
        var outF, inI, ogF, ogI := cT[|cT|-1][2], cT[0][0], cT[|cT|-1][1], cT[0][1];
        // assert forall f :: 0<=f<|g|/3 ==> (forall c :: 0<=c<|g|/3 ==> (g[f+|g|/3][c+(|g|/3)*2] <==> g'[f][c]));
        assert g[outF][inI]==>g'[ogF][ogI] by
        {
            dumb_aux_lemma(g, g', outF, inI, ogF, ogI);
        }
        assert g[outF][inI] by {triplets_property3_auxiliar_lemma(c, cT);}
        assert g'[ogF][ogI];
        assert ogF==cT[|cT|-1][1] && ogI==cT[0][1];
        // assume g'[cT[|cT|-1][1]][cT[0][1]];
    }

    lemma dumb_aux_lemma(g: Graph, g': Graph, c: seq<nat>, outF: nat, inI: nat, ogF: nat, ogI: nat)
        requires validUndirectedGraph(g)
        requires |g|>2 && |g|%3==0
        requires in_out_graph(g)
        requires isUndirectedHamiltonianCircuit(g, c)
        requires g' == reverse_rFunction(g)
        requires standarized_in_out_circuit(g, c)
        requires 0<=ogF<|g|/3
        requires 0<=ogI<|g|/3
        requires outF == ogF + |g|/3
        requires inI == ogI + (|g|/3)*2
        ensures g[outF][inI]==>g'[ogF][ogI]
    {
        assert forall f :: 0<=f<|g|/3 ==> (forall c :: 0<=c<|g|/3 ==> (g[f+|g|/3][c+(|g|/3)*2] <==> g'[f][c]));
    }

}