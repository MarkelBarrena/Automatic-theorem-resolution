include "reduction_hamiltonian_definitions.dfy"
include "reduction_hamiltonian_rFunction.dfy"
include "permutation_property.dfy"

module ReductionCorrectness
{
    import opened Definitions
    import opened ReductionFunction
    import opened PermutationProperty

    ///// REDUCTION CORRECTNESS /////

    lemma reduction_lemma(g: Graph)
        requires validGraph(g)
        ensures directedHamiltonianCircuit(g) <==> undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
    {
        if directedHamiltonianCircuit(g)
        {
            reduction_forward_lemma(g);
        }
        if undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
        {
            reduction_backward_lemma(g);
        }
    }

    // Forward reduction: directedHamiltonian(g) ==> undirectedHamiltonian(f(g))

    lemma reduction_forward_lemma(g: Graph)
        requires validGraph(g)
        requires directedHamiltonianCircuit(g)
        ensures undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
    {
        var g' := directed_to_undirected_graph(g);

        assert |g'|>2;
        var dhc :| isDirectedHamiltonianCircuit(g, dhc);

        assert forall i :: 0<i<|g| ==> g[dhc[i-1]][dhc[i]] && g[dhc[|g|-1]][dhc[0]];

        var dhc_eq := circuit_equivalence(g, g', dhc);
        
    }

    // Backward reduction: undirectedHamiltonian(f(g)) ==> directedHamiltonian(g)

    lemma reduction_backward_lemma(g: Graph) //TODO
        requires validGraph(g)
        requires undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
        ensures directedHamiltonianCircuit(g)
    {} //see left_lemma_working_file.dfy

    //returns the directed circuit's undirected equivalence
    ghost function circuit_equivalence(g: Graph, g': Graph, circuit: seq<nat>): seq<nat>
        requires validGraph(g)
        requires |g|>0
        requires isDirectedHamiltonianCircuit(g, circuit)
        requires g' == directed_to_undirected_graph(g)
        ensures isUndirectedHamiltonianCircuit(g', circuit_equivalence(g, g', circuit))
    {
        var ce := circuit_equivalence_(g, g', circuit, |g|-1).0;
        assert ce == circuit_equivalence_(g, g', circuit, |g|-1).0;   //trivial but necessary
        assert UniqueElements(ce) by {circuit_equivalence_no_duplicates_lemma(g, g', circuit, |g|-1);}
        aux_lemma(ce);
        assert forall i :: 0<=i<|g'| ==> !(exists j :: 0<=j<|g'| && j!=i && ce[i]==ce[j]);  //no duplicates
        ce
    }

    /**
    outputs:
    0: circuit equivalent
    1-3 for verification purposes: partial correctness (no duplicates)
        1: all original nodes
        2: all out nodes
        3: all in nodes
     */
    ghost function circuit_equivalence_(g: Graph, g': Graph, circuit: seq<nat>, i: int): (seq<nat>, seq<nat>, seq<nat>, seq<nat>)
        requires validGraph(g)
        requires |g|>0
        requires isDirectedHamiltonianCircuit(g, circuit)
        requires g' == directed_to_undirected_graph(g)
        requires -1<=i<|circuit|
        decreases i
        //size relation
        ensures |circuit_equivalence_(g, g', circuit, i).0| == (i+1)*3
        ensures |circuit_equivalence_(g, g', circuit, i).0| % 3 == 0 //triplets
        // ensures |circuit_equivalence_(g, g', circuit, i)| == |circuit_equivalence_(g, g', circuit, i-1)|+3
        //central, in and out nodes position relation
        ensures forall j :: 0<=j<= i ==> 
        (
            circuit_equivalence_(g, g', circuit, i).0[3*j] == circuit[j]+|g|*2
            &&
            circuit_equivalence_(g, g', circuit, i).0[3*j+1] == circuit[j]
            &&
            circuit_equivalence_(g, g', circuit, i).0[3*j+2] == circuit[j]+|g|
        )
        //nodes boundaries
        ensures forall j :: 0<=j<|circuit_equivalence_(g, g', circuit, i).0| ==> circuit_equivalence_(g, g', circuit, i).0[j]<|g'|
        //connectivity
        ensures var circuit' := circuit_equivalence_(g, g', circuit, i).0;
            forall j :: 0<j<|circuit'| ==> (g'[circuit'[j-1]][circuit'[j]] || g'[circuit'[j]][circuit'[j-1]])
        //for partial correctness: no duplicates (working with 1, 2 & 3 sequences)
        //sizes
        ensures i>=0 ==> var a := circuit_equivalence_(g, g', circuit, i);
            |a.1|==i+1 && |a.2|==i+1 && |a.3|==i+1
        //contains
        ensures forall j :: 0<=j<|circuit_equivalence_(g, g', circuit, i).1| ==> circuit_equivalence_(g, g', circuit, i).1[j]==circuit[j]
        ensures forall j :: 0<=j<|circuit_equivalence_(g, g', circuit, i).2| ==> circuit_equivalence_(g, g', circuit, i).2[j] == circuit[j]+|g|
        ensures forall j :: 0<=j<|circuit_equivalence_(g, g', circuit, i).3| ==> circuit_equivalence_(g, g', circuit, i).3[j] == circuit[j]+|g|*2
        //unique elements (no duplicates)
        ensures UniqueElements(circuit_equivalence_(g, g', circuit, i).1) && UniqueElements(circuit_equivalence_(g, g', circuit, i).2) && UniqueElements(circuit_equivalence_(g, g', circuit, i).3)
        //no interdepenence: all elements in no overlapping ranges
        ensures var a := circuit_equivalence_(g, g', circuit, i);
            inRange(0, |g|, a.1) && inRange(|g|, |g|*2, a.2) && inRange(|g|*2, |g|*3, a.3)
    {
        if i==-1 then ([], [], [], []) else
            var circuit' := circuit_equivalence_(g, g', circuit, i-1);
            (circuit'.0 + [circuit[i]+|g|*2] + [circuit[i]] + [circuit[i]+|g|], circuit'.1+[circuit[i]], circuit'.2+[circuit[i]+|g|], circuit'.3+[circuit[i]+|g|*2])
    }

    //postcondition of circuit equivalence: circuit equivalent sequence is a permutation of 2nd + 3rd + 4th returning sequences
    lemma circuit_equivalence_post_lemma(g: Graph, g': Graph, circuit: seq<nat>, i: int)
        requires validGraph(g)
        requires |g|>0
        requires isDirectedHamiltonianCircuit(g, circuit)
        requires g' == directed_to_undirected_graph(g)
        requires -1<=i<|circuit|
        ensures multiset(circuit_equivalence_(g, g', circuit, i).0) == multiset(circuit_equivalence_(g, g', circuit, i).1) + multiset(circuit_equivalence_(g, g', circuit, i).2) + multiset(circuit_equivalence_(g, g', circuit, i).3)
    {}

    /**
    CRITICAL postcondition of circuit equivalence: circuit_equivalence has no duplicated values
    (2nd + 3rd + 4th has no duplicated values) && (circuit equivalent is a permutation of 2nd + 3rd + 4th)
        ||=> circuit equivalent has no duplicated values
    Note: uses "permutation_property.dfy" file's module, see file and link at the top for further information
    */
    lemma circuit_equivalence_no_duplicates_lemma(g: Graph, g': Graph, circuit: seq<nat>, i: int)
        requires validGraph(g)
        requires |g|>0
        requires isDirectedHamiltonianCircuit(g, circuit)
        requires g' == directed_to_undirected_graph(g)
        requires -1<=i<|circuit|
        ensures UniqueElements(circuit_equivalence_(g, g', circuit, i).0)
    {
        var c' := circuit_equivalence_(g, g', circuit, i);
        var s_aux := c'.1 + c'.2 + c'.3;
        assert s_aux == c'.1 + c'.2 + c'.3;
        assert UniqueElements(s_aux);
        assert multiset(c'.0) == multiset(s_aux) by {circuit_equivalence_post_lemma(g, g', circuit, i);} //by is usefull here
        assert |c'.0| == |s_aux|;
        UniqueMultiSet(s_aux, c'.0);
    }

    //trifling lemma for definition equivalences
    lemma aux_lemma(s: seq<nat>)
        requires UniqueElements(s)
        ensures forall i :: 0<=i<|s| ==> !(exists j :: 0<=j<|s| && j!=i && s[i]==s[j])
    {}

    //auxiliar predicate
    ghost predicate inRange(n1: int, n2: int, s:seq<nat>)
    {
        forall i :: 0<=i<|s| ==> n1<=s[i]<n2
    }

}