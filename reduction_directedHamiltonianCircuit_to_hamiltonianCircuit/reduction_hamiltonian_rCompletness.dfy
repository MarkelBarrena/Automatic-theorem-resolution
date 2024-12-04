include "reduction_hamiltonian_definitions.dfy"
include "reduction_hamiltonian_rFunction.dfy"

module ReductionCompletness
{
    import opened Definitions
    import opened ReductionFunction

    ///// REDUCTION COMPLETNESS /////

    lemma reduction_lemma(g: Graph)
        requires validGraph(g)
        ensures directedHamiltonianCircuit(g) <==> undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
    {
        if directedHamiltonianCircuit(g)
        {
            reduction_lemma_right(g);
        }
        if undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
        {
            reduction_lemma_left(g);
        }
    }

    // Reduction to the right: directedHamiltonian(g) ==> undirectedHamiltonian(f(g))

    lemma reduction_lemma_right(g: Graph)
        requires validGraph(g)
        requires directedHamiltonianCircuit(g)
        ensures undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
    {
        var g' := directed_to_undirected_graph(g);

        assert |g'|>2;
        var dhc :| isDirectedHamiltonianCircuit(g, dhc);

        // directedHamiltonianCircuitProperty_lemma(g, dhc);
        assert forall i :: 0<i<|g| ==> g[dhc[i-1]][dhc[i]] && g[dhc[|g|-1]][dhc[0]];

        var dhc_eq := circuit_equivalence(g, g', dhc);

        // var dhc_uEq := circuit_equivalence(g, g', dhc);
        // circuit_equivalent_lemma(g, g', dhc, dhc_uEq);

        // assert forall i :: 0<i<|g| ==> (g[dhc[i-1]][dhc[i]] ==> g'[dhc[i-1]+|g|][dhc[i]+|g|*2]);
        // assert forall i :: 0<i<|g| ==> (g[dhc[i-1]][dhc[i]] ==> g'[dhc[i-1]+|g|][dhc[i]+|g|*2]);
        // assert g[dhc[|g|-1]][dhc[0]] ==> g'[dhc[|g|-1]+|g|][dhc[0]+|g|*2];
        
    }

    // ghost predicate circuit_equivalent(g: Graph, g': Graph, circuit: seq<nat>, circuit': seq<nat>)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires isDirectedHamiltonianCircuit(g, circuit)
    //     requires g' == directed_to_undirected_graph(g)
    //     // ensures forall i :: (0<=i<|circuit'| && i % 3 ==1)  ==> circuit'[i] == circuit[(i-1)/3]
    // {
    //     |circuit'|==|g|*3
    //     &&
    //     (
    //         forall i :: 0<=i<|g| ==>    //giving the index of the original node i, the index of the same node in circuit': f(i)=3i+1
    //         (
    //             circuit'[i*3]==circuit[i]+|g|*2 //in node
    //             &&
    //             circuit'[i*3+1]==circuit[i] //central (original) node
    //             &&
    //             circuit'[i*3+2]==circuit[i]+|g| //out node
    //         )
    //     )
    // }

    // lemma circuit_equivalent_aux1_lemma(g: Graph, g': Graph, circuit: seq<nat>, circuit': seq<nat>)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires isDirectedHamiltonianCircuit(g, circuit)
    //     requires g' == directed_to_undirected_graph(g)
    //     requires circuit_equivalent(g, g', circuit, circuit')
    //     ensures forall i :: 0<=i<|circuit'| ==> circuit'[i]<|g'|
    // {
    //     forall i | 0<=i<|circuit'|
    //     {
    //         circuit_equivalent_aux1_local_lemma(g, g', circuit, circuit', i);
    //     }
    // }

    // lemma circuit_equivalent_aux1_local_lemma(g: Graph, g': Graph, circuit: seq<nat>, circuit': seq<nat>, i: int)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires isDirectedHamiltonianCircuit(g, circuit)
    //     requires g' == directed_to_undirected_graph(g)
    //     requires circuit_equivalent(g, g', circuit, circuit')
    //     requires 0<=i<|circuit'|
    //     ensures circuit'[i]<|g'|
    // {
    //     assert circuit'[i*3]==circuit[i]+|g|*2;
    //     assert circuit'[i*3+1]==circuit[i];
    //     assert circuit'[i*3+2]==circuit[i]+|g|;
    // }

    // lemma circuit_equivalent_lemma(g: Graph, g': Graph, circuit: seq<nat>, circuit': seq<nat>)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires isDirectedHamiltonianCircuit(g, circuit)
    //     requires g' == directed_to_undirected_graph(g)
    //     requires circuit_equivalent(g, g', circuit, circuit')
    //     ensures isUndirectedHamiltonianCircuit(g', circuit')
    // {
    //     if !isUndirectedHamiltonianCircuit(g', circuit')
    //     {
    //         reveal circuit_equivalent(g, g', circuit, circuit');
    //         directedHamiltonianCircuitProperty_lemma(g, circuit);
    //         assert forall i :: 0<i<|g| ==> g[circuit[i-1]][circuit[i]]; //property_lemma definition
    //         assert forall i :: 0<=i<|g| ==> circuit'[i*3+1]==circuit[i] && circuit'[i*3]==circuit[i]+|g|*2 && circuit'[i*3+2]==circuit[i]+|g|;  //equivalence property
    //         assert forall i :: 0<=i<|g| ==> 0<=circuit[i]<|g|;
    //         assert forall i :: 0<=i<|g| ==> g'[circuit'[i*3+1]][circuit'[i*3]];
    //     }
    // }

    //returns the directed circuit's undirected equivalence
    ghost function circuit_equivalence(g: Graph, g': Graph, circuit: seq<nat>): seq<nat>
        requires validGraph(g)
        requires |g|>2
        requires isDirectedHamiltonianCircuit(g, circuit)
        requires g' == directed_to_undirected_graph(g)
        ensures isUndirectedHamiltonianCircuit(g', circuit_equivalence(g, g', circuit))
    {
        circuit_equivalence_connectivity_lemma(g, g', circuit, |g|-1);
        circuit_equivalence_(g, g', circuit, |g|-1)
    }

    ghost function circuit_equivalence_(g: Graph, g': Graph, circuit: seq<nat>, i: int): seq<nat>
        requires validGraph(g)
        requires |g|>2
        requires isDirectedHamiltonianCircuit(g, circuit)
        requires g' == directed_to_undirected_graph(g)
        requires -1<=i<|circuit|
        decreases i
        //size relation
        ensures |circuit_equivalence_(g, g', circuit, i)| == (i+1)*3
        ensures |circuit_equivalence_(g, g', circuit, i)| % 3 == 0 //triplets
        // ensures |circuit_equivalence_(g, g', circuit, i)| == |circuit_equivalence_(g, g', circuit, i-1)|+3
        //central, in and out nodes position relation
        ensures forall j :: 0<=j<= i ==> 
        (
            circuit_equivalence_(g, g', circuit, i)[3*j] == circuit[j]+|g|*2
            &&
            circuit_equivalence_(g, g', circuit, i)[3*j+1] == circuit[j]
            &&
            circuit_equivalence_(g, g', circuit, i)[3*j+2] == circuit[j]+|g|
        )
        //reverse relation
        ensures i>=0 ==>
        (
            var circuit' := circuit_equivalence_(g, g', circuit, i);
            circuit'[|circuit'|-3] == circuit[(|circuit'|-3)/3]+|g|*2
            &&
            circuit'[|circuit'|-2] == circuit[((|circuit'|-2)-1)/3]
            &&
            circuit'[|circuit'|-1] == circuit[((|circuit'|-1)-2)/3]+|g|
        )
        // ensures forall j :: 0<=j<|circuit_equivalence_(g, g', circuit, i)| ==>
        // (
        //     (j % 3 == 0 ==> (circuit_equivalence_(g, g', circuit, i)[j] == circuit[(j)/3]+|g|*2))
        //     &&
        //     (j % 3 == 1 ==> (circuit_equivalence_(g, g', circuit, i)[j] == circuit[(j-1)/3]))
        //     &&
        //     (j % 3 == 2 ==> (circuit_equivalence_(g, g', circuit, i)[j] == circuit[(j-2)/3]+|g|))
        // )
        //nodes boundaries
        ensures forall j :: 0<j<|circuit_equivalence_(g, g', circuit, i)| ==> circuit_equivalence_(g, g', circuit, i)[j]<|g'|
        //connectivity
        // ensures var circuit' := circuit_equivalence_(g, g', circuit, i);
            // forall j :: 0<j<|circuit'| ==> g'[circuit'[j-1]][circuit'[j]]
    {
        if i==-1 then [] else
            var circuit' := circuit_equivalence_(g, g', circuit, i-1);
            var ret_circuit := circuit' + [circuit[i]+|g|*2] + [circuit[i]] + [circuit[i]+|g|];
            // assert |ret_circuit| == |circuit'|+3;
            // var i1, i2, i3 := |circuit'|, |circuit'|+1, |circuit'|+2;
            // assert ret_circuit[i1] == circuit[(i1)/3]+|g|*2;
            // assert ret_circuit[i2] == circuit[(i2-1)/3];
            // assert ret_circuit[i3] == circuit[(i3-2)/3]+|g|;
            ret_circuit
    }

    lemma circuit_equivalence_reverse_position_relation_lemma(g: Graph, g': Graph, circuit: seq<nat>, i: int)
        requires validGraph(g)
        requires |g|>2
        requires isDirectedHamiltonianCircuit(g, circuit)
        requires g' == directed_to_undirected_graph(g)
        requires -1<=i<|circuit|
        ensures var circuit' := circuit_equivalence_(g, g', circuit, i);
            forall j :: 0<=j<|circuit'| ==>
            (
                (j % 3 == 0 ==> (circuit'[j] == circuit[(j)/3]+|g|*2))
                &&
                (j % 3 == 1 ==> (circuit'[j] == circuit[(j-1)/3]))
                &&
                (j % 3 == 2 ==> (circuit'[j] == circuit[(j-2)/3]+|g|))
            )
    {
        if i>0
        {
            circuit_equivalence_reverse_position_relation_lemma(g, g', circuit, i-1);
            var circuit1 := circuit_equivalence_(g, g', circuit, i-1);
            var circuit2 := circuit_equivalence_(g, g', circuit, i);
            assert circuit2 == circuit_equivalence_(g, g', circuit, i-1) + [circuit[i]+|g|*2] + [circuit[i]] + [circuit[i]+|g|];
            assert forall j :: 0<=j<|circuit1| ==>
            (
                (j % 3 == 0 ==> (circuit1[j] == circuit[(j)/3]+|g|*2))
                &&
                (j % 3 == 1 ==> (circuit1[j] == circuit[(j-1)/3]))
                &&
                (j % 3 == 2 ==> (circuit1[j] == circuit[(j-2)/3]+|g|))
            );
            var j1, j2, j3 := |circuit2|-3, |circuit2|-2, |circuit2|-1;
            assert j1%3==0 && j2%3==1 && j3%3==2;
            // assert
            // (
            //     (j1 % 3 == 0 && (circuit1[j1] == circuit[(j1)/3]+|g|*2))
            //     &&
            //     (j2 % 3 == 1 && (circuit1[j2] == circuit[(j2-1)/3]))
            //     &&
            //     (j3 % 3 == 2 && (circuit1[j3] == circuit[(j3-2)/3]+|g|))
            // );
            assume forall j :: 0<=j<|circuit2| ==>
            (
                (j % 3 == 0 ==> (circuit2[j] == circuit[(j)/3]+|g|*2))
                &&
                (j % 3 == 1 ==> (circuit2[j] == circuit[(j-1)/3]))
                &&
                (j % 3 == 2 ==> (circuit2[j] == circuit[(j-2)/3]+|g|))
            );
        }
    }

    lemma circuit_equivalence_connectivity_lemma(g: Graph, g': Graph, circuit: seq<nat>, i: int)
        requires validGraph(g)
        requires |g|>2
        requires isDirectedHamiltonianCircuit(g, circuit)
        requires g' == directed_to_undirected_graph(g)
        requires 0<=i<|circuit|
        ensures var circuit' := circuit_equivalence_(g, g', circuit, i);
            (forall j :: 0<j<|circuit'| ==> g'[circuit'[j-1]][circuit'[j]]) && g'[circuit'[|circuit'|-1]][circuit'[0]]
    // {
    //     var circuit' := circuit_equivalence_(g, g', circuit, i);
    //     forall j | 0<j<|circuit'|
    //     {
    //         circuit_equivalence_connectivity_local_lemma(g, g', circuit, i, circuit', j);
    //     }
    // }

    // lemma circuit_equivalence_connectivity_local_lemma(g: Graph, g': Graph, circuit: seq<nat>, i: int, circuit': seq<nat>, j: int)
    //     requires validGraph(g)
    //     requires |g|>2
    //     requires isDirectedHamiltonianCircuit(g, circuit)
    //     requires g' == directed_to_undirected_graph(g)
    //     requires 0<=i<|circuit|
    //     requires circuit' == circuit_equivalence_(g, g', circuit, i)
    //     requires 0<j<|circuit'|
    //     ensures g'[circuit'[j-1]][circuit'[j]]
    // {
    //     if j%3==0
    //     {
    //         // assert circuit'[j] == circuit[j]+|g|*2;
    //         assume g'[circuit'[j-1]][circuit'[j]];
    //     }
    //     if j%3==1
    //     {assume g'[circuit'[j-1]][circuit'[j]];}
    //     if j%3==2
    //     {assume g'[circuit'[j-1]][circuit'[j]];}
    // }

    // Reduction to the left: undirectedHamiltonian(f(g)) ==> directedHamiltonian(g)

    lemma reduction_lemma_left(g: Graph) //TODO
        requires validGraph(g)
        requires undirectedHamiltonianCircuit(directed_to_undirected_graph(g))
        ensures directedHamiltonianCircuit(g)
    // {}


    // ghost function directedHamiltonianCircuit_witness(g: Graph): seq<nat>
    //     requires validGraph(g)
    //     requires directedHamiltonianCircuit(g)
    //     ensures isDirectedHamiltonianCircuit(g, (directedHamiltonianCircuit_witness(g)))

    // ghost function undirectedHamiltonianCircuit_witness(g: Graph): seq<nat>
    //     requires validUndirectedGraph(g)
    //     requires undirectedHamiltonianCircuit(g)
    //     ensures isUndirectedHamiltonianCircuit(g, (undirectedHamiltonianCircuit_witness(g)))

}