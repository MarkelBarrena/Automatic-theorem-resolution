// This function calculates the sum of the elements of a sequence
function sum_seq(s:seq<int>): int
	ensures |s| == 1 ==> sum_seq(s) == s[0]  			
{
	if |s| == 0 then 0
	else  s[0] + sum_seq(s[1..])
}


// This function creates a sequence from a multiset
// This function will help later. 
ghost function seq_from_multiset(ms:multiset<int>): seq<int>
	ensures multiset(seq_from_multiset(ms)) == ms
	
{
	if ms == multiset{} then [] else 
		var i:| i in ms; 
		[i] + seq_from_multiset(ms - multiset{i})
}


// This problem is known as SubsetSum (it is NP-complete)
ghost predicate subsetSum(t:int, r:seq<int>)
{
	exists s:seq<int>:: multiset(s) <= multiset(r) && sum_seq(s) == t
}


// This problem is known as Partition.
ghost predicate partition(r:seq<int>)
{
	exists s:seq<int>:: multiset(s) <= multiset(r)  && sum_seq(r) == 2*sum_seq(s)
}


/**
The reduction: Subsetsum <=p Partition
**/


// Reduction function
// The reduction only adds a new element to the sequence r.
function subSetToPartition(t:int, r:seq<int>): seq<int>
{
	r + [sum_seq(r) - 2*t]
}


//Reduction correctness
lemma reduction_Lemma  (t:int, r:seq<int>)
	ensures subsetSum(t, r) <==> partition(subSetToPartition(t, r)) 
{
	if subsetSum(t, r) 
	{
		reduction_Lemma_right(t, r);
	}
	if partition(r + [sum_seq(r) - 2*t])
	{
		reduction_Lemma_left(t, r);
	}
}


lemma reduction_Lemma_right (t:int, r:seq<int>)
	requires subsetSum(t, r) 
	ensures partition(subSetToPartition(t, r)) 

{
	forall_distributive_sum_seq_Lemma();
	//var nr := r + [sum_seq(r) - 2*t];
	var s :|  multiset(s) <= multiset(r) && sum_seq(s) == t;
	var ns := s + [sum_seq(r) - 2*t]; 
	//assert sum_seq(ns) == sum_seq(r) - t;
	//assert  multiset(ns) <= multiset(nr)  && sum_seq(nr) == 2*sum_seq(ns);
	//assert partition(nr);	
}


lemma reduction_Lemma_left (t:int, r:seq<int>)
	requires partition(r + [sum_seq(r) - 2*t]) 
	ensures subsetSum(t, r)

{	
	forall_distributive_sum_seq_Lemma();
	var i := sum_seq(r) - 2*t;
	var nr := r + [i];
	var s :| multiset(s) <= multiset(nr)  && sum_seq(nr) == 2*sum_seq(s);	
	//assert sum_seq(s) == sum_seq(r) - t;
	if i !in multiset(s)
	{
		var sm := seq_from_multiset(multiset(r) - multiset(s));
		same_sum_Lemma(sm + s, r); //Same multisets have the same sum.
	}
	else
	{
		
		var sm := seq_from_multiset(multiset(s) - multiset{i}); 
		same_sum_Lemma(sm + [i], s); //Same multisets have the same sum.
		
	}
}


///// Auxiliar lemmas for sequences and multisets //////////////////////

lemma distributive_sum_seq_Lemma(s:seq<int>, r:seq<int>)
	ensures sum_seq(s + r) == sum_seq(s) + sum_seq(r)
{
	if s == [] 
	{ 
		assert s + r == r;
	}
	else
	{
		assert s + r == [s[0]] + (s[1..] + r);
	}
}

lemma forall_distributive_sum_seq_Lemma()
	ensures forall s,r :: sum_seq(s + r) == sum_seq(s) + sum_seq(r)
{
	forall s:seq<int>, r:seq<int>
	{
		distributive_sum_seq_Lemma(s, r);
	}
}

lemma same_sum_Lemma(s:seq<int>, r:seq<int>)
	requires multiset(r) == multiset(s)
	ensures sum_seq(r) == sum_seq(s)

{
	forall_distributive_sum_seq_Lemma();
	if r != []
	{
		assert r == [r[0]] + r[1..];
		assert multiset(r)[r[0]] == multiset(s)[r[0]];
		//assert r[0] in s;
		var j :| 0 <= j < |s| && s[j] == r[0];
		assert s == s[..j] + [r[0]] + s[j+1..];
		//assert sum_seq(s) == sum_seq(s[..j]) + r[0] + sum_seq(s[j+1..]); //sum_seq  distributes.
		var ss := s[..j] + s[j+1..];								
		//assert sum_seq(ss) == sum_seq(s[..j]) + sum_seq(s[j+1..]); //sum_seq distributes.
		assert multiset(ss) == multiset(s) - multiset{r[0]};
		same_sum_Lemma(ss, r[1..]);	//Same multisets have the same sum.				
		//assert sum_seq(r[1..]) == sum_seq(ss); //H.I.				
		//assert r[0] + sum_seq(r[1..]) == r[0] + sum_seq(ss); 	//Def. sum_seq.
		//assert sum_seq(r) == sum_seq(s);
	}
}


