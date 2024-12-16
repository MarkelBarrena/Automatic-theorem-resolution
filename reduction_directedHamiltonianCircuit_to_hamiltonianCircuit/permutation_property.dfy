module PermutationProperty
{

    /**
    Question answered in stackoverflow:
    https://stackoverflow.com/questions/77049958/problems-in-trying-to-prove-non-duplicate-element-sequence-in-dafny

    1. If it is not case that all elements of sequence r are unique then there should exists indices m < n such that r[m] == r[n].
    2. Next we try to pair up elements of sequence s (left) with element of sequence r (right) by equality.
    3. To do that we find index ridx in r such r[ridx] equal to current element of s we are pairing.
    4. Now if ridx happens to be n, then we can pair current element of s with r[m] as r[m] == r[n]
    5. Effectively we are pairing up n distinct elements with n-1 elements.
    6. We do some index shifting to convince dafny that we indeed pairing with n-1 elements on right side of matching.
    7. By pigeonhole two elements of left should pair up with same element on right.
    8. This means those two elements are equal but that is not possible as all elements are distinct on left side.
    9. Our assumption is wrong and all elements on right side are distinct.
    */

    predicate UniqueElements(s: seq<int>)
    {
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
    }

    lemma pigeonhole(m : int, n: int, f : int -> int)
    requires 0 <= m < n
    requires forall i :: 0 <= i < n ==> 0 <= f(i) < m
    ensures exists j, k :: (0 <= j < k < n) && f(j) == f(k)
    {
    if m <= 0 {
        assert 0 <= f(0) < 0;
    }
    else {
        var i : int := 0;
        while i < n
        invariant forall k :: 0 <= k < i ==> 0 <= f(k) < m - 1
        invariant i <= n
        {
        if f(i) == m-1 {
            var j : int := i + 1;
            while j < n
            invariant forall k :: i < k < j ==> 0 <= f(k) < m - 1
            {
            if f(j) == m-1 { return; }
                j := j + 1;
            }
            var g : int -> int := x => if x < i then f(x) else f(x+1);
            pigeonhole(m-1, n-1, g);
            return;
        }
        i := i + 1;
        }
        pigeonhole(m-1, n, f);
    }
    }


    lemma UniqueMultiSet(s: seq<int>, r: seq<int>)
    requires UniqueElements(s)
    requires |s| == |r|
    requires multiset(s) == multiset(r)
    ensures UniqueElements(r)
    {
    assert |multiset(s)| == |multiset(r)|;
    if !UniqueElements(r){
        var m, n :| 0 <= m < n < |r| && r[m] == r[n];
        forall idx | 0 <= idx < |s| ensures exists ridx :: 0 <= ridx < |r| && r[ridx] == s[idx]
        {
        assert s[idx] in multiset(r);
        }
        var f : int -> int :=
        x => if 0 <= x < |s|
            then
                var idx :| 0 <= idx < |r| && r[idx] == s[x];
                if idx < n then idx else if idx == n then m else idx - 1
            else -1;
        pigeonhole(|s|-1, |s|, f);
        var k, l :| 0 <= k < l < |s| && f(k) == f(l);
        assert s[k] == s[l];
    }
    }

}