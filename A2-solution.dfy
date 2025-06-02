method Rearrange(a: array<int>)
    modifies a
    ensures forall i :: 0 <= i < a.Length ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i]
    ensures multiset(a[..]) == multiset(old(a[..]))
    decreases *
{
    var n := 0;
    while n < a.Length
        invariant 0 <= n <= a.Length  // bounds on n
        invariant forall i :: 0 <= i < n ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i] // replace a.Length with n 
        invariant multiset(a[..]) == multiset(old(a[..])) // use postcondition
        decreases *
    {
        while 0 <= a[n] < a.Length && a[a[n]] != a[n]
            invariant forall i :: 0 <= i < n ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i] // weaken postcondition
            // Note that the postcondition of the inner loop has n+1 in place of n above
            invariant multiset(a[..]) == multiset(old(a[..])) // use postcondition
            // Note that Dafny deduces that the first invariant above is not altered by the loop body
            decreases *
        {
            a[n], a[a[n]] := a[a[n]], a[n];
        }
        n := n + 1;
    }
}

// Alternative with more direct postcondition
method Rearrange1(a: array<int>)
    modifies a
    ensures forall i :: 0 <= i < a.Length && i in a[..] ==> a[i] == i
    // can use a[..] instead of old(a[..]) here since multiset(a[..]) == multiset(old(a[..]))
    ensures multiset(a[..]) == multiset(old(a[..]))
    decreases *
{
    var n := 0;
    while n < a.Length
        invariant 0 <= n <= a.Length  // bounds on n
        invariant forall i :: 0 <= i < n && i in a[..] ==> a[i] == i || a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i] 
        // weaken postcondition then replace a.Length with n 
        // since a[a[i]] == a[i] when a[i] == i, this could be further simplified to 
        //        forall i :: 0 <= i < n && i in a[..] ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i]
        invariant forall i :: 0 <= i < n && i !in a[..] ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i]
        // additional invariant for cases when i is not in a[..]
        // could replace both invariants above with the single invariant 
        //        forall i :: 0 <= i < n ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i]
        invariant multiset(a[..]) == multiset(old(a[..])) // use postcondition
        decreases *
    {
        while 0 <= a[n] < a.Length && a[a[n]] != a[n]
            invariant forall i :: 0 <= i < n && i in a[..] ==> a[i] == i || a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i] 
            // weaken postcondition (since postcondition of the inner loop has n+1 in place of n above)
            invariant forall i :: 0 <= i < n && i !in a[..] ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i]
            // weaken postcondition (since postcondition of the inner loop has n+1 in place of n above)
            invariant multiset(a[..]) == multiset(old(a[..])) // use postcondition
            // Note that Dafny deduces that the first invariant above is not altered by the loop body
            decreases *
        {
            a[n], a[a[n]] := a[a[n]], a[n];
        }
        n := n + 1;
    }
}

method Find(a: array<int>) returns (r: int)
    modifies a
    ensures 0 <= r <= a.Length
    ensures r == a.Length || r !in a[..]
    ensures forall j :: 0 <= j < r ==> j in a[..]
    ensures multiset(a[..]) == multiset(old(a[..]))
    decreases *
{    
    Rearrange(a); 
    r := 0;
    while r != a.Length && r == a[r] 
        invariant 0 <= r <= a.Length // use postcondition
        invariant forall j :: 0 <= j < r ==> j in a[..] // use postcondition
        // Note: Dafny deduces that the postconditions of Rearrange are maintained
        // by the loop. These imply the final postcondition of this method, and the
        // second postcondition when the guard is negated. 
        decreases *
    {
        r := r + 1;
    }
}

method FindAll(a: array<int>) returns (b: array<bool>)
    modifies a
    ensures b.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> (i in a[..] <==> b[i])
    ensures multiset(a[..]) == multiset(old(a[..]))
    decreases *
{
    Rearrange(a); 
    b := new bool[a.Length];
    var n := 0;
    while n < a.Length
        invariant 0 <= n <= a.Length    // bounds on n
        invariant forall i :: 0 <= i < a.Length && i in a[..] ==> a[i] == i
        // additional invariant from Rearrange's postcondition
        invariant forall i :: 0 <= i < n ==> (i in a[..] <==> b[i]) // replace a constant with a variable
        invariant multiset(a[..]) == multiset(old(a[..]))   // use postcondition
        // Note: Dafny can deduce that the lengths of arrays a and b don't change and hence the first postcondition holds
        decreases *
    {
        if a[n] == n {
            b[n] := true;
        } else {
            b[n] := false;
        }
        n := n + 1;
    }
}