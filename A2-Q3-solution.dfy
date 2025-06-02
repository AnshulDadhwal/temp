method Rearrange(a: array<int>)
    modifies a
    ensures forall i :: 0 <= i < a.Length ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i]
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var n := 0;
    while n < a.Length
        invariant 0 <= n <= a.Length  // bounds on n
        invariant forall i :: 0 <= i < n ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i] // replace a.Length with n 
        invariant multiset(a[..]) == multiset(old(a[..])) // use postcondition
    {
        ghost var s := {};
        while 0 <= a[n] < a.Length && a[a[n]] != a[n]
            invariant forall i :: 0 <= i < n ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i] // weaken postcondition
            // Note that the postcondition of the inner loop has n+1 in place of n above
            invariant multiset(a[..]) == multiset(old(a[..])) // use postcondition
            // Note that Dafny deduces that the first invariant above is not altered by the loop body
            invariant forall val :: val in s ==> 0 <= val < a.Length && val == a[val]
            decreases (set val | val in a[..]) - s
        {
            s := s + {a[n]};
            a[n], a[a[n]] := a[a[n]], a[n];
        }
        n := n + 1;
    }
}

// Alternative where elements removed from a set
method Rearrange1(a: array<int>)
    modifies a
    ensures forall i :: 0 <= i < a.Length ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i]
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var n := 0;
    while n < a.Length
        invariant 0 <= n <= a.Length  // bounds on n
        invariant forall i :: 0 <= i < n ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i] // replace a.Length with n 
        invariant multiset(a[..]) == multiset(old(a[..])) // use postcondition
    {
        ghost var s := set i | 0 <= i < a.Length && a[i] != i; 
        while 0 <= a[n] < a.Length && a[a[n]] != a[n]
            invariant forall i :: 0 <= i < n ==> a[i] < 0 || a[i] >= a.Length || a[a[i]] == a[i] // weaken postcondition
            // Note that the postcondition of the inner loop has n+1 in place of n above
            invariant multiset(a[..]) == multiset(old(a[..])) // use postcondition
            // Note that Dafny deduces that the first invariant above is not altered by the loop body
            invariant s == set i | 0 <= i < a.Length && a[i] != i
            decreases s
        {
            s := s - {a[n]};
            if a[a[n]] == n {s := s - {n};}
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
{    
    Rearrange(a); 
    r := 0;
    while r != a.Length && r == a[r] 
        invariant 0 <= r <= a.Length // use postcondition
        invariant forall j :: 0 <= j < r ==> j in a[..] // use postcondition
    {
        r := r + 1;
    }
}