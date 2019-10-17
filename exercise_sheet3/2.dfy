predicate isSortedRanged(a: array<int>, x1: nat, x2: nat) 
    reads a
    requires 0 <= x1 <= x2 <= a.Length
{
    forall i, j :: x1 <= i < j < x2 ==> a[i] <= a[j]
}

predicate isSorted(a: array<int>)
    reads a
{
    isSortedRanged(a, 0, a.Length)
}

method insertionSort(a: array<int>)
    modifies a 
    ensures isSorted(a) 
    ensures multiset(a[..]) == multiset(old(a[..])) 
{
    var i := 0;
    while i < a.Length 
        decreases a.Length - i
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant 0 <= i <= a.Length
        invariant isSortedRanged(a, 0, i)
    {
        var j := i;
        while j > 0 && a[j-1] > a[j] 
            decreases j 
            invariant multiset(a[..]) == multiset(old(a[..]))
            invariant 0 <= j <= i
            invariant forall l, r :: (0 <= l < r <= i && j != r) ==> a[l] <= a[r]
        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
        i := i + 1;
    }
}

method Main() {
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 9, 4, 6, 3, 8;
    insertionSort(a);
    assert isSorted(a);
}