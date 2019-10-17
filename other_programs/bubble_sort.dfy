type T = int 

predicate isSortedRanged(a: array<T>, x1: nat, x2: nat) 
    reads a
    requires 0 <= x1 <= x2 <= a.Length
{
    forall i, j :: x1 <= i < j < x2 ==> a[i] <= a[j]
}

predicate isSorted(a: array<T>)
    reads a
{
    isSortedRanged(a, 0, a.Length)
}

method bubbleSort(a: array<T>)
    modifies a
    ensures isSorted(a)
    ensures multiset(a[..]) == multiset(old(a[..])) 
{
    var i := a.Length;
    while i > 1
        decreases i - 1
        invariant multiset(a[..]) == multiset(old(a[..])) 
        invariant 0 <= i <= a.Length
        invariant forall l, r :: (0 <= l < r < a.Length && r >= i) ==> a[l] <= a[r]
    {
        var j := 0;
        while j < i - 1
            decreases i - j - 1
            invariant multiset(a[..]) == multiset(old(a[..])) 
            invariant 0 <= j < i
            invariant forall l, r :: (0 <= l < r < a.Length && (r >= i || r == j))  ==> a[l] <= a[r]
        {
            if (a[j] > a[j+1]) 
            { 
                a[j], a[j+1] := a[j+1], a[j]; 
            }
            j := j+1; 
        }
        i := i-1;
    }
}

 method Main() {
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 9, 4, 6, 3, 8;
    bubbleSort(a);
    assert isSorted(a);
}