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
    var i := 0;
    while i < a.Length - 1
        decreases a.Length - i
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant 0 <= i <= a.Length
        invariant forall l, r :: (0 <= l < r < a.Length && l < i) ==> a[l] <= a[r]
    {
        var j := a.Length - 1;
        while j > i
            decreases j - i
            invariant multiset(a[..]) == multiset(old(a[..]))
            invariant i <= j < a.Length
            invariant forall l, r :: (0 <= l < r < a.Length && (l < i || j == l)) ==> a[l] <= a[r]
        {
            if (a[j] < a[j-1]) 
            { 
                a[j], a[j-1] := a[j-1], a[j]; 
            }
            j := j-1; 
        }
        i := i+1;
    }
}

method Main() {
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 9, 4, 6, 3, 8;
    bubbleSort(a);
    assert isSorted(a);
}