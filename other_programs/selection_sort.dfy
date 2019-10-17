predicate isSortedRanged(a: array<int>, x1: nat, x2: nat)
  requires 0 <= x1 <= x2 <= a.Length
  reads a
{
    forall i, j :: x1 <= i < j < x2 ==> a[i] <= a[j] 
}
predicate isSorted(a: array<int>)
  reads a
{
    isSortedRanged(a, 0, a.Length)
}

method selectionSort(a: array<int>)
    modifies a
    ensures multiset(a[..]) == multiset(old(a[..]))
    ensures isSortedRanged(a, 0, a.Length) 
{
    var i := 0; 
    while i < a.Length 
        decreases a.Length - i
        invariant multiset(a[..]) == multiset(old(a[..]))
        invariant 0 <= i <= a.Length
        invariant isSortedRanged(a, 0, i)
        invariant forall l, r :: 0 <= l < i <= r < a.Length ==> a[l] <= a[r] 
    {
        var min_index := findMin(a, i, a.Length);
        a[i], a[min_index] := a[min_index], a[i];
        i := i + 1;
    }

}

method findMin(a: array<int>, x1: nat, x2: nat) returns(index: nat)
  requires 0 <= x1 < x2 <= a.Length
  ensures x1 <= index < x2
  ensures forall i :: x1 <= i < x2 ==> a[i] >= a[index]
{
    index := x1;
    var i := x1;
    while i < x2
      decreases a.Length - i
      invariant x1 <= i <= x2
      invariant x1 <= index < x2
      invariant forall x :: x1 <= x < i ==> a[x] >= a[index]  
    {
        if a[i] < a[index] {
            index := i;
        }
        i := i + 1;
    }
}

method Main() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 5, 12, 4, 0, 4;
  selectionSort(a);
  assert isSorted(a);
}