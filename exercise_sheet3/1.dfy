predicate isSorted(a: array<int>)
  reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

method binarySearch(a: array<int>, x: int) 
    returns (index: int)
    requires isSorted(a)
    ensures -1 <= index < a.Length
    ensures index == -1 ==> x !in a[..]
    ensures index >= 0  ==> a[index] == x

{   
    var low, high := 0, a.Length;
    while low < high 
        decreases high - low
        invariant 0 <= low <= high <= a.Length
        invariant x !in a[..low]
        invariant x !in a[high..]
    {
        var mid := low + (high - low) / 2;
        if 
        {
            case a[mid]  < x => low := mid + 1;
            case a[mid]  > x => high := mid;
            case a[mid] == x => return mid;
        }
    }
    return -1;
}

method Main() {
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 1, 5, 10, 12, 15;

    var x0 := binarySearch(a, 4);
    var x1 := binarySearch(a, 5);
    
    assert x0 == -1;
}
