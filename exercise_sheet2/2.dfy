function method fact(n: nat) : nat
  decreases n
{
    if n == 0 then 1 else n * fact(n-1)
}

method factIter(n: nat) returns (f : nat)
    ensures f == fact(n)
{
    f := 1;
    var i := 0;
    while i < n 
        decreases n - i
        invariant 0 <= i <= n
        invariant f == fact(i)
    {
        i := i + 1;
        f := f * i;
    }
}

method main() {
    var x0 := factIter(0); 
    var x1 := factIter(1); 
    var x2 := factIter(2); 
    var x3 := factIter(3); 
    var x4 := factIter(4); 
    var x5 := factIter(5); 
    
    assert x0 == 1;
    assert x1 == 1;
    assert x2 == 2;
    assert x3 == 6;
    assert x4 == 24;
    assert x5 == 120;
}