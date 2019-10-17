function fib(n : nat ) : nat
  decreases n
{
    if n < 2 then n else fib(n - 2) + fib(n - 1)
}

method computeFib (n : nat) returns (x : nat)
    ensures x == fib(n)
{
    var i := 0;
    x := 0;
    var y := 1;
    while  i < n 
        decreases n - i
        invariant 0 <= i <= n
        invariant x == fib(i)
        invariant y == fib(i+1)
    {
        x, y := y, x + y; // multiple assignment
        i := i + 1;
    }
}

method main() {
    var x0 := computeFib(0); 
    var x1 := computeFib(1); 
    var x2 := computeFib(2); 
    var x3 := computeFib(3); 
    var x4 := computeFib(4); 
    var x5 := computeFib(5); 
    
    assert x0 == 0;
    assert x1 == 1;
    assert x2 == 1;
    assert x3 == 2;
    assert x4 == 3;
    assert x5 == 5;
}