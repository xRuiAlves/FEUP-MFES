function method abs(n: int) : nat {
    if n > 0 then n else -n
}

method div(n: nat, d: nat) returns (q: nat, r: nat)
    requires d > 0
    ensures 0 <= r < d && q * d + r == n {

    q := 0;
    r := n;  

    while r >= d
    decreases  r
    invariant q * d + r == n {
        q := q + 1;
        r := r - d;
    }
}

method Main()
{
    var q1, r1 := div(23, 6);
    assert q1 == 3;
    assert r1 == 5;

    var q2, r2 := div(17, 35);
    assert q2 == 0;
    assert r2 == 17;

    var q3, r3 := div(32, 1);
    assert q3 == 32;
    assert r3 == 0;
}