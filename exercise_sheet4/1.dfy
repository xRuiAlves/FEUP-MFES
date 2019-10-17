type T = int // to allow doing new T[capacity], but can be other type 

 
class {:autocontracts} Stack
{

    const elems: array<T>; // immutable (pointer)
    var size : nat; // used size

    predicate Valid() {
        size <= elems.Length
    }
 
    constructor (capacity: nat)
        ensures size == 0
        ensures elems.Length == capacity
    {
        elems := new T[capacity];
        size := 0; 
    }
 
    predicate method isEmpty()
    {
        size == 0
    }
 
    predicate method isFull()
    {
        size == elems.Length
    }
 
    method push(x : T)
        requires size < elems.Length
        ensures elems[..size] == old(elems[..size]) + [x]
    {
        elems[size] := x;
        size := size + 1;
    }
 
    function method top(): T
        requires size > 0
    {
         elems[size-1]
    }

    method pop() 
        requires size > 0
        ensures elems[..size] == old(elems[..size-1])
    {
         size := size-1;
    }
}

// A simple test case.
method Main()
{
    var s := new Stack(3);
    assert s.isEmpty();
    s.push(1);
    s.push(2);
    s.push(3);
    assert s.top() == 3;
    assert s.isFull();
    s.pop();
    assert s.top() == 2;
    print "top = ", s.top(), " \n";
}
