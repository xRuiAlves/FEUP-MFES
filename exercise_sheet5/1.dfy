type T = int // for demo purposes, but could be another type
 
class {:autocontracts} Deque
{
    // (Public) ghost variables used for specification purposes only
    ghost var elems: seq<T>;  // front at head, back at tail
    ghost const capacity: nat; 

    // (Private) concrete variables 
    const list: array<T>; // circular array, from list[start] (front) to list[(start+size-1) % list.Length] (back) 
    var start : nat; 
    var size : nat;

    predicate Valid()
    {
        // integrity constraints on concrete representation 
        0 <= size <= list.Length  && 0 <= start < list.Length 
        // abstraction relation
        && capacity == list.Length 
        && elems == if start + size <= list.Length then list[start..start + size]
                    else list[start..] + list[..size - (list.Length - start)]  
    }
 
    constructor (capacity: nat)
      requires capacity > 0
      ensures elems == [] && this.capacity == capacity
    {
        // initialize concrete variables
        list := new T[capacity];
        start := 0;
        size := 0;
        // initialize ghost variables
        this.capacity := capacity;
        elems := []; 
    }

    predicate method isEmpty()
      ensures isEmpty() <==> elems == []
    {
        size == 0
    }
    
    predicate method isFull()
      ensures isFull() <==> |elems| == capacity
    {
        size == list.Length
    }

    function method front() : T
      requires !isEmpty()
      ensures front() == elems[0]
    {
        list[start]
    }

    function method back() : T
      requires !isEmpty()
      ensures back() == elems[|elems| - 1]
    {
        list[(start + size - 1) % list.Length] 
    }
    
    method push_back(x : T)
      requires !isFull()
      ensures elems == old(elems) + [x]
    {
        // update concrete variables
        list[(start + size) % list.Length] := x;
        size := size + 1;
        // update ghost variable
        elems := elems + [x];
    }

    method pop_back()
      requires !isEmpty()
      ensures elems == old(elems[..|elems|-1])
    {
        // update concrete variables
        size := size - 1;
        // update ghost variable
        elems := elems[..|elems|-1];
    }

    method push_front(x : T)
      requires !isFull()
      ensures elems == [x] + old(elems) 
    {
        // update concrete variables
        if start > 0
        {
            start := start - 1;
        }
        else
        {
            start := list.Length - 1;
        }
        list[start] := x;
        size := size + 1;
        // update ghost variable
        elems := [x] + elems;
    }    

    method pop_front()
      requires !isEmpty()
      ensures elems == old(elems[1..]) 
    {
        // update concrete variables
        if start + 1 < list.Length
        {
            start := start + 1;
        }
        else
        {
            start := 0;
        }
        size := size - 1;
        // update ghost variable
        elems := elems[1..];
    } 

}
 
// A simple test scenario.
method testDeque()
{
    var q := new Deque(3);
    assert q.isEmpty();
    q.push_front(1);
    assert q.front() == 1;
    assert q.back() == 1;
    q.push_front(2);
    assert q.front() == 2;
    assert q.back() == 1;
    q.push_back(3);
    assert q.front() == 2;
    assert q.back() == 3;
    assert q.isFull();
    q.pop_back();
    assert q.front() == 2;
    assert q.back() == 1;
    q.pop_front();
    assert q.front() == 1;
    assert q.back() == 1;
    q.pop_front();
    assert q.isEmpty();
}
