class Stack<T(0)> {
    ghost var s: seq<T>     
    ghost const max: nat  
    ghost var Repr: set<object>
    var a: array<T>
    var top: nat

    ghost predicate Valid() 
       
    constructor (max: nat)

    function Size(): nat

    method Push(v: T)

    method Pop() returns (v: T)
}

class Deque<T(0)> { 	
    ghost var q: seq<T>   	
    ghost const max: nat  
    ghost var Repr: set<object> 
    var a: array<T> 
    var front: nat 
    var back: nat 

    ghost predicate Valid() 

    constructor (max: nat) 

    function Size(): nat

    method AddBack(x:T)

    method AddFront(x:T)

    method RemoveBack() returns (x:T)

    method RemoveFront() returns (x:T)
}

class MidStack<T(0)> {
    ghost var s: seq<T>
    ghost const max: nat
    ghost var Repr: set<object>
    var stack: Stack<T>
    var deque: Deque<T>

    ghost predicate Valid()

    constructor (max: nat)

    function Size(): nat
    
    method Push(x: T)

    method Pop() returns (x:T)

    method PopMiddle() returns (x: T)
}