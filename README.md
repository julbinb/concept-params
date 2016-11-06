# Concept Parameters for Generic Programming

## Concept Parameters in STLC 

Coq formalization of "concept parameters" for "generic" programming in STLC.

The first step is to add simple **concepts** and **models** into STLC:
look at `cpSTLCa*` files in [`cpSTLC`](cpSTLC).  
Concepts contain function signatures only, models define those functions.
A program in cpSTLCa consists of concepts' and models' definitions and
a term in STLC extended with concept parametrization and model application.

Here is an example of well-typed cpSTLCa program:

```
concept MonoidNat
  ident : Nat
  op    : Nat -> Nat -> Nat
endc

model MNPlus of MonoidNat
  ident = 0
  op    = \x:Nat.\y:Nat. x + y
endm

model MNMult of MonoidNat
  ident = 1
  op    = \x:Nat.\y:Nat. x * y
endm

(* accOrTwice takes MonoidNat concept parameter 
     and two nats, x and y, 
   and either accumulates x and y using monoid binary operation
     (if x is not equal to identity element)
     or accumulates y and y (if x is equal to identity element) 
*)
let 
  accOrTwice = \m#MonoidNat. \x:Nat.\y:Nat. if x == m.ident 
                 then m.op y y
                 else m.op x y
                          
in
  (* sum of 3 5*)
  accOrTwice # MNSum 3 5
```
