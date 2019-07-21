module Dependent

type vector (a : Type) : nat -> Type = 
| Nil : vector a 0
| Cons : hd:a -> #n:nat -> tl:vector a n -> vector a (n + 1) 

val add_vector : #n:nat -> x:(vector int n) -> y:(vector int n) -> vector int n
let rec add_vector #n x y = match x with 
| Nil -> Nil
| Cons hd tl -> 
  let (Cons hd2 tl2) = y in 
  Cons (hd + hd2) (add_vector tl tl2)
