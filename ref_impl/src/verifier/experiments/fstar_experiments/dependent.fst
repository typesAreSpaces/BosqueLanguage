module Dependent

type vector (a : Type) : nat -> Type = 
| Nil : vector a 0
| Cons : hd:a -> n:nat -> tl:vector a n -> vector a (n + 1) 

val add_vector : n:nat -> x:(vector int n) -> y:(vector int n) -> vector int n
let rec add_vector n x y = match n with 
| 0 -> Nil
| m -> (match x, y with
      | Cons hd1 (m - 1) tl1, 
      )
