module Dependent

type vector (a : Type) : nat -> Type = 
| Nil : vector a 0
| Cons : hd:a -> n:nat -> tl : vector a n -> vector a (n + 1)


let x = Cons 1231 1 (Cons 11321 0 Nil)

val add3 : vector int 3 -> int

let add3 x = match x with 
| Cons a 2 (Cons b 1 (Cons c 0 Nil)) -> a + b + c

let x1 = add3 (Cons 23 2 (Cons 44 1 (Cons 12 0 Nil)))
let x2 = add3 (Cons 230 2 (Cons 440 1 (Cons 120 0 Nil)))

val addn : (forall n . vector int n -> vector int n -> vector int n)
let addn = fun n -> 
