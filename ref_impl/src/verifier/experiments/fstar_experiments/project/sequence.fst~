module Sequence

type sequence 'a : nat -> Type = 
| CNil : sequence 'a 0
| CCons : hd:'a -> #n:nat -> tl : sequence 'a n -> sequence 'a (n + 1) 

val mapSequence : ('a -> Tot 'b) -> #n:nat -> (sequence 'a n) -> Tot (sequence 'b n)
let rec mapSequence f #n seq = match seq with
| CNil -> CNil
| CCons hd tl -> CCons (f hd) (mapSequence f tl)
