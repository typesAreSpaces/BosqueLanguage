module Sequence

type sequence 'a : nat -> Type = 
| SNil : sequence 'a 0
| SCons : hd:'a -> #n:nat -> tl : sequence 'a n -> sequence 'a (n + 1) 

val mapSequence : ('a -> Tot 'b) -> #n:nat -> (sequence 'a n) -> Tot (sequence 'b n)
let rec mapSequence f #n seq = match seq with
| SNil -> SNil
| SCons hd tl -> SCons (f hd) (mapSequence f tl)
