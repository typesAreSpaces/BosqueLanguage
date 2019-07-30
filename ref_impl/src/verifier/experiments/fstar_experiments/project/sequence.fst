module Sequence

type sequence 'a : nat -> Type = 
| SNil : sequence 'a 0
| SCons : hd:'a -> #n:nat -> tl : sequence 'a n -> sequence 'a (n + 1) 

val mapSequence : ('a -> Tot 'b) -> #n:nat -> (sequence 'a n) -> Tot (sequence 'b n)
let rec mapSequence f #n seq = match seq with
| SNil -> SNil
| SCons hd tl -> SCons (f hd) (mapSequence f tl)

val zipSequence : #a:Type -> #b:Type -> #n:nat -> sequence a n -> sequence b n -> Tot (sequence (a * b) n)
let rec zipSequence #a #b #n v1 v2 = match v1 with
  | SNil -> SNil
  | SCons a tl1 ->
    let SCons b tl2 = v2 in
    SCons (a, b) (zipSequence tl1 tl2)
