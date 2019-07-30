module Ahh


type sequence (a : Type) : nat -> Type =
| CNil : sequence a 0
| CCons : hd:a -> #n:nat -> tl : sequence a n -> sequence a (n + 1)

type aa2 =
| Nila2
| A2 : #n:nat -> (sequence aa2 n) -> aa2

type bb2 =
| Nilb2
| B2 : #n:nat -> (sequence bb2 n) -> bb2

val g2 : #n:nat -> (x:sequence aa2 n) -> Tot (sequence bb2 n) (decreases x)
val f2 : x:aa2 -> Tot bb2 (decreases x )
let rec f2 x = match x with
| Nila2 -> Nilb2
| A2 y -> B2 (g2 y)
and g2 #n x = match x with
| CNil -> CNil
| CCons y ys -> CCons (f2 y) (g2 ys)

val mapSequence : ('a -> Tot 'b) -> #n:nat -> (x: sequence 'a n) -> Tot (sequence 'b n) (decreases x)
let rec mapSequence f #n seq = match seq with
| CNil -> CNil
| CCons hd tl -> CCons (f hd) (mapSequence f tl)

val f3 : x:aa2 -> Tot bb2 (decreases x )
let rec f3 x = match x with
| Nila2 -> Nilb2
| A2 y -> B2 (mapSequence f3 y)
