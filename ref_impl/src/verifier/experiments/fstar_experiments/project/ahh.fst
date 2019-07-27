module Ahh

type list' (a : Type) : Type =
| Nil' : list' a
| Cons' : hd:a -> tl:list' a -> list' a

type aa = 
| Nila
| A : (list' aa) -> aa

type bb = 
| Nilb
| B : (list' bb) -> bb

val g : list' aa -> list' bb
val f : aa -> Tot bb 
let rec f x = match x with
| Nila -> Nilb
| A y -> B (g y)
// | A Nil -> B Nil
// | A (Cons y ys) -> B (Cons (f y) (g ys))
and g x = match x with
| Nil' -> Nil'
| Cons' y ys -> Cons' (f y) (g ys) 

let example = A (Cons' (A Nil')  (Cons' (A Nil') Nil') )
let example2 = A (Cons' example Nil')
let example3 = f example2

(* ---------------------------------------------------------------------------- *)

type sequence (a : Type) : nat -> Type = 
| CNil : sequence a 0
| CCons : hd:a -> #n:nat -> tl : sequence a n -> sequence a (n + 1)

type aa2 = 
| Nila2
| A2 : #n:nat -> (sequence aa2 n) -> aa2

type bb2 = 
| Nilb2
| B2 : #n:nat -> (sequence bb2 n) -> bb2

val g2 : #n:nat -> sequence aa2 n -> sequence bb2 n
val f2 : aa2 -> Tot bb2 
let rec f2 x = match x with
| Nila2 -> Nilb2
| A2 y -> admit(); B2 (g2 y)
// | A2 CNil -> B2 CNil
// | A2 (CCons y ys) -> B2 (CCons (f2 y) (g2 ys))
and g2 #n x = match x with
| CNil -> CNil
| CCons y ys -> admit(); CCons (f2 y) (g2 ys) 

let example1 = A2 (CCons (A2 CNil)  (CCons (A2 CNil) CNil) )
let example21 = A2 (CCons example1 CNil)
let example31 = f2 example21

val f0 : n:nat -> Tot nat
let rec f0 n = if (n > 0) then 0 else f0 (n + 1)

val f6 : nat -> Tot nat
let rec f6 n = admit(); if (n > 6) then 0 else f6 (n + 1)

val lemma_f6 : n:nat -> Lemma (f6 n == 0)
let lemma_f6 n = ()

val max : m:nat -> n:nat -> nat
let max m n = if (m > n) then m else n

val f7 : n:nat -> Tot nat
let rec f7 n = if (n > 7) then 0 else f7 (n + 1)

// The fuel wasn't enough
val lemma_f7 : n:nat -> Lemma (f7 n == 0)
let rec lemma_f7 n = if (n > 7) then () else lemma_f7 (n + 1)

val foo : l:list int -> Tot int (decreases %[l; 0])
val bar : l:list int -> Tot int (decreases %[1; 1])
let rec foo l = match l with
| [] -> 0
| x :: xs -> bar xs
and bar l = foo l
