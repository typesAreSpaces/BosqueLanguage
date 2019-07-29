module Ahh

val f0 : n:nat -> Tot nat (decreases (-n+1))
let rec f0 n = if (n > 0) then 0 else f0 (n + 1)

val f6 : n:nat -> Tot nat (decreases (-n + 7))
let rec f6 n = if (n > 6) then 0 else f6 (n + 1)

val lemma_f6 : n:nat -> Lemma (f6 n == 0)
let lemma_f6 n = ()


val f7 : n:nat -> Tot nat (decreases (-n + 8))
let rec f7 n = if (n > 7) then 0 else f7 (n + 1) 

// The fuel wasn't enough
val lemma_f7 : n:nat -> Lemma (ensures f7 n == 0)
let rec lemma_f7 n = admit(); if (n > 7) then () else lemma_f7 (n + 1)

// So it needs a ranking-function to work!
val lemma_f7_2 : n:nat -> Lemma (ensures f7 n == 0) (decreases (-n + 8))
let rec lemma_f7_2 n = if (n > 7) then () else lemma_f7_2 (n + 1)

val bar : l:list int -> Tot int (decreases %[l; 1])
val foo : l:list int -> Tot int (decreases %[l; 0])
let rec foo l = match l with
  | [] -> 0
  | x :: xs -> bar xs
and bar l = foo l


val ackermann: m:nat -> n:nat -> Tot nat (decreases %[m; n])
let rec ackermann m n =
  if m=0 then n + 1
    else if n = 0 then ackermann (m - 1) 1
      else ackermann (m - 1) (ackermann m (n - 1))

val max : nat -> nat -> nat
let max x y = if (x > y) then x else y

type list' (a : Type) : Type =
| Nil' : list' a
| Cons' : hd:a -> tl:list' a -> list' a

val map' : (f : 'a -> Tot 'b) -> list' 'a -> list' 'b
let rec map' f x = match x with
| Nil' -> Nil'
| Cons' y ys -> Cons' (f y) (map' f ys)

type option' (a : Type) : Type = 
| None' : option' a
| Some' : x : a -> option' a

// This works because None is an element of the option (list' 'a) and
// not an element of the list' 'a, I think
val mapOption : (f : 'a -> Tot 'b) -> option (list' 'a) -> option' (list' 'b)
let rec mapOption f x = match x with
| None -> None'
| Some y -> Some' (map' f y)

type aa = 
| Nila
| A : (list' aa) -> aa

type bb = 
| Nilb
| B : (list' bb) -> bb

val wfo_aa_aux : list' aa -> nat
val wfo_aa : aa -> nat
let rec wfo_aa x = match x with
| Nila -> 0
| A Nil' -> 1
| A (Cons' y ys) -> 1 + max (wfo_aa y) (wfo_aa_aux ys)
and wfo_aa_aux x = match x with
| Nil' -> 0
| Cons' y ys -> max (wfo_aa y) (wfo_aa_aux ys)

(* Testing *)
let test0 = Nila
let test1 = A (Cons' test0 Nil')
let test2 = A (Cons' test1 (Cons' test0 Nil'))
let test3 = A (Cons' test1 (Cons' test1 Nil'))
let wo_0 = wfo_aa test0
let wo_1 = wfo_aa test1
let wo_2 = wfo_aa test2
let wo_3 = wfo_aa test3

// // Bizarre ... This is actually the identity function on aa
// // This doesn't work
// val bizarre_id : x:aa -> Tot aa (decreases (wfo_aa x))
// let rec bizarre_id x = match x with
// | Nila -> Nila
// | A y -> A (map' bizarre_id y)

// // Bizarre ... This is actually the identity function on aa
// // This doesn't work either
// val bizarre_id : x:aa -> Tot aa (decreases (wfo_aa x))
// let rec bizarre_id x = match x with
// | Nila -> Nila
// | A Nil' -> A Nil'
// | A (Cons' y ys) -> A (Cons' (bizarre_id y) (map' bizarre_id ys))

// let test_0 = bizarre test0
// let test_1 = bizarre test1
// let test_2 = bizarre test2
// let test_3 = bizarre test3

// // First approach, it didn't work
// val f : x:aa -> Tot bb (decreases (wfo_aa x)) 
// let rec f x = match x with
// | Nila -> Nilb
// | A y -> B (map' f y)

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

// val maxaa2 : #n:nat -> sequence aa2 n -> aux:nat -> nat
// val rankingFunctionaa2 : aa2 -> nat
// let rec rankingFunctionaa2 x = match x with
// | Nila2 -> 0
// | A2 y -> 1 
// and maxaa2 #n x aux = match x with
// | CNil -> aux
// | CCons y ys -> maxaa2 ys (max aux (rankingFunctionaa2 y)) 

val wfo_aa2_aux : #n:nat -> sequence aa2 n -> nat 
val wfo_aa2 : aa2 -> nat
let rec wfo_aa2 x = match x with
| Nila2 -> 0
| A2 CNil -> 0
| A2 (CCons y #m ys) -> admit(); 1 + max (wfo_aa2 y) (wfo_aa2_aux #m ys)
and wfo_aa2_aux #n x = match x with
| CNil -> 0
| CCons y #m ys -> max (wfo_aa2 y) (wfo_aa2_aux #m ys)

let t0 = Nila2
let t1 = A2 (CCons t0 CNil)
let t2 = A2 (CCons t1 (CCons t0 CNil))
let t3 = A2 (CCons t1 (CCons t1 CNil))
let wt0 = wfo_aa2 t0
let wt1 = wfo_aa2 t1
let wt2 = wfo_aa2 t2
let wt3 = wfo_aa2 t3

val g2 : #n:nat -> sequence aa2 n -> sequence bb2 n
val f2 : x:aa2 -> Tot bb2 (decreases (wfo_aa2 x))
let rec f2 x = match x with
| Nila2 -> Nilb2
| A2 y -> B2 (g2 y)
// | A2 CNil -> B2 CNil
// | A2 (CCons y ys) -> B2 (CCons (f2 y) (g2 ys))
and g2 #n x = match x with
| CNil -> CNil
| CCons y ys -> CCons (f2 y) (g2 ys) 

let example1 = A2 (CCons (A2 CNil)  (CCons (A2 CNil) CNil) )
let example21 = A2 (CCons example1 CNil)
let example31 = f2 example21
