module Trigger_lib

type list 'a : Type = 
| LNil 
| LCons : hd : 'a -> tl : list 'a -> list 'a 

val length : list 'a -> Tot nat
let rec length x = match x with
| LNil -> 0
| LCons _ tl -> 1 + length tl

val append : list 'a -> list 'a -> list 'a
let rec append x y = match x with
| LNil -> y
| LCons hd tl -> LCons hd (append tl y)

val filter : ('a -> bool) -> list 'a -> list 'a
let rec filter p x = match x with
| LNil -> LNil
| LCons hd tl -> if (p hd) then LCons (hd) (filter p tl) else (filter p tl)

val map : ('a -> 'b) -> list 'a -> list 'b
let rec map f x = match x with
| LNil -> LNil
| LCons hd tl -> LCons (f hd) (map f tl)

val lemma_length_append : x : list 'a -> y : list 'a -> Lemma
  (requires True)
  (ensures length x + length y = length (append x y)) [SMTPat (append x y)]
let rec lemma_length_append x y = match x with
| LNil -> ()
| LCons hd tl -> lemma_length_append tl y

val lemma_length_map : f : ('a -> 'b) -> x : list 'a -> Lemma 
  (requires True) 
  (ensures length x = length (map f x)) [SMTPat (map f x)]
let rec lemma_length_map f x = match x with 
| LNil -> ()
| LCons hd tl -> lemma_length_map f tl

val lemma_length_filter : 
p : ('a -> bool) -> x : list 'a -> Lemma 
  (requires True) 
  (ensures length x >= length (filter p x)) [SMTPat (filter p x)]
let rec lemma_length_filter p x = match x with
| LNil -> ()
| LCons hd tl -> lemma_length_filter p tl

val filter_append : p : ('a -> bool) -> x : list 'a -> y : list 'a -> Lemma 
  (requires True) 
  (ensures (append (filter p x) (filter p y)) == (filter p (append x y))) [SMTPat (filter p (append x y))]
let rec filter_append p x y = match x with 
| LNil -> ()
| LCons hd tl ->  filter_append p tl y
