module BosqueCollections

open List

val lemma_length_append : x : list 'a -> y : list 'a -> Lemma
  (requires True)
  (ensures lengthList x + lengthList y = lengthList (appendList x y)) [SMTPat (appendList x y)]
let rec lemma_length_append x y = match x with
| LNil -> ()
| LCons hd tl -> lemma_length_append tl y

val lemma_length_map : f : ('a -> 'b) -> x : list 'a -> Lemma 
  (requires True) 
  (ensures lengthList x = lengthList (mapList f x)) [SMTPat (mapList f x)]
let rec lemma_length_map f x = match x with 
| LNil -> ()
| LCons hd tl -> lemma_length_map f tl

val lemma_length_filter : p : ('a -> bool) -> x : list 'a -> Lemma
  (requires True) 
  (ensures lengthList x >= lengthList (filterList p x)) [SMTPat (filterList p x)]
let rec lemma_length_filter p x = match x with
| LNil -> ()
| LCons hd tl -> lemma_length_filter p tl

val filter_append : p : ('a -> bool) -> x : list 'a -> y : list 'a -> Lemma 
  (requires True) 
  (ensures (appendList (filterList p x) (filterList p y)) == (filterList p (appendList x y))) [SMTPat (filterList p (appendList x y))]
let rec filter_append p x y = match x with 
| LNil -> ()
| LCons hd tl ->  filter_append p tl y 
