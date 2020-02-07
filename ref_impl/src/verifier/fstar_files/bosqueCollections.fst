module BosqueCollections 

// Contains the axiomatization of 
// the collections used in Bosque

open List

val lemma_length_append : x : list 'a -> y : list 'a -> Lemma
  (requires True)
  (ensures lengthList x + lengthList y = lengthList (appendList x y)) [SMTPat (appendList x y)]
let rec lemma_length_append x y = match x with
| LNil -> ()
| LCons hd tl -> lemma_length_append tl y


// val lemma_length_map_3 : n:nat -> f:('a -> 'b) -> l1:list 'a -> l2:list 'b -> Lemma
//   (requires n < lengthList l1)
//   (ensures lengthList (mapList' l1 n l2 f) = lengthList l2 + lengthList l1 - n)
// let rec lemma_length_map_3 pos f l1 l2 = admit()

// val lemma_length_map_2 : n:nat ->  f:('a -> 'b) -> x:list 'a -> Lemma 
//   (requires (n < lengthList x))
//   (ensures (lengthList (mapList' x n LNil f)) = lengthList x - n)
// let rec lemma_length_map_2 pos f xs = lemma_length_map_3 pos f xs LNil

// val lemma_length_map_1 : f : ('a -> 'b) -> x : 'a -> xs : list 'a -> Lemma 
//   (requires True)
//   (ensures lengthList (mapList' (LCons x xs) 0 LNil f) = 1 + lengthList (mapList' xs 0 LNil f))
// let rec lemma_length_map_1 f x xs = match xs with
// | LNil -> ()
// | LCons hd tl -> lemma_length_map_1 f hd tl

val lemma_length_map : f : ('a -> 'b) -> x : list 'a -> Lemma 
  (requires True) 
  (ensures lengthList x = lengthList (mapList x f)) [SMTPat (mapList x f)]
let rec lemma_length_map f x = match x with 
| LNil -> ()
| LCons hd tl -> lemma_length_map_1 f hd tl; lemma_length_map f tl

val lemma_length_filter : p : ('a -> bool) -> x : list 'a -> Lemma
  (requires True) 
  (ensures lengthList x >= lengthList (filterList x p)) [SMTPat (filterList x p)]
let rec lemma_length_filter p x = match x with
| LNil -> ()
| LCons hd tl -> admit()
// | LCons hd tl -> lemma_length_filter p tlw

val filter_append : p : ('a -> bool) -> x : list 'a -> y : list 'a -> Lemma 
  (requires True) 
  (ensures (appendList (filterList x p) (filterList y p)) == (filterList (appendList x y) p)) [SMTPat (filterList (appendList x y) p)]
let rec filter_append p x y = match x with 
| LNil -> ()
| LCons hd tl ->  admit()
// | LCons hd tl ->  filter_append p tl y 
