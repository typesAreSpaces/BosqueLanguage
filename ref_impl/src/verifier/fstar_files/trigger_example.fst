module Trigger_example

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

val length_append : x : list 'a -> y : list 'a -> Lemma (requires True) (ensures length x + length y = length (append x y)) [SMTPat (append x y)]
let rec length_append x y = match x with
| LNil -> ()
| LCons hd tl -> length_append tl y

val filter_append : p : ('a -> bool) -> x : list 'a -> y : list 'a 
  -> Lemma (requires True) (ensures (append (filter p x) (filter p y)) == (filter p (append x y)))
let rec filter_append p x y = match x with 
| LNil -> ()
| LCons hd tl ->  filter_append p tl y

val filtered_lists_are_smaller : 
p : ('a -> bool) -> x : list 'a -> Lemma (requires True) (ensures length x >= length (filter p x)) [SMTPat (filter p x)]
let rec filtered_lists_are_smaller p x = match x with
| LNil -> ()
| LCons hd tl -> filtered_lists_are_smaller p tl

val map_preserves_length : f : ('a -> 'b) -> x : list 'a 
  -> Lemma (requires True) (ensures length x = length (map f x)) [SMTPat (map f x)]
let rec map_preserves_length f x = match x with 
| LNil -> ()
| LCons hd tl -> map_preserves_length f tl

val positive_fun : x : list 'a -> Tot nat
let positive_fun x = length x

val another_positive_fun : x : list nat -> Tot nat
let another_positive_fun x = length x - (length (filter (fun (x : nat) -> x = 0) x))


assume type t

assume val (+): t -> t -> t

assume val plus_associative: x:t -> y:t -> z:t -> Lemma
  (requires True)
  (ensures  (x + y) + z == x + (y + z))
  [SMTPat ((x + y) + z)]

irreducible let trigger (x:t) (y:t) = True

val test: x:t -> y:t -> z:t -> Lemma
  (requires forall (a:t) (b:t).{:pattern (trigger a b)} trigger a b /\ a + b == b + a)
  (ensures  (x + y) + z == (z + y) + x)
let test x y z = cut (trigger z y /\ trigger x (z + y))


// assume type t

// assume val (+): t -> t -> t

// assume val plus_associative: x:t -> y:t -> z:t -> Lemma
//   (requires True)
//   (ensures  (x + y) + z == x + (y + z))
//   [SMTPat ((x + y) + z)]

// irreducible let trigger (x:t) (y:t) = True

// val test: x:t -> y:t -> z:t -> Lemma
//   (requires forall (a:t) (b:t).{:pattern (trigger a b)} trigger a b /\ a + b == b + a)
//   (ensures  (x + y) + z == (z + y) + x)
// let test x y z = cut (trigger z y /\ trigger x (z + y))
