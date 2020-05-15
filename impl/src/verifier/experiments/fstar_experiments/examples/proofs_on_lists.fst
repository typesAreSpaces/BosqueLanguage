module Proofs_on_lists

val length : list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

// Exercise 4a\
val append_with_property : l1 : list 'a -> l2 : list 'a -> l : list 'a {length l == length l1 + length l2}
let rec append_with_property l1 l2 = match l1 with 
| [] -> l2
| hd :: tl -> hd :: append_with_property tl l2

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val append_len : l1 : list 'a -> l2 : list 'a -> Lemma (requires True) (ensures (length (append l1 l2) == length l1 + length l2))
let rec append_len l1 l2 = match l1 with
  | [] -> ()
  | _ :: tl -> append_len tl l2

val mem : #a : eqtype -> a -> list a -> Tot bool
let rec mem #a x xs = match xs with 
| [] -> false
| hd :: tl -> hd = x || mem x tl

val append_mem : #a : eqtype -> l1 : list a -> l2 : list a -> x : a -> Lemma (mem x (append l1 l2) <==>  mem x l1 || mem x l2)
let rec append_mem #a l1 l2 x = match l1 with 
| [] -> ()
| _ :: tl -> append_mem tl l2 x

// val reverse : #a:Type -> f:(list 'a -> Tot (list 'a)){forall l . l == f (f l)}
val reverse : #a:Type -> list a -> Tot (list a)
let rec reverse #a = function 
| [] -> []
| hd :: tl -> append (reverse #a tl) [hd]

let snoc l h = append l [h]

val snoc_cons : l:list 'a -> h:'a -> Lemma (reverse (snoc l h) == h :: reverse l)
let rec snoc_cons tl hd = match tl with 
| [] -> ()
| _ :: xs -> snoc_cons xs hd

val rev_involutive : l : list 'a -> Lemma (reverse (reverse l) == l)
let rec rev_involutive = function
| [] -> ()
| hd :: tl -> rev_involutive tl; snoc_cons (reverse tl) hd

// Exercise 4d
val snoc_lemma : l1 :list 'a -> l2 : list 'a  -> x : 'a -> y : 'a -> Lemma (requires snoc l1 x == snoc l2 y) (ensures l1 == l2 /\ x == y)
let rec snoc_lemma l1 l2 x y = match l1, l2 with 
| _ :: tl1, _ :: tl2 -> snoc_lemma tl1 tl2 x y
| _, _ -> ()

val rev_injective : l1 : list 'a -> l2 : list 'a -> Lemma (requires (reverse l1 == reverse l2)) (ensures (l1 == l2))
let rec rev_injective x y = match x, y with 
| hd1::tl1, hd2::tl2 -> snoc_lemma (reverse tl1) (reverse tl2) hd1 hd2; rev_injective tl1 tl2
| _, _ -> ()
