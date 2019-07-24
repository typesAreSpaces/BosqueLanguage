module Proving_termination

val ackermann : m : nat -> n:nat -> Tot nat(decreases %[m; n])
let rec ackermann m n = 
  if (m = 0) then n + 1
  else if (n = 0) then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))

val ackermann_swap: n:nat -> m:nat -> Tot nat (decreases %[m;n])
let rec ackermann_swap n m =
   if m=0 then n + 1
      else if n = 0 then ackermann_swap 1 (m - 1)
         else ackermann_swap (ackermann_swap (n - 1) m)
                                 (m - 1)
                                 
let rec append l1 l2 = match l1 with 
| [] -> l2
| hd :: tl -> hd :: append tl l2

let rec reverse l1 = match l1 with 
| [] -> []
| hd :: tl -> append (reverse tl) [hd]

val rev : l1 : list 'a -> l2 : list 'a -> Tot (list 'a) (decreases l2)
let rec rev l1 l2 = match l2 with 
| [] -> l1
| hd :: tl -> rev (hd :: l1) tl

val append_assoc : xs:list 'a -> ys:list 'a -> zs:list 'a -> Lemma
      (ensures (append (append xs ys) zs == append xs (append ys zs)))
      let rec append_assoc xs ys zs =
        match xs with
          | [] -> ()
            | x :: xs' -> append_assoc xs' ys zs

val lemma_aux : l1 : list 'a -> l2 : list 'a -> Lemma (ensures rev l1 l2 == append (reverse l2) l1) (decreases l2)
let rec lemma_aux l1 l2 = match l2 with 
| [] -> ()
| hd :: tl -> append_assoc (reverse tl) ([hd]) l1; lemma_aux (hd :: l1) tl

val lemma_append_empty : l1 : list 'a -> Lemma (append l1 [] == l1)
let rec lemma_append_empty l1 = match l1 with
| [] -> ()
| hd :: tl -> lemma_append_empty tl

val rev_is_ok : l : list 'a -> Lemma (rev [] l == reverse l)
let rev_is_ok l = lemma_append_empty (reverse l); lemma_aux ([]) l
