module Intuitionistic_proof 

val factorial : x:int{x >= 0} -> Tot int
let rec factorial n = if (n = 0) then 1 else op_Multiply n (factorial (n - 1))

val factorial_is_positive : x:nat -> GTot (u:unit{factorial x > 0})
let rec factorial_is_positive x = match x with 
| 0 -> ()
| _ -> factorial_is_positive (x - 1)

val factorial_is_greater_than_arg : x : (y : nat{ y > 2}) -> GTot (u : unit {factorial x > x})
let rec factorial_is_greater_than_arg x = 
match x with 
| 3 -> ()
| _ -> factorial_is_greater_than_arg (x - 1)

val fibonacci : nat -> Tot nat 
let rec fibonacci n = if (n <= 1) then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fib_greater_than_arg : n : nat{n >= 2} -> Lemma (fibonacci n >= n)
let rec fib_greater_than_arg x = match x with 
| 2 -> ()
| _ -> fib_greater_than_arg (x - 1)


val length : list 'a -> Tot nat
let rec length x = match x with
  | Nil -> 0
  | _ :: xs -> 1 + length xs

let rec append l1 l2 = match l1 with
  | Nil -> l2
  | hd :: tl -> hd :: append tl l2


val lemma_append : l1 : list 'a -> l2 : list 'a -> Lemma (length (append l1 l2) == length l1 + length l2)
let rec lemma_append l1 l2 = match l1 with
  | Nil -> ()
  | _ :: tl -> lemma_append tl l2 


// Impressive!
val ackermann : nat -> nat -> Tot nat
let rec ackermann m n =
  if (m = 0) then n + 1
  else if n = 0 then ackermann (m - 1) 1 
  else ackermann (m - 1) (ackermann m (n - 1))

