module Factorial

open FStar.All
open FStar.Mul

val factorial: x:int{x>=0} -> Tot int
let rec factorial n = 
  if n = 0 then 1 else n * (factorial (n - 1))



val factorial_is_positive: x:nat -> GTot (u:unit{factorial x > 0})
let rec factorial_is_positive x =
  match x with
  | 0 -> ()
  | _ -> factorial_is_positive (x - 1)

val factorial_is_greater_than_arg : x:nat -> Lemma (requires(x>2)) (ensures (factorial x > x))
let rec factorial_is_greater_than_arg x = 
match x with
| 3 -> ()
| _ -> factorial_is_greater_than_arg (x - 1)

val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_greater_than_arg : n:nat{n >= 2} -> Lemma (fibonacci n >= n)
let rec fibonacci_greater_than_arg n = 
    match n with 
        | 2 -> ()
        | _ -> fibonacci_greater_than_arg (n - 1)

val what : x:'a{x:int /\ x:bool} -> x:'a{x:int /\ x:bool}
let what a = a
