module Trigger_example

open Trigger_lib

val positive_fun : x : list 'a -> Tot nat
let positive_fun x = length x

val another_positive_fun : x : list nat -> Tot nat
let another_positive_fun x = length x - (length (filter (fun (x : nat) -> x = 0) x))

val hmm : p : ('a -> bool) -> x : list 'a -> y : list 'a -> Lemma 
  (requires True)
  (ensures (length (filter p (append x y))) == (length (filter p x)) + (length (filter p y)))
let hmm _ _ _ = ()
