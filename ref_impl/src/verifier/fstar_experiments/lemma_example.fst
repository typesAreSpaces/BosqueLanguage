module Lemma_example

let f (x : int) : int = x

val lemma_f : x : int -> Lemma (f x == x) 
let lemma_f x = ()

let x = 1


let _ = assert (forall x . (lemma_f x))
