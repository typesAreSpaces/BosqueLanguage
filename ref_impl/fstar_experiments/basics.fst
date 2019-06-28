module Basics

open FStar.All

val simple : int -> bool
let simple = fun n -> n = 0

val simple2 : int -> int
let simple2 = fun n -> n 

// let _ = assert (forall x . simple x = true)
let _ = assert (exists x . simple2 x = x)
