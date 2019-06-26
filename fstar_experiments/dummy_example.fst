module Dummy_example

open FStar.All
open FStar.Exn

(* exception InvalidCondition *)
val example : int -> int 
let example n = if (true) then n else 0

let _ = assert (forall x . example x = x)

exception What
val example2 : int -> ML int
let example2 n = if (true) then () else raise What; n

(* let _ = assert (forall x . example2 x = x) 
   Note :F* complains because the type of example2 x is ML int whereas x is of type int *)
