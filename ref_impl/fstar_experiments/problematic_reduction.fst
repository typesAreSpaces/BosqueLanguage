module Problematic_reduction

type noneee = 
| Noneee : noneee

type noneableAux 'a 'b = x:'b{x:noneee \/ x:'a}
type noneable 'a = noneableAux 'a noneee

val test : noneable bool -> x:int{x>=0}
let test x = match x with
  | Noneee -> 0
  | _ -> x + 1

let _ = assert (forall x . test x >= 0)

val test2 : noneable int -> int
let test2 x = if (x = Noneee) then 0 else x + 1

let _ = assert (forall x . test2 x >= 0)
