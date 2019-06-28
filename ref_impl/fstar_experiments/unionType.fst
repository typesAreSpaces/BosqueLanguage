module UnionType  

open FStar.All

type utib (t:eqtype) = x:t{t == int \/ t == bool}

val test : utib bool -> int
let test n = match n with
| true -> 1
| false -> 2
| _ -> n + 1

type utib2 'a = x:'a{x:int \/ x:bool}

val test2 : utib2 bool -> Tot int
let test2 n = match n with 
| true -> 1
| false -> 2
| _ -> n + 1

type none = | None : none
type noneableAux 'a 'b = x:'b{x:none \/ x:'a}
type noneable 'a = noneableAux 'a none

val test3 : noneable int -> Tot int
let test3 = fun n -> match n with
  | None -> 0
  | _ -> n

val maxNone : noneable int -> int -> Tot int
let maxNone x y = match x with
| None -> y
| _ -> if (x > y) then x else y
  
val simple : int -> int
let simple n = n

let x = simple 10

type list 'a = | Nil : list 'a | Const : hd : 'a -> tl : list 'a -> list 'a

type none = | None : none
