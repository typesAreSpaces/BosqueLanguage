module UnionType  

open FStar.All

val the_idea : x:int{x >= 0} -> x:int{x >= 1}
let the_idea n = if (n = 0) then 1 else n
(* Seems to work *)


// Goal: create a type A such that :
// 1) ... -1, 0, 1, ... : A
// 2) false, true : A
// Kind of like a union type, I'm aware this is
// not the standard definition

(* type intbool = #a:Type -> x:a{x:int \/ x:bool} *)

(* val test : intbool -> intbool *)
(* let test n = if (n = true) then 1 else if (n = false) then 2 else n *)


type list 'a = 
| Nil  : list 'a
| Cons : hd:'a -> tl:list 'a -> list 'a

type listInt = 
| NilInt  : listInt
| ConsInt : hdInt:int -> tlInt:listInt -> listInt

type whate = 
| A : whate

type none = 
| None : none

type either 'a 'b =
| Either : left : 'a -> right : 'b -> either 'a 'b

val projectLeft : either 'a 'b -> 'a
let projectLeft n = match n with 
| Either x y -> x

val projectRight : either 'a 'b -> 'b
let projectRight n = match n with 
| Either x y -> y

let whatever : either int bool = Either 12 true
let hmmm = projectLeft whatever
