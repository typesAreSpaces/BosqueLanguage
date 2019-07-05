module Gadt_example

noeq type expr : Type -> Type = 
| I : i:int -> expr int
| B : b:bool -> expr bool
| A : expr int -> expr int -> expr int
| E : #a:eqtype -> expr a -> expr a -> expr bool

val f : #a:eqtype -> a -> Tot bool
let f #a n = (n = n)


val eval : expr 'a -> Tot 'a
let rec eval = fun n -> 
match n with
  | I n -> n
  | B b -> b
  | A x y -> eval x + eval y
  | E x y -> eval x = eval y

let _ = assert (eval (E (I 12) (I 12)) = true)


let x = 12

let _ = assert (has_type x int)

val w : Type0
let w = int

let _ = assert (has_type w Type0)
let _ = assert (has_type x int)

type p1 = {x : int; y: bool}
type t = 
// | A1 of ({x : int; y: bool})
| A1 of p1


val g2 : p1 -> int
let g2 x = x.x

let g3 = g2 ({x = 1; y = true})

noeq type ttt = 
| Af of int

let x322323 = Af 12
let x11 = I 12


let _ = assert (has_type x11 (expr int))
let _ = assert (has_type x322323 ttt)

val max : int -> int -> Tot bool
let max x y = if (x >= y) then true else false 
