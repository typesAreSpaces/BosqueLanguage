module What

open FStar.String

let _ = assert_norm (length "" = 0)

let _ = assert_norm (strlen "" = 0)

type tuple_2 (t_1:Type) (t_2:Type) = 
 | Mktuple_2: _1: t_1 -> _2: t_2 -> tuple_2 t_1 t_2

type tuple_intint = 
 | Mktuple_intint: _1: int -> _2: int -> tuple_intint
 
type what = 
| Mkwhat : _1:int -> _2: tuple_intint -> what

let x = Mktuple_2 1 2
let x_ = Mktuple_2 1 (Mktuple_2 1 2)
let x2 = Mktuple_intint 1 2
let x3 = Mkwhat 1 (Mktuple_intint 1 2)
let x4 = Mktuple_2?._1 x_
val f : (tuple_2 int int) -> int

type record_2 (t_1:Type) (t_2:Type) = 
| Mkrecord_2 : g : t_1 -> f : t_2 -> record_2 t_1 t_2

let y = Mkrecord_2 1 2
let y_ = Mkrecord_2?.f y

val g : (record_2 int int) -> int


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

val ffff : int -> x:int{x>=0}
let ffff x = if (x >= 1) then x else -x + 1

type uniontype_bool_int : Type -> Type = 
| Intuniontype_bool_int : i:int -> uniontype_bool_int int
| Booluniontype_bool_int : i:bool -> uniontype_bool_int bool

val extractInt : uniontype_bool_int int -> int
let extractInt x = match x with 
| Intuniontype_bool_int i -> i
| Booluniontype_bool_int _ -> 0
  

let xx = Intuniontype_bool_int 13


let x__ = Intuniontype_int_bool 1


type record_2again (t_1:Type) (t_2:Type) = 
| Mkrecord_2again : g : t_1 -> f : t_2 -> record_2again t_1 t_2

val f2 : (record_2 int int) -> int
let f2 x = Mkrecord_2?.f x



let y23423948 = (1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1)

let _ = assert (x = y)

let x = tuple

let constructorTuple x y = (x, y)

let (x, _) = constructorTuple 1 2
