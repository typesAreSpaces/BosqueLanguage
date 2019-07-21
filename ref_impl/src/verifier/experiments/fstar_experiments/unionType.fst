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

val test2_1 : utib2 int -> Tot bool
let test2_1 n = if (n >= 0) then true else if (n < 0) then false else n

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

type unionIntBool = 
| Intt : x:int -> unionIntBool
| Booll: x:bool -> unionIntBool

val test4 : unionIntBool -> Tot int
let test4 x = match x with
| Intt n -> n
| Booll _ -> 0

let ahh __NSMain__max0____tmp_0 __NSMain__max0___return_ = if (op_Equality __NSMain__max0____tmp_0 true) then let temporal = 0 in let temporal = 0 in let temporal = 0 in let temporal = 0 in __NSMain__max0___return_ else let temporal
 = 0 in let temporal = 0 in let temporal = 0 in let temporal = 0 in __NSMain__max0___return_

let max2 x y = let __tmp_0 = (op_GreaterThanOrEqual x y) in if (op_Equality __tmp_0 true) then let _ir_ret__1 = x in let _ir_ret__2 = _ir_ret__1 in let _return_ = _ir_ret__2 in _return_ else let _ir_ret_ = y in let _ir_ret__2 = _ir_ret_ in let _return_ = _ir_ret__2 in _return_

let x_1 = 1


let _ = assert (has_type x_1 int)



let sdsdf = if (has_type x_1 int) then 1 else 0


