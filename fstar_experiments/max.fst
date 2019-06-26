module Max

open FStar.All
open FStar.Exn

val max_example : int -> int -> int
let max_example x y = if (x > y) then x else y

let _ = assert (forall x y . max_example x y >= x && max_example x y >= y && (max_example x y = x || max_example x y = y))

val max_control_flow : int -> int -> int
let max_control_flow x y = let tmp_0 = x > y in if (tmp_0) then let return_ = x in return_ else let return_ = y in return_

let _ = assert (forall x y . max_control_flow x y >= x && max_control_flow x y >= y && (max_control_flow x y = x || max_control_flow x y = y))
(*let _ = assert (forall x y . max_control_flow x y = (x + y)) ;; So if something is false, FStar wont be able to prove it!*)

exception What
val max_control_flow_2 : int -> int -> int
let max_control_flow_2 x y = let tmp_0 = x > y in 
  if (tmp_0) then 
    let return_1 = x in 
    let return_2 = y in
      if (tmp_0) then 
        let return_ = return_1 in 
          return_ 
      else 
        let return_ = return_2 in 
          return_ 
  else 
    let return_1 = x in
    let return_2 = y in 
          if (tmp_0) then 
        let return_ = return_1 in 
          return_ 
      else 
        let return_ = return_2 in 
          return_ 

let _ = assert (forall x y . max_control_flow_2 x y >= x && max_control_flow_2 x y >= y && (max_control_flow_2 x y = x || max_control_flow_2 x y = y))

exception InvalidCondition
val dummy_example : int -> ML int
let dummy_example n = if (true) then n else raise InvalidCondition

let _ = assert (forall x . dummy_example x = x)


