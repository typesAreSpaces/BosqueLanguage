module Max_example

open FStar.Exn

val max_obvious : int -> int -> int
let max_obvious x y = if (x > y) then x else y

let _ = assert (forall x y . max_obvious x y >= x && max_obvious x y >= y && (max_obvious x y = x || max_obvious x y = y))

val max_control_flow : int -> int -> int
let max_control_flow x y = let tmp_0 = x > y in 
  if (tmp_0) then 
    let return_ = x in 
      return_ 
  else 
    let return_ = y in 
    return_

let _ = assert (forall x y . max_control_flow x y >= x && max_control_flow x y >= y && (max_control_flow x y = x || max_control_flow x y = y))
(* let _ = assert (forall x y . max_control_flow x y = (x + y)) ;; So if something is false, FStar wont be able to prove it! *)

val max_control_flow_2 : int -> int -> int
let max_control_flow_2 x y = let tmp_0 = x > y in 
  if (tmp_0) then 
    let return_1 = x in 
    let return_2 = y in (* This branch is not supposed to know about this variable! *)
      if (tmp_0) then 
        let return_ = return_1 in 
          return_ 
      else 
        let return_ = return_2 in 
          return_ 
  else 
    let return_1 = x in (* This branch is not supposed to know about this variable! *)
    let return_2 = y in 
      if (tmp_0) then 
        let return_ = return_1 in 
          return_ 
      else 
        let return_ = return_2 in 
          return_ 

let _ = assert (forall x y . max_control_flow_2 x y >= x && max_control_flow_2 x y >= y && (max_control_flow_2 x y = x || max_control_flow_2 x y = y))

// val max_control_flow_3 : int -> int -> int
// let max_control_flow_3 x y = let tmp_0 = x > y in 
//   if (tmp_0) then 
//     let return_1 = x in 
//       if (tmp_0) then 
//         let return_ = return_1 in 
//           return_ 
//       else 
//         let return_ = 0 in (* Or any other default value (?) *)
//           return_ 
//   else 
//     let return_2 = y in 
//       if (tmp_0) then 
//         let return_ = 0 in (* Or any other default value (?) *)
//           return_ 
//       else 
//         let return_ = return_2 in 
//           return_ 

// let _ = assert (forall x y . max_control_flow_3 x y >= x && max_control_flow_3 x y >= y && (max_control_flow_3 x y = x || max_control_flow_3 x y = y))
