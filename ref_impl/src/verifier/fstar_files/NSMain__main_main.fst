module NSMain__main_main

open Sequence
open List
open BosqueTypes
open BosqueTerms
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main  = 
  let __tmp_0_arg_2 = (BBool true) in
  let __tmp_0_arg_1 = (BInt 2) in
  let __tmp_0_arg_0 = (BInt 1) in
  let _ = assert_norm(subtypeOf BBoolType (getType __tmp_0_arg_2)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_0_arg_1)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_0_arg_0)) in
  let __tmp_0 = (BnSMain__Baz2 __tmp_0_arg_0 __tmp_0_arg_1 __tmp_0_arg_2) in
  let e = __tmp_0 in
  let __ir_ret__ = (BInt 0) in
  let _return_ = __ir_ret__ in
  _return_

