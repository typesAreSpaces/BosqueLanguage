module NSMain__main_simple_main

open Sequence
open List
open BosqueTypes
open BosqueTerms
open BosqueCollections
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)

(* Constant Declarations *)
let nSMain__Baz__local_const =                         
  let ___ir_ret__ = (BInt 1) in
  ___ir_ret__

(* Default Declarations *)
let nSMain__Baz_zexample_default =                         
  let ___ir_ret__ = (BInt 567) in
  ___ir_ret__

(* Function Declarations *)
val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main  = 
  let __tmp_4 = nSMain__Baz_zexample_default in
  let __tmp_0_arg_3 = __tmp_4 in
  let __tmp_0_arg_2 = (BBool true) in
  let __tmp_0_arg_1 = (BInt 34) in
  let __tmp_0_arg_0 = (BInt 12) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_0_arg_3)) in
  let _ = assert_norm(subtypeOf BBoolType (getType __tmp_0_arg_2)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_0_arg_1)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_0_arg_0)) in
  let __tmp_0 = (BnSMain__Baz __tmp_0_arg_0 __tmp_0_arg_1 __tmp_0_arg_2 __tmp_0_arg_3) in
  let e = __tmp_0 in
  let __tmp_6 = nSMain__Baz__local_const in
  let _ = assert_norm(subtypeOf BIntType (getType (BInt 1))) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_6)) in
  let __tmp_5 = (op_add __tmp_6 (BInt 1)) in
  let access_example = __tmp_5 in
  let ___ir_ret__ = access_example in
  let __return = ___ir_ret__ in
  __return

