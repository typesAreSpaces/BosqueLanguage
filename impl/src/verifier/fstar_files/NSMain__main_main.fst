module NSMain__main_main

open Sequence
open List
open BosqueTypes
open BosqueTerms
open BosqueCollections
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)

(* Constant Declarations *)
let nSMain__Baz2__local_const =                         
  let ___ir_ret__ = (BInt 1) in
  ___ir_ret__

(* Function Declarations *)
val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main  = 
  let __tmp_1 = nSMain__Baz2__local_const in
  let _ = assert_norm(subtypeOf BIntType (getType (BInt 1))) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_1)) in
  let __tmp_0 = (op_add __tmp_1 (BInt 1)) in
  let access_example = __tmp_0 in
  let ___ir_ret__ = (BInt 0) in
  let __return = ___ir_ret__ in
  __return

