module NSMain__main_main
open Sequence
open BosqueTypes
open BosqueTerms
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bRecordType_2fBIntType_gBIntTypefalse = BRecordType false 2 (SCons "f" 1 (SCons "g" 0 SNil)) (SCons BIntType 1 (SCons BIntType 0 SNil))

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main  = 
  let __tmp_0 = (BRecord 2 (SCons "f" 1 (SCons "g" 0 SNil)) (SCons (BInt 1) 1 (SCons (BInt 2) 0 SNil))) in
  let xRecord = __tmp_0 in
  let _ = assert_norm(subtypeOf bRecordType_2fBIntType_gBIntTypefalse (getType xRecord)) in
  let __tmp_5 = (nthRecord "f" 2 xRecord) in
  let x_ProjectedRecord = __tmp_5 in
  let __ir_ret__ = x_ProjectedRecord in
  let _return_ = __ir_ret__ in
  _return_

