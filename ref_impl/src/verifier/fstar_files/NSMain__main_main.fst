module NSMain__main_main
open Sequence
open BosqueTypes
open BosqueTerms
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bRecordType_3BBoolType_BIntType_bTypedStringType_BAnyTypefalse = BRecordType false 3 (SCons "f" 2 (SCons "g" 1 (SCons "h" 0 SNil))) (SCons BBoolType 2 (SCons BIntType 1 (SCons bTypedStringType_BAnyType 0 SNil)))
let bRecordType_2BBoolType_BIntTypefalse = BRecordType false 2 (SCons "f" 1 (SCons "g" 0 SNil)) (SCons BBoolType 1 (SCons BIntType 0 SNil))
let bRecordType_2BIntType_BBoolTypefalse = BRecordType false 2 (SCons "f" 1 (SCons "k" 0 SNil)) (SCons BIntType 1 (SCons BBoolType 0 SNil))

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main  = 
  let __tmp_0 = (BRecord 3 (SCons "f" 2 (SCons "g" 1 (SCons "h" 0 SNil))) (SCons (BBool true) 2 (SCons (BInt 2) 1 (SCons (BTypedString "hello" BAnyType) 0 SNil)))) in
  let xRecord = __tmp_0 in
  let _ = assert_norm(subtypeOf bRecordType_3BBoolType_BIntType_bTypedStringType_BAnyTypefalse (getType xRecord)) in
  let __tmp_6 = (nthRecord "g" 3 xRecord) in
  let x_ProjectedRecord = __tmp_6 in
  let __fresh_name1NSMain__main = (nthRecord "g" 3 xRecord) in
  let __fresh_name0NSMain__main = (nthRecord "f" 3 xRecord) in
  let __tmp_9 = (BRecord 2 (SCons "f" 1 (SCons "g" 0 SNil)) (SCons __fresh_name0NSMain__main 1 (SCons __fresh_name1NSMain__main 0 SNil))) in
  let x = __tmp_9 in
  let __tmp_10_arg_2 = (BBool true) in
  let __tmp_10_arg_1 = (BInt 2) in
  let __tmp_10_arg_0 = (BInt 1) in
  let _ = assert_norm(subtypeOf BBoolType (getType __tmp_10_arg_2)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_10_arg_1)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_10_arg_0)) in
  let __tmp_10 = (BnSMain__Baz2 __tmp_10_arg_0 __tmp_10_arg_1 __tmp_10_arg_2) in
  let e = __tmp_10 in
  let _ = assert_norm(subtypeOf BnSMain__Baz2Type (getType e)) in
  let __tmp_16 = (projectBnSMain__Baz2_f e) in
  let e2 = __tmp_16 in
  let __fresh_name1NSMain__main = (projectBnSMain__Baz2_k e) in
  let __fresh_name0NSMain__main = (projectBnSMain__Baz2_f e) in
  let __tmp_19 = (BRecord 2 (SCons "f" 1 (SCons "k" 0 SNil)) (SCons __fresh_name0NSMain__main 1 (SCons __fresh_name1NSMain__main 0 SNil))) in
  let e3 = __tmp_19 in
  let _MIRProjectFromTypeConcept = (BInt 0) in
  let e4 = __tmp_22 in
  let __ir_ret__ = e2 in
  let _return_ = __ir_ret__ in
  _return_

