module NSMain__main_main

open Sequence
open List
open BosqueTypes
open BosqueTerms
open BosqueCollections
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTypedStringType_BnSMain__PlayerMarkType = (BTypedStringType BnSMain__PlayerMarkType)
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))

(* Constant Declarations *)
let nSMain__Baz2__local_const =                         
  let __ir_ret__ = (BInt 1) in
  __ir_ret__

(* Function Declarations *)
val fn--/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/main.bsq%244%0 : (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf BIntType (getType x)})
let fn--/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/main.bsq%244%0 x y = 
  let _ = assert_norm(subtypeOf BIntType (getType y)) in
  let _ = assert_norm(subtypeOf BIntType (getType x)) in
  let __tmp_0 = (op_add x y) in
  let __ir_ret__ = __tmp_0 in
  let _return_ = __ir_ret__ in
  _return_

val nSMain__foo[/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/main.bsq%244%0] : (x:bosqueTerm{subtypeOf bTupleType_2BIntType_BIntTypefalse (getType x)}) -> Tot (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__foo[/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/main.bsq%244%0] a = 
  let _ = assert_norm(subtypeOf bTupleType_2BIntType_BIntTypefalse (getType a)) in
  let __tmp_2 = (nthTuple 0 2 a) in
  let __tmp_3 = (nthTuple 1 2 a) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_3)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_2)) in
  let __tmp_0 = (fn--/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/main.bsq%244%0 __tmp_2 __tmp_3) in
  let __ir_ret__ = __tmp_0 in
  let _return_ = __ir_ret__ in
  _return_

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
  let m_i = (BInt 12) in
  let m_i2 = (BInt 234) in
  let _ = assert_norm(subtypeOf BIntType (getType m_i2)) in
  let _ = assert_norm(subtypeOf BIntType (getType m_i)) in
  let __tmp_6 = (op_eqTerm m_i m_i2) in
  let e_ = __tmp_6 in
  let __tmp_9 = (BTypedString "x" BnSMain__PlayerMarkType) in
  let player2 = __tmp_9 in
  let __tmp_11 = nSMain__Baz2__local_const in
  let _ = assert_norm(subtypeOf BIntType (getType (BInt 1))) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_11)) in
  let __tmp_10 = (op_add __tmp_11 (BInt 1)) in
  let access_example = __tmp_10 in
  let __tmp_15 = (BTuple 2 (SCons (BInt 1) 1 (SCons (BInt 2) 0 SNil))) in
  let _ = assert_norm(subtypeOf bTupleType_2BIntType_BIntTypefalse (getType __tmp_15)) in
  let __tmp_13 = (nSMain__foo[/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/main.bsq%244%0] __tmp_15) in
  let ir = __tmp_13 in
  let __ir_ret__ = (BInt 0) in
  let _return_ = __ir_ret__ in
  _return_

