module NSMain__main_main

open Sequence
open List
open BosqueTypes
open BosqueTerms
open BosqueCollections
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))

(* Constant Declarations *)
let nSMain__Baz2__local_const =                         
  let ___ir_ret__ = (BInt 1) in
  ___ir_ret__

(* Default Declarations *)
let nSMain__Baz2_zexample_default =                         
  let ___ir_ret__ = (BInt 567) in
  ___ir_ret__

(* Function Declarations *)
val nSMain__emptyArgs : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__emptyArgs  = 
  let ___ir_ret__ = (BInt 0) in
  let __return = ___ir_ret__ in
  __return

val fn___home_jose_Documents_GithubProjects_BosqueLanguage_impl_src_test_apps_max_main_bsq_235_0 : (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf BIntType (getType x)})
let fn___home_jose_Documents_GithubProjects_BosqueLanguage_impl_src_test_apps_max_main_bsq_235_0 x y __c_access_example = 
  let _ = assert_norm(subtypeOf BIntType (getType __c_access_example)) in
  let _ = assert_norm(subtypeOf BIntType (getType y)) in
  let __tmp_2 = (op_add y __c_access_example) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_2)) in
  let _ = assert_norm(subtypeOf BIntType (getType x)) in
  let __tmp_0 = (op_add x __tmp_2) in
  let ___ir_ret__ = __tmp_0 in
  let __return = ___ir_ret__ in
  __return

val nSMain__foo__home_jose_Documents_GithubProjects_BosqueLanguage_impl_src_test_apps_max_main_bsq_235_0_ : (x:bosqueTerm{subtypeOf bTupleType_2BIntType_BIntTypefalse (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__foo__home_jose_Documents_GithubProjects_BosqueLanguage_impl_src_test_apps_max_main_bsq_235_0_ a __c_access_example = 
  let _ = assert_norm(subtypeOf bTupleType_2BIntType_BIntTypefalse (getType a)) in
  let __tmp_3 = (nthTuple 0 2 a) in
  let __tmp_4 = (nthTuple 1 2 a) in
  let _ = assert_norm(subtypeOf BIntType (getType __c_access_example)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_4)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_3)) in
  let __tmp_0 = (fn___home_jose_Documents_GithubProjects_BosqueLanguage_impl_src_test_apps_max_main_bsq_235_0 __tmp_3 __tmp_4 __c_access_example) in
  let ___ir_ret__ = __tmp_0 in
  let __return = ___ir_ret__ in
  __return

val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main  = 
  let __tmp_4 = nSMain__Baz2_zexample_default in
  let __tmp_0_arg_3 = (BInt 12) in
  let __tmp_0_arg_2 = __tmp_4 in
  let __tmp_0_arg_1 = (BBool true) in
  let __tmp_0_arg_0 = (BInt 34) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_0_arg_3)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_0_arg_2)) in
  let _ = assert_norm(subtypeOf BBoolType (getType __tmp_0_arg_1)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_0_arg_0)) in
  let __tmp_0 = (BnSMain__Baz2 __tmp_0_arg_0 __tmp_0_arg_1 __tmp_0_arg_2 __tmp_0_arg_3) in
  let e = __tmp_0 in
  let _ = assert_norm(subtypeOf BnSMain__Baz2Type (getType e)) in
  let __tmp_7 = (projectBnSMain__Baz2_f e) in
  let e_f = __tmp_7 in
  let __tmp_9 = nSMain__Baz2__local_const in
  let _ = assert_norm(subtypeOf BIntType (getType (BInt 1))) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_9)) in
  let __tmp_8 = (op_add __tmp_9 (BInt 1)) in
  let access_example = __tmp_8 in
  let __tmp_11 = (nSMain__emptyArgs ) in
  let empty_args_test = __tmp_11 in
  let __tmp_14 = (BTuple 2 (SCons (BInt 1) 1 (SCons (BInt 2) 0 SNil))) in
  let _ = assert_norm(subtypeOf BIntType (getType access_example)) in
  let _ = assert_norm(subtypeOf bTupleType_2BIntType_BIntTypefalse (getType __tmp_14)) in
  let __tmp_12 = (nSMain__foo__home_jose_Documents_GithubProjects_BosqueLanguage_impl_src_test_apps_max_main_bsq_235_0_ __tmp_14 access_example) in
  let ir = __tmp_12 in
  let ___ir_ret__ = (BInt 0) in
  let __return = ___ir_ret__ in
  __return

