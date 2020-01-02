module NSMain__main_main
open Sequence
open BosqueTypes
open BosqueTerms
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTypedStringType_BnSMain__PlayerMarkType = (BTypedStringType BnSMain__PlayerMarkType)
let bTupleType_2BnSMain__PlayerMarkType_bTypedStringType_BnSMain__PlayerMarkTypefalse = BTupleType false 2 (SCons BnSMain__PlayerMarkType 1 (SCons bTypedStringType_BnSMain__PlayerMarkType 0 SNil))
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))
let bTupleType_2BIntType_bTupleType_2BIntType_BIntTypefalsefalse = BTupleType false 2 (SCons BIntType 1 (SCons bTupleType_2BIntType_BIntTypefalse 0 SNil))
let bTupleType_3bTupleType_2BIntType_BIntTypefalse_bTupleType_2BIntType_BIntTypefalse_BIntTypefalse = BTupleType false 3 (SCons bTupleType_2BIntType_BIntTypefalse 2 (SCons bTupleType_2BIntType_BIntTypefalse 1 (SCons BIntType 0 SNil)))
let bTupleType_16BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_bTupleType_2BIntType_BIntTypefalse_bTypedStringType_BAnyType_BBoolType_BBoolTypefalse = BTupleType false 16 (SCons BIntType 15 (SCons BIntType 14 (SCons BIntType 13 (SCons BIntType 12 (SCons BIntType 11 (SCons BIntType 10 (SCons BIntType 9 (SCons BIntType 8 (SCons BIntType 7 (SCons BIntType 6 (SCons BIntType 5 (SCons BIntType 4 (SCons bTupleType_2BIntType_BIntTypefalse 3 (SCons bTypedStringType_BAnyType 2 (SCons BBoolType 1 (SCons BBoolType 0 SNil))))))))))))))))
let bTupleType_3BIntType_BBoolType_bTypedStringType_BAnyTypefalse = BTupleType false 3 (SCons BIntType 2 (SCons BBoolType 1 (SCons bTypedStringType_BAnyType 0 SNil)))
let bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BAnyType = (BUnionType BBoolType (BUnionType BIntType (BUnionType BNoneType bTypedStringType_BAnyType)))
let bUnionType_BIntType_BNoneType = (BUnionType BIntType BNoneType)
let bUnionType_BBoolType_BNoneType = (BUnionType BBoolType BNoneType)
let bUnionType_BBoolType_BIntType_BNoneType = (BUnionType BBoolType (BUnionType BIntType BNoneType))
let bUnionType_BBoolType_BNoneType_BIntType = (BUnionType BBoolType (BUnionType BNoneType BIntType))
let bTupleType_2bTupleType_2BIntType_bTupleType_2BIntType_BIntTypefalsefalse_BIntTypefalse = BTupleType false 2 (SCons bTupleType_2BIntType_bTupleType_2BIntType_BIntTypefalsefalse 1 (SCons BIntType 0 SNil))
let bTupleType_2BIntType_BBoolTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BBoolType 0 SNil))
let bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons bUnionType_BBoolType_BNoneType 0 SNil))

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__max3 : (x:bosqueTerm{subtypeOf bTupleType_2BIntType_BIntTypefalse (getType x)}) -> Tot (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__max3 x = 
  let _ = assert_norm(subtypeOf bTupleType_2BIntType_BIntTypefalse (getType x)) in  let __tmp_3 = (nthTuple 0 2 x) in
  let __tmp_6 = (nthTuple 1 2 x) in
  let _ = assert_norm(subtypeOf BBoolType (getType (op_greaterOrEq __tmp_3 __tmp_6))) in
  let __tmp_0 = (extractBool (op_greaterOrEq __tmp_3 __tmp_6)) in
  if __tmp_0 then 
    let __tmp_9 = (nthTuple 0 2 x) in
    let __ir_ret___1 = __tmp_9 in
    let __ir_ret___2 = __ir_ret___1 in
    let _return_ = __ir_ret___2 in
    _return_
  else 
    let __tmp_12 = (nthTuple 1 2 x) in
    let __ir_ret__ = __tmp_12 in
    let __ir_ret___2 = __ir_ret__ in
    let _return_ = __ir_ret___2 in
    _return_

val nSMain__identityUnion : (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BAnyType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BAnyType (getType x)})
let nSMain__identityUnion x = 
  let __ir_ret__ = x in
  let _return_ = __ir_ret__ in
  _return_

val nSMain__max : (x:bosqueTerm{subtypeOf bUnionType_BIntType_BNoneType (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__max x y = 
  let _ = assert_norm(subtypeOf bUnionType_BIntType_BNoneType (getType x)) in
  let __tmp_0 = (isNone x) in
  if __tmp_0 then 
    let __ir_ret___2 = y in
    let __ir_ret___3 = __ir_ret___2 in
    let _return_ = __ir_ret___3 in
    _return_
  else 
    let _ = assert_norm(subtypeOf BBoolType (getType (op_greaterOrEq x y))) in
    let __tmp_4 = (extractBool (op_greaterOrEq x y)) in
    if __tmp_4 then 
      let __ir_ret___1 = x in
      let __ir_ret___3 = __ir_ret___1 in
      let _return_ = __ir_ret___3 in
      _return_
    else 
      let __ir_ret__ = y in
      let __ir_ret___3 = __ir_ret__ in
      let _return_ = __ir_ret___3 in
      _return_

val nSMain__maxx : (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BNoneType (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType (getType x)})
let nSMain__maxx x y = 
  let _ = assert_norm(subtypeOf BBoolType (getType (op_greater y (BInt 0)))) in
  let __tmp_0 = (extractBool (op_greater y (BInt 0))) in
  if __tmp_0 then 
    let __ir_ret___1 = x in
    let __ir_ret___2 = __ir_ret___1 in
    let _return_ = __ir_ret___2 in
    _return_
  else 
    let __ir_ret__ = y in
    let __ir_ret___2 = __ir_ret__ in
    let _return_ = __ir_ret___2 in
    _return_

val nSMain__identityTupleNoneable : (x:bosqueTerm{subtypeOf bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse (getType x)})
let nSMain__identityTupleNoneable x = 
  let __ir_ret__ = x in
  let _return_ = __ir_ret__ in
  _return_

val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main  = 
  let string_test = (BTypedString "string_test" BAnyType) in
  let __tmp_6_arg_0 = (BTypedString "o" BAnyType) in
  let _ = assert_norm(subtypeOf bTypedStringType_BAnyType (getType __tmp_6_arg_0)) in
  let __tmp_6 = (BnSMain__PlayerMark __tmp_6_arg_0) in
  let __tmp_1_arg_4 = __tmp_6 in
  let __tmp_1_arg_3 = (BTypedString "Chris" BAnyType) in
  let __tmp_1_arg_2 = (BTypedString "Cornell" BAnyType) in
  let __tmp_1_arg_1 = (BBool true) in
  let __tmp_1_arg_0 = (BInt 100) in
  let _ = assert_norm(subtypeOf BnSMain__PlayerMarkType (getType __tmp_1_arg_4)) in
  let _ = assert_norm(subtypeOf bTypedStringType_BAnyType (getType __tmp_1_arg_3)) in
  let _ = assert_norm(subtypeOf bTypedStringType_BAnyType (getType __tmp_1_arg_2)) in
  let _ = assert_norm(subtypeOf BBoolType (getType __tmp_1_arg_1)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_1_arg_0)) in
  let __tmp_1 = (BnSMain__Artist __tmp_1_arg_0 __tmp_1_arg_1 __tmp_1_arg_2 __tmp_1_arg_3 __tmp_1_arg_4) in
  let chris = __tmp_1 in
  let __tmp_8_arg_1 = (BTypedString "Guitar" BAnyType) in
  let __tmp_8_arg_0 = chris in
  let _ = assert_norm(subtypeOf bTypedStringType_BAnyType (getType __tmp_8_arg_1)) in
  let _ = assert_norm(subtypeOf BnSMain__ArtistType (getType __tmp_8_arg_0)) in
  let __tmp_8 = (BnSMain__Musician __tmp_8_arg_0 __tmp_8_arg_1) in
  let chris_but_musician = __tmp_8 in
  let __tmp_11_arg_0 = (BTypedString "x" BAnyType) in
  let _ = assert_norm(subtypeOf bTypedStringType_BAnyType (getType __tmp_11_arg_0)) in
  let __tmp_11 = (BnSMain__PlayerMark __tmp_11_arg_0) in
  let player1 = __tmp_11 in
  let __tmp_13 = (BTypedString "x" BnSMain__PlayerMarkType) in
  let player2 = __tmp_13 in
  let __tmp_14 = (BTypedString "hmm" BnSMain__PlayerMarkType) in
  let player3 = __tmp_14 in
  let __tmp_15_arg_4 = player1 in
  let __tmp_15_arg_3 = (BTypedString "Peter" BAnyType) in
  let __tmp_15_arg_2 = (BTypedString "Pan" BAnyType) in
  let __tmp_15_arg_1 = (BBool true) in
  let __tmp_15_arg_0 = (BInt 100) in
  let _ = assert_norm(subtypeOf BnSMain__PlayerMarkType (getType __tmp_15_arg_4)) in
  let _ = assert_norm(subtypeOf bTypedStringType_BAnyType (getType __tmp_15_arg_3)) in
  let _ = assert_norm(subtypeOf bTypedStringType_BAnyType (getType __tmp_15_arg_2)) in
  let _ = assert_norm(subtypeOf BBoolType (getType __tmp_15_arg_1)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_15_arg_0)) in
  let __tmp_15 = (BnSMain__Artist __tmp_15_arg_0 __tmp_15_arg_1 __tmp_15_arg_2 __tmp_15_arg_3 __tmp_15_arg_4) in
  let artist1 = __tmp_15 in
  let __tmp_21_arg_4 = player1 in
  let __tmp_21_arg_3 = (BTypedString "Chris" BAnyType) in
  let __tmp_21_arg_2 = (BTypedString "Cornell" BAnyType) in
  let __tmp_21_arg_1 = (BBool true) in
  let __tmp_21_arg_0 = (BInt 100) in
  let _ = assert_norm(subtypeOf BnSMain__PlayerMarkType (getType __tmp_21_arg_4)) in
  let _ = assert_norm(subtypeOf bTypedStringType_BAnyType (getType __tmp_21_arg_3)) in
  let _ = assert_norm(subtypeOf bTypedStringType_BAnyType (getType __tmp_21_arg_2)) in
  let _ = assert_norm(subtypeOf BBoolType (getType __tmp_21_arg_1)) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_21_arg_0)) in
  let __tmp_21 = (BnSMain__Artist __tmp_21_arg_0 __tmp_21_arg_1 __tmp_21_arg_2 __tmp_21_arg_3 __tmp_21_arg_4) in
  let artist2 = __tmp_21 in
  let __tmp_27 = (BTuple 2 (SCons player1 1 (SCons player2 0 SNil))) in
  let player_tuple = __tmp_27 in
  let n = BNone in
  let __tmp_31 = (BTuple 2 (SCons (BInt 10) 1 (SCons (BInt 30) 0 SNil))) in
  let xTuple = __tmp_31 in
  let __tmp_34 = (BTuple 2 (SCons (BInt 10) 1 (SCons xTuple 0 SNil))) in
  let xTuple2 = __tmp_34 in
  let __tmp_39 = (BTuple 2 (SCons (BInt 10) 1 (SCons (BInt 3) 0 SNil))) in
  let __tmp_37 = (BTuple 2 (SCons (BInt 10) 1 (SCons __tmp_39 0 SNil))) in
  let xTuple3 = __tmp_37 in
  let _ = assert_norm(subtypeOf bTupleType_2BIntType_bTupleType_2BIntType_BIntTypefalsefalse (getType xTuple2)) in  let __tmp_44 = (nthTuple 1 2 xTuple2) in
  let xTupleProj = __tmp_44 in
  let _ = assert_norm(subtypeOf bTupleType_2BIntType_bTupleType_2BIntType_BIntTypefalsefalse (getType xTuple3)) in  let __tmp_47 = (nthTuple 1 2 xTuple3) in
  let xTupleProj2 = __tmp_47 in
  let _ = assert_norm(subtypeOf bTupleType_2BIntType_BIntTypefalse (getType xTupleProj)) in
  let __tmp_48 = (nSMain__max3 xTupleProj) in
  let x_max_tuple = __tmp_48 in
  let _ = assert_norm(subtypeOf bTupleType_2BIntType_BIntTypefalse (getType xTupleProj2)) in
  let __tmp_50 = (nSMain__max3 xTupleProj2) in
  let x_max_tuple2 = __tmp_50 in
  let __tmp_54 = (BTuple 2 (SCons (BInt 1) 1 (SCons (BInt 2) 0 SNil))) in
  let __tmp_57 = (BTuple 2 (SCons (BInt 3) 1 (SCons (BInt 4) 0 SNil))) in
  let __tmp_53 = (BTuple 3 (SCons __tmp_54 2 (SCons __tmp_57 1 (SCons (BInt 5) 0 SNil)))) in
  let _ = assert_norm(subtypeOf bTupleType_3bTupleType_2BIntType_BIntTypefalse_bTupleType_2BIntType_BIntTypefalse_BIntTypefalse (getType __tmp_53)) in  let __tmp_61 = (nthTuple 2 3 __tmp_53) in
  let proj_tuple = __tmp_61 in
  let __tmp_75 = (BTuple 2 (SCons (BInt 1) 1 (SCons (BInt 1) 0 SNil))) in
  let __tmp_62 = (BTuple 16 (SCons (BInt 1) 15 (SCons (BInt 1) 14 (SCons (BInt 1) 13 (SCons (BInt 1) 12 (SCons (BInt 1) 11 (SCons (BInt 1) 10 (SCons (BInt 1) 9 (SCons (BInt 1) 8 (SCons (BInt 1) 7 (SCons (BInt 1) 6 (SCons (BInt 1) 5 (SCons (BInt 1) 4 (SCons __tmp_75 3 (SCons (BTypedString "hello" BAnyType) 2 (SCons (BBool false) 1 (SCons (BBool true) 0 SNil))))))))))))))))) in
  let xTuple4 = __tmp_62 in
  let __tmp_81 = (BTuple 3 (SCons (BInt 10) 2 (SCons (BBool false) 1 (SCons (BTypedString "hello" BAnyType) 0 SNil)))) in
  let hmm_tuple = __tmp_81 in
  let y = (BInt 20) in
  let _ = assert_norm(subtypeOf BIntType (getType y)) in
  let __tmp_86 = (nSMain__identityUnion y) in
  let y2 = __tmp_86 in
  let __tmp_91 = (nthTuple 0 2 xTuple2) in
  let _ = assert_norm(subtypeOf BIntType (getType __tmp_91)) in
  let __tmp_88 = (nSMain__max __tmp_91 y) in
  let z = __tmp_88 in
  let _ = assert_norm(subtypeOf BIntType (getType z)) in
  let __tmp_93 = (nSMain__max z y) in
  let z_max_func_repeated = __tmp_93 in
  let _ = assert_norm(subtypeOf BIntType (getType (BInt 3))) in
  let _ = assert_norm(subtypeOf BBoolType (getType (BBool false))) in
  let __tmp_96 = (nSMain__maxx (BBool false) (BInt 3)) in
  let z4 = __tmp_96 in
  let __tmp_99 = (BTuple 2 (SCons xTuple2 1 (SCons y 0 SNil))) in
  let zTuple = __tmp_99 in
  let __tmp_103 = (BTuple 2 (SCons y 1 (SCons (BBool false) 0 SNil))) in
  let _ = assert_norm(subtypeOf bTupleType_2BIntType_BBoolTypefalse (getType __tmp_103)) in
  let __tmp_102 = (nSMain__identityTupleNoneable __tmp_103) in
  let z5 = __tmp_102 in
  let __ir_ret__ = z_max_func_repeated in
  let _return_ = __ir_ret__ in
  _return_

