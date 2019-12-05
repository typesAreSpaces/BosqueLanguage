module NSMain__main_main
open Sequence
open BosqueTypes
open BosqueTerms
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))
let bTupleType_2BIntType_bTupleType_2BIntType_BIntTypefalsefalse = BTupleType false 2 (SCons BIntType 1 (SCons bTupleType_2BIntType_BIntTypefalse 0 SNil))
let bTupleType_3bTupleType_2BIntType_BIntTypefalse_bTupleType_2BIntType_BIntTypefalse_BIntTypefalse = BTupleType false 3 (SCons bTupleType_2BIntType_BIntTypefalse 2 (SCons bTupleType_2BIntType_BIntTypefalse 1 (SCons BIntType 0 SNil)))
let bTupleType_16BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_bTupleType_2BIntType_BIntTypefalse_bTypedStringType_BAnyType_BBoolType_BBoolTypefalse = BTupleType false 16 (SCons BIntType 15 (SCons BIntType 14 (SCons BIntType 13 (SCons BIntType 12 (SCons BIntType 11 (SCons BIntType 10 (SCons BIntType 9 (SCons BIntType 8 (SCons BIntType 7 (SCons BIntType 6 (SCons BIntType 5 (SCons BIntType 4 (SCons bTupleType_2BIntType_BIntTypefalse 3 (SCons bTypedStringType_BAnyType 2 (SCons BBoolType 1 (SCons BBoolType 0 SNil))))))))))))))))
let bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BAnyType = (BUnionType BBoolType (BUnionType BIntType (BUnionType BNoneType bTypedStringType_BAnyType)))
let bUnionType_BIntType_BNoneType = (BUnionType BIntType BNoneType)
let bTupleType_3BIntType_BBoolType_BIntTypefalse = BTupleType false 3 (SCons BIntType 2 (SCons BBoolType 1 (SCons BIntType 0 SNil)))
let bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue = BTupleType true 4 (SCons BIntType 3 (SCons BBoolType 2 (SCons BIntType 1 (SCons BBoolType 0 SNil))))
let bUnionType_bTupleType_3BIntType_BBoolType_BIntTypefalse_bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue = (BUnionType bTupleType_3BIntType_BBoolType_BIntTypefalse bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue)
let bTupleType_1bTypedStringType_BAnyTypefalse = BTupleType false 1 (SCons bTypedStringType_BAnyType 0 SNil)
let bTupleType_1bTypedStringType_BAnyTypetrue = BTupleType true 1 (SCons bTypedStringType_BAnyType 0 SNil)
let bUnionType_BBoolType_BNoneType = (BUnionType BBoolType BNoneType)
let bUnionType_BBoolType_BIntType_BNoneType = (BUnionType BBoolType (BUnionType BIntType BNoneType))
let bUnionType_BBoolType_BNoneType_BIntType = (BUnionType BBoolType (BUnionType BNoneType BIntType))
let bTupleType_2bTupleType_2BIntType_BIntTypefalse_BIntTypefalse = BTupleType false 2 (SCons bTupleType_2BIntType_BIntTypefalse 1 (SCons BIntType 0 SNil))
let bTupleType_2BIntType_BBoolTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BBoolType 0 SNil))
let bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons bUnionType_BBoolType_BNoneType 0 SNil))

(* Concept Declarations *)

(* Entity Declarations *)
type nSMain__Musician = 
| BnSMain__Musician : artist : nSMain__Artist -> 
instrument : bosqueTerm{bTypedStringType_BAnyType = (getType instrument)} -> 
nSMain__Musician
type nSMain__Artist = 
| BnSMain__Artist : id : bosqueTerm{BIntType = (getType id)} -> 
isGood : bosqueTerm{BBoolType = (getType isGood)} -> 
lastName : bosqueTerm{bTypedStringType_BAnyType = (getType lastName)} -> 
name : bosqueTerm{bTypedStringType_BAnyType = (getType name)} -> 
player : nSMain__PlayerMark -> 
nSMain__Artist
type nSMain__PlayerMark = 
| BnSMain__PlayerMark : mark : bosqueTerm{bTypedStringType_BAnyType = (getType mark)} -> 
nSMain__PlayerMark

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__max3 : (x:bosqueTerm{subtypeOf bTupleType_2BIntType_BIntTypefalse (getType x)}) -> Tot (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__max3 x = 
 let __tmp_3 = (cast (bosqueTerm) (x:bosqueTerm{BIntType=(getType x)}) (nthTuple 0 2 x)) in 
  let __tmp_6 = (cast (bosqueTerm) (x:bosqueTerm{BIntType=(getType x)}) (nthTuple 1 2 x)) in 
   let __tmp_0 = (extractBool (op_greaterOrEq __tmp_3 __tmp_6)) in 
    if __tmp_0 then 
     let __tmp_9 = (cast (bosqueTerm) (x:bosqueTerm{BIntType=(getType x)}) (nthTuple 0 2 x)) in 
      let __ir_ret___1 = __tmp_9 in 
       let __ir_ret___2 = __ir_ret___1 in 
        let _return_ = __ir_ret___2 in 
         _return_
    else 
     let __tmp_12 = (cast (bosqueTerm) (x:bosqueTerm{BIntType=(getType x)}) (nthTuple 1 2 x)) in 
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
 let __tmp_0 = (isNone x) in 
  if __tmp_0 then 
   let __ir_ret___2 = y in 
    let __ir_ret___3 = __ir_ret___2 in 
     let _return_ = __ir_ret___3 in 
      _return_
  else 
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

val nSMain__identityTupleOptional : (x:bosqueTerm{subtypeOf bUnionType_bTupleType_3BIntType_BBoolType_BIntTypefalse_bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bUnionType_bTupleType_3BIntType_BBoolType_BIntTypefalse_bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue (getType x)})
let nSMain__identityTupleOptional x = 
 let __ir_ret__ = x in 
  let _return_ = __ir_ret__ in 
   _return_

val nSMain__identityOpenTuple : (x:bosqueTerm{subtypeOf bTupleType_1bTypedStringType_BAnyTypetrue (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bTupleType_1bTypedStringType_BAnyTypetrue (getType x)})
let nSMain__identityOpenTuple x = 
 let __ir_ret__ = x in 
  let _return_ = __ir_ret__ in 
   _return_

val nSMain__maxx : (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BNoneType (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType (getType x)})
let nSMain__maxx x y = 
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
   let __tmp_6 = (BnSMain__PlayerMark __tmp_6_arg_0) in 
    let __tmp_1_arg_4 = __tmp_6 in 
     let __tmp_1_arg_3 = (BTypedString "Chris" BAnyType) in 
      let __tmp_1_arg_2 = (BTypedString "Cornell" BAnyType) in 
       let __tmp_1_arg_1 = (BBool true) in 
        let __tmp_1_arg_0 = (BInt 100) in 
         let __tmp_1 = (BnSMain__Artist __tmp_1_arg_0 __tmp_1_arg_1 __tmp_1_arg_2 __tmp_1_arg_3 __tmp_1_arg_4) in 
          let node = __tmp_1 in 
           let __tmp_8_arg_1 = (BTypedString "Guitar" BAnyType) in 
            let __tmp_8_arg_0 = node in 
             let __tmp_8 = (BnSMain__Musician __tmp_8_arg_0 __tmp_8_arg_1) in 
              let musician = __tmp_8 in 
               let __tmp_11_arg_0 = (BTypedString "x" BAnyType) in 
                let __tmp_11 = (BnSMain__PlayerMark __tmp_11_arg_0) in 
                 let player1 = __tmp_11 in 
                  let __tmp_13 = (BInt 0) in 
                   let player2 = __tmp_13 in 
                    let __tmp_14_arg_4 = player1 in 
                     let __tmp_14_arg_3 = (BTypedString "Peter" BAnyType) in 
                      let __tmp_14_arg_2 = (BTypedString "Pan" BAnyType) in 
                       let __tmp_14_arg_1 = (BBool true) in 
                        let __tmp_14_arg_0 = (BInt 100) in 
                         let __tmp_14 = (BnSMain__Artist __tmp_14_arg_0 __tmp_14_arg_1 __tmp_14_arg_2 __tmp_14_arg_3 __tmp_14_arg_4) in 
                          let node1 = __tmp_14 in 
                           let __tmp_20_arg_4 = player1 in 
                            let __tmp_20_arg_3 = (BTypedString "Chris" BAnyType) in 
                             let __tmp_20_arg_2 = (BTypedString "Cornell" BAnyType) in 
                              let __tmp_20_arg_1 = (BBool true) in 
                               let __tmp_20_arg_0 = (BInt 100) in 
                                let __tmp_20 = (BnSMain__Artist __tmp_20_arg_0 __tmp_20_arg_1 __tmp_20_arg_2 __tmp_20_arg_3 __tmp_20_arg_4) in 
                                 let node2 = __tmp_20 in 
                                  let n = BNone in 
                                   let __tmp_27 = (BTuple 2 (SCons (BInt 10) 1 (SCons (BInt 30) 0 SNil))) in 
                                    let xTuple2 = __tmp_27 in 
                                     let __tmp_30 = (BTuple 2 (SCons (BInt 10) 1 (SCons xTuple2 0 SNil))) in 
                                      let xTuple2_1 = __tmp_30 in 
                                       let __tmp_35 = (BTuple 2 (SCons (BInt 10) 1 (SCons (BInt 3) 0 SNil))) in 
                                        let __tmp_33 = (BTuple 2 (SCons (BInt 10) 1 (SCons __tmp_35 0 SNil))) in 
                                         let xTuple2_2 = __tmp_33 in 
                                          let __tmp_40 = (cast (bosqueTerm) (x:bosqueTerm{bTupleType_2BIntType_BIntTypefalse=(getType x)}) (nthTuple 1 2 xTuple2_1)) in 
                                           let xTuple_second = __tmp_40 in 
                                            let __tmp_43 = (cast (bosqueTerm) (x:bosqueTerm{bTupleType_2BIntType_BIntTypefalse=(getType x)}) (nthTuple 1 2 xTuple2_2)) in 
                                             let xTuple_second_ = __tmp_43 in 
                                              let __tmp_44 = (nSMain__max3 xTuple_second) in 
                                               let x_max_tuple = __tmp_44 in 
                                                let __tmp_46 = (nSMain__max3 xTuple_second_) in 
                                                 let x_max_tuple_ = __tmp_46 in 
                                                  let __tmp_50 = (BTuple 2 (SCons (BInt 1) 1 (SCons (BInt 2) 0 SNil))) in 
                                                   let __tmp_53 = (BTuple 2 (SCons (BInt 3) 1 (SCons (BInt 4) 0 SNil))) in 
                                                    let __tmp_49 = (BTuple 3 (SCons __tmp_50 2 (SCons __tmp_53 1 (SCons (BInt 5) 0 SNil)))) in 
                                                     let __tmp_57 = (cast (bosqueTerm) (x:bosqueTerm{BIntType=(getType x)}) (nthTuple 2 3 __tmp_49)) in 
                                                      let proj_tuple = __tmp_57 in 
                                                       let __tmp_71 = (BTuple 2 (SCons (BInt 1) 1 (SCons (BInt 1) 0 SNil))) in 
                                                        let __tmp_58 = (BTuple 16 (SCons (BInt 1) 15 (SCons (BInt 1) 14 (SCons (BInt 1) 13 (SCons (BInt 1) 12 (SCons (BInt 1) 11 (SCons (BInt 1) 10 (SCons (BInt 1) 9 (SCons (BInt 1) 8 (SCons (BInt 1) 7 (SCons (BInt 1) 6 (SCons (BInt 1) 5 (SCons (BInt 1) 4 (SCons __tmp_71 3 (SCons (BTypedString "hello" BAnyType) 2 (SCons (BBool false) 1 (SCons (BBool true) 0 SNil))))))))))))))))) in 
                                                         let x2 = __tmp_58 in 
                                                          let y = (BInt 20) in 
                                                           let __tmp_78 = (nSMain__identityUnion y) in 
                                                            let y2 = __tmp_78 in 
                                                             let __tmp_83 = (cast (bosqueTerm) (x:bosqueTerm{BIntType=(getType x)}) (nthTuple 0 2 xTuple2)) in 
                                                              let __tmp_80 = (nSMain__max __tmp_83 y) in 
                                                               let z = __tmp_80 in 
                                                                let __tmp_85 = (nSMain__max z y) in 
                                                                 let z_max_func_repeated = __tmp_85 in 
                                                                  let __tmp_89 = (BTuple 3 (SCons (BInt 1) 2 (SCons (BBool true) 1 (SCons (BInt 2) 0 SNil)))) in 
                                                                   let __tmp_88 = (nSMain__identityTupleOptional __tmp_89) in 
                                                                    let z2 = __tmp_88 in 
                                                                     let __tmp_94 = (BTuple 1 (SCons (BTypedString "hello" BAnyType) 0 SNil)) in 
                                                                      let __tmp_93 = (nSMain__identityOpenTuple __tmp_94) in 
                                                                       let z3 = __tmp_93 in 
                                                                        let __tmp_96 = (nSMain__maxx (BBool false) (BInt 3)) in 
                                                                         let z4 = __tmp_96 in 
                                                                          let __tmp_99 = (BTuple 2 (SCons xTuple2 1 (SCons y 0 SNil))) in 
                                                                           let zTuple2 = __tmp_99 in 
                                                                            let __tmp_103 = (BTuple 2 (SCons y 1 (SCons (BBool false) 0 SNil))) in 
                                                                             let __tmp_102 = (nSMain__identityTupleNoneable __tmp_103) in 
                                                                              let z5 = __tmp_102 in 
                                                                               let __ir_ret__ = z in 
                                                                                let _return_ = __ir_ret__ in 
                                                                                 _return_

