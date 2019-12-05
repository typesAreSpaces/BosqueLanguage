module NSMain__main_main
open Sequence
open BosqueTypes
open BosqueTerms
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))
let bTupleType_3bTupleType_2BIntType_BIntTypefalse_bTupleType_2BIntType_BIntTypefalse_BIntTypefalse = BTupleType false 3 (SCons bTupleType_2BIntType_BIntTypefalse 2 (SCons bTupleType_2BIntType_BIntTypefalse 1 (SCons BIntType 0 SNil)))
let bTupleType_16BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_bTupleType_2BIntType_BIntTypefalse_bTypedStringType_BAnyType_BBoolType_BBoolTypefalse = BTupleType false 16 (SCons BIntType 15 (SCons BIntType 14 (SCons BIntType 13 (SCons BIntType 12 (SCons BIntType 11 (SCons BIntType 10 (SCons BIntType 9 (SCons BIntType 8 (SCons BIntType 7 (SCons BIntType 6 (SCons BIntType 5 (SCons BIntType 4 (SCons bTupleType_2BIntType_BIntTypefalse 3 (SCons bTypedStringType_BAnyType 2 (SCons BBoolType 1 (SCons BBoolType 0 SNil))))))))))))))))
let bTypedStringType_BNoneType = (BTypedStringType BNoneType)
let bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BNoneType = (BUnionType BBoolType (BUnionType BIntType (BUnionType BNoneType bTypedStringType_BNoneType)))
let bUnionType_BIntType_BNoneType = (BUnionType BIntType BNoneType)
let bTupleType_3BIntType_BBoolType_BIntTypefalse = BTupleType false 3 (SCons BIntType 2 (SCons BBoolType 1 (SCons BIntType 0 SNil)))
let bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue = BTupleType true 4 (SCons BIntType 3 (SCons BBoolType 2 (SCons BIntType 1 (SCons BBoolType 0 SNil))))
let bUnionType_bTupleType_3BIntType_BBoolType_BIntTypefalse_bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue = (BUnionType bTupleType_3BIntType_BBoolType_BIntTypefalse bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue)
let bTupleType_1bTypedStringType_BAnyTypefalse = BTupleType false 1 (SCons bTypedStringType_BAnyType 0 SNil)
let bTupleType_1bTypedStringType_BAnyTypetrue = BTupleType true 1 (SCons bTypedStringType_BAnyType 0 SNil)
let bTupleType_1bTypedStringType_BNoneTypetrue = BTupleType true 1 (SCons bTypedStringType_BNoneType 0 SNil)
let bUnionType_BBoolType_BNoneType = (BUnionType BBoolType BNoneType)
let bUnionType_BBoolType_BIntType_BNoneType = (BUnionType BBoolType (BUnionType BIntType BNoneType))
let bUnionType_BBoolType_BNoneType_BIntType = (BUnionType BBoolType (BUnionType BNoneType BIntType))
let bTupleType_2bTupleType_2BIntType_BIntTypefalse_BIntTypefalse = BTupleType false 2 (SCons bTupleType_2BIntType_BIntTypefalse 1 (SCons BIntType 0 SNil))
let bTupleType_2BIntType_BBoolTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BBoolType 0 SNil))
let bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons bUnionType_BBoolType_BNoneType 0 SNil))

(* Concept Declarations *)

(* Entity Declarations *)

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__identityUnion : (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BNoneType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BNoneType (getType x)})
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

// val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let a  = 
 let __tmp_0 = (BTuple 2 (SCons (BInt 10) 1 (SCons (BInt 30) 0 SNil))) in 
  let xTuple2 = __tmp_0 in 
   let __tmp_5 = (BTuple 2 (SCons (BInt 1) 1 (SCons (BInt 2) 0 SNil))) in 
    let __tmp_8 = (BTuple 2 (SCons (BInt 3) 1 (SCons (BInt 4) 0 SNil))) in 
     let __tmp_4 = (BTuple 3 (SCons __tmp_5 2 (SCons __tmp_8 1 (SCons (BInt 5) 0 SNil)))) in 
      let __tmp_12 = (cast (bosqueTerm) (x:bosqueTerm{BIntType=(getType x)}) (nthTuple 2 3 __tmp_4)) in 
       let proj_tuple = __tmp_12 in 
        let __tmp_26 = (BTuple 2 (SCons (BInt 1) 1 (SCons (BInt 1) 0 SNil))) in 
         let __tmp_13 = (BTuple 16 (SCons (BInt 1) 15 (SCons (BInt 1) 14 (SCons (BInt 1) 13 (SCons (BInt 1) 12 (SCons (BInt 1) 11 (SCons (BInt 1) 10 (SCons (BInt 1) 9 (SCons (BInt 1) 8 (SCons (BInt 1) 7 (SCons (BInt 1) 6 (SCons (BInt 1) 5 (SCons (BInt 1) 4 (SCons __tmp_26 3 (SCons (BTypedString "hello" BAnyType) 2 (SCons (BBool false) 1 (SCons (BBool true) 0 SNil))))))))))))))))) in 
          let x2 = __tmp_13 in 
           let y = (BInt 20) in 
            let __tmp_33 = (nSMain__identityUnion y) in 
             let y2 = __tmp_33 in 
              let __tmp_38 = (cast (bosqueTerm) (x:bosqueTerm{BIntType=(getType x)}) (nthTuple 0 2 xTuple2)) in 
               let __tmp_35 = (nSMain__max __tmp_38 y) in 
                let z = __tmp_35 in 
                 let __tmp_40 = (nSMain__max z y) in 
                  let z_max_func_repeated = __tmp_40 in 
                   // let __tmp_44 = (BTuple 3 (SCons (BInt 1) 2 (SCons (BBool true) 1 (SCons (BInt 2) 0 SNil)))) in 
                   //  let __tmp_43 = (nSMain__identityTupleOptional __tmp_44) in 
                   //   let z2 = __tmp_43 in 
                      let __tmp_49 = (BTuple 1 (SCons (BTypedString "hello" BAnyType) 0 SNil)) in 
                       let __tmp_48 = (nSMain__identityOpenTuple __tmp_49) in 
                        let z3 = __tmp_48 in 
                         let __tmp_51 = (nSMain__maxx (BBool false) (BInt 3)) in 
                          let z4 = __tmp_51 in 
                           let __tmp_54 = (BTuple 2 (SCons xTuple2 1 (SCons y 0 SNil))) in 
                            let zTuple2 = __tmp_54 in 
                             // let __tmp_58 = (BTuple 2 (SCons y 1 (SCons (BBool false) 0 SNil))) in 
                             //  let __tmp_57 = (nSMain__identityTupleNoneable __tmp_58) in 
                             //   let z5 = __tmp_57 in 
                                let __ir_ret__ = z in 
                                 let _return_ = __ir_ret__ in 
                                  _return_


let b = let __tmp_58 = (BTuple 2 (SCons (BInt 20) 1 (SCons (BBool false) 0 SNil))) in 
  let __tmp_57 = (nSMain__identityTupleNoneable __tmp_58) in 
    let z5 = __tmp_57 in  z5
