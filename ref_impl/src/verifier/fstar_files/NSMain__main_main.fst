module NSMain__main_main
open Sequence
open BosqueTypes
open BosqueTerms
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))
let bTupleType_2BIntType_bTupleType_2BIntType_BIntTypefalsefalse = BTupleType false 2 (SCons BIntType 1 (SCons bTupleType_2BIntType_BIntTypefalse 0 SNil))

(* Concept Declarations *)

(* Entity Declarations *)
type nSMain__PlayerMark = 
| BnSMain__PlayerMark : mark : bosqueTerm{bTypedStringType_BAnyType = (getType mark)} -> 
nSMain__PlayerMark
type nSMain__Artist = 
| BnSMain__Artist : id : bosqueTerm{BIntType = (getType id)} -> 
isGood : bosqueTerm{BBoolType = (getType isGood)} -> 
lastName : bosqueTerm{bTypedStringType_BAnyType = (getType lastName)} -> 
name : bosqueTerm{bTypedStringType_BAnyType = (getType name)} -> 
player : nSMain__PlayerMark -> 
nSMain__Artist
type nSMain__Musician = 
| BnSMain__Musician : artist : nSMain__Artist -> 
instrument : bosqueTerm{bTypedStringType_BAnyType = (getType instrument)} -> 
nSMain__Musician

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__max3 : (x:bosqueTerm{subtypeOf bTupleType_2BIntType_BIntTypefalse (getType x)}) -> Tot (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__max3 x = 
 let _ = assert_norm(subtypeOf bTupleType_2BIntType_BIntTypefalse (getType x)) in
 let __tmp_3 = (nthTuple 0 2 x) in 
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

val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main  = 
 let __tmp_0 = (BTuple 2 (SCons (BInt 10) 1 (SCons (BInt 30) 0 SNil))) in 
  let xTuple2 = __tmp_0 in 
   let __tmp_3 = (BTuple 2 (SCons (BInt 10) 1 (SCons xTuple2 0 SNil))) in 
    let xTuple2_1 = __tmp_3 in 
     let __tmp_8 = (BTuple 2 (SCons (BInt 10) 1 (SCons (BInt 3) 0 SNil))) in 
      let __tmp_6 = (BTuple 2 (SCons (BInt 10) 1 (SCons __tmp_8 0 SNil))) in 
       let xTuple2_2 = __tmp_6 in 
        let _ = assert_norm(subtypeOf bTupleType_2BIntType_bTupleType_2BIntType_BIntTypefalsefalse (getType xTuple2_1)) in
        let __tmp_13 = (nthTuple 1 2 xTuple2_1) in 
         let xTuple_second = __tmp_13 in 
          let _ = assert_norm(subtypeOf bTupleType_2BIntType_bTupleType_2BIntType_BIntTypefalsefalse (getType xTuple2_2)) in
          let __tmp_16 = (nthTuple 1 2 xTuple2_2) in 
           let xTuple_second_ = __tmp_16 in 
            let _ = assert_norm(subtypeOf bTupleType_2BIntType_BIntTypefalse (getType xTuple_second)) in
            
            let __tmp_17 = (nSMain__max3 xTuple_second) in 
             let x_max_tuple = __tmp_17 in 
              let _ = assert_norm(subtypeOf bTupleType_2BIntType_BIntTypefalse (getType xTuple_second_)) in
              
              let __tmp_19 = (nSMain__max3 xTuple_second_) in 
               let x_max_tuple_ = __tmp_19 in 
                let __ir_ret__ = (BInt 2) in 
                 let _return_ = __ir_ret__ in 
                  _return_

