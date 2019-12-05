module NSMain__main_main_testing
open Sequence
open BosqueTypes
open BosqueTerms
open Util

#set-options "--z3rlimit 15"

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))
let bUnionType_BIntType_BNoneType = (BUnionType BIntType BNoneType)
let bTermbUnion = x1:bosqueTerm{subtypeOf (BUnionType BIntType BNoneType) (getType x1)} 

(* Concept Declarations *)

(* Entity Declarations *)

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__max2 : (x1:bosqueTerm{subtypeOf BIntType (getType x1)}) -> (x2:bosqueTerm{subtypeOf BIntType (getType x2)}) -> Tot (x3:bosqueTerm{subtypeOf BIntType (getType x3)}) 
let nSMain__max2 x y = 
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
        
val nSMain__max : (x1:bosqueTerm{subtypeOf bUnionType_BIntType_BNoneType (getType x1)}) -> (x2:bosqueTerm{subtypeOf BIntType (getType x2)}) -> Tot (x3:bosqueTerm{subtypeOf BIntType (getType x3)}) 
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

val nSMain__main3 : (x:bosqueTerm{subtypeOf BIntType (getType x)}) 
let nSMain__main3  = 
 let what = (SCons (BInt 10) 1 (SCons (BInt 30) 0 SNil)) in
  let __tmp_0 = (BTuple 2 what) in 
   let xTuple2 = __tmp_0 in 
    let y = (BInt 20) in 
      (BInt 10) 

let tuple_test = (SCons (BInt 10) 1 (SCons (BInt 30) 0 SNil))
let proj1_tuple_test = nthTuple 0 2 (BTuple 2 tuple_test)
let hmm = op_neg (proj1_tuple_test)
let hmm2 = nSMain__max (proj1_tuple_test) (BInt 11) 

let __tmp_7 =  let what = (SCons (BInt 10) 1 (SCons (BInt 30) 0 SNil)) in
  let __tmp_0 = (BTuple 2 what) in 
   let xTuple2 = __tmp_0 in 
    let y = (BInt 20) in (nthTuple 0 2 (BTuple 2 what)) 

let ahhhh4 = nSMain__max2 (cast (bosqueTerm) (x:bosqueTerm{BIntType = (getType x)}) __tmp_7) (BInt 1)
let ahhhh5 = nSMain__max2 (cast (bosqueTerm) (x:bosqueTerm{isInt x}) (BBool true)) (BInt 1)// <- This abuses the cast function
let check = ahhhh4 = BInt 10

val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main  = 
  let y = (BInt 20) in
    let __tmp_4 = (nSMain__max2 (cast (bosqueTerm) (x:bosqueTerm{BIntType = (getType x)}) __tmp_7) y) in 
      let z = __tmp_4 in 
        let __ir_ret__ = z in 
          let _return_ = __ir_ret__ in 
            _return_

val nSMain__main_original : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main_original  = 
 let what = (SCons (BInt 10) 1 (SCons (BInt 30) 0 SNil)) in
  let __tmp_0 = (BTuple 2 what) in 
   let xTuple2 = __tmp_0 in 
    let y = (BInt 20) in 
     let __tmp_7 = (nthTuple 0 2 (BTuple 2 what)) in 
      let __tmp_4 = (nSMain__max (cast (bosqueTerm) (x:bosqueTerm{BIntType = (getType x)}) __tmp_7) y) in 
       let z = __tmp_4 in 
        let __ir_ret__ = z in 
         let _return_ = __ir_ret__ in 
          _return_

val lemma_nthTuple : index : int -> dimension : nat -> x : bosqueTerm -> 
Lemma (ensures ((nthTupleType index dimension x) = (getType (nthTuple index dimension x))))
let rec lemma_nthTuple index dimension y = match y with
| BTuple 0 SNil -> ()
| BTuple dimension'' (SCons x dimension' xs) -> 
  if (index <= 0 || index >= dimension) then () 
  else lemma_nthTuple (index-1)  dimension' (BTuple dimension' xs)
| _ -> ()

val nSMain__main_original2 : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main_original2  = 
 let what = (SCons (BInt 10) 1 (SCons (BInt 30) 0 SNil)) in
  let __tmp_0 = (BTuple 2 what) in 
   let xTuple2 = __tmp_0 in 
    let y = (BInt 20) in 
     let __tmp_7 = (nthTuple 0 2 (BTuple 2 what)) in 
      lemma_nthTuple 0 2 (__tmp_0);
      let __tmp_4 = (nSMain__max __tmp_7 y) in
       let z = __tmp_4 in 
        let __ir_ret__ = z in 
         let _return_ = __ir_ret__ in 
          _return_
