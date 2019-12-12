module A
open Sequence
open BosqueTypes
open BosqueTerms
open Util

#set-options "--z3rlimit 25"
// #set-options "--max_fuel 5 --max_ifuel 5 --initial_fuel 1"

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))
let bTupleType_3bTupleType_2BIntType_BIntTypefalse_bTupleType_2BIntType_BIntTypefalse_BIntTypefalse = BTupleType false 3 (SCons bTupleType_2BIntType_BIntTypefalse 2 (SCons bTupleType_2BIntType_BIntTypefalse 1 (SCons BIntType 0 SNil)))
let bTupleType_16BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_bTupleType_2BIntType_BIntTypefalse_bTypedStringType_BAnyType_BBoolType_BBoolTypefalse = BTupleType false 16 (SCons BIntType 15 (SCons BIntType 14 (SCons BIntType 13 (SCons BIntType 12 (SCons BIntType 11 (SCons BIntType 10 (SCons BIntType 9 (SCons BIntType 8 (SCons BIntType 7 (SCons BIntType 6 (SCons BIntType 5 (SCons BIntType 4 (SCons bTupleType_2BIntType_BIntTypefalse 3 (SCons bTypedStringType_BAnyType 2 (SCons BBoolType 1 (SCons BBoolType 0 SNil))))))))))))))))
let bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BAnyType = (BUnionType BBoolType (BUnionType BIntType (BUnionType BNoneType bTypedStringType_BAnyType)))
let bUnionType_BIntType_BNoneType = (BUnionType BIntType BNoneType)
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
val nSMain__identityTupleNoneable : (x:bosqueTerm{subtypeOf bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse (getType x)})
let nSMain__identityTupleNoneable x = 
 let __ir_ret__ = x in 
  let _return_ = __ir_ret__ in 
   _return_ 

let c = let inside = BInt 10 in cast (bosqueTerm) (x:bosqueTerm{BIntType = (getType x)}) inside

let c2 = let inside = BInt 10 <: (x:bosqueTerm{BIntType = (getType x)}) in  inside


let mm1 = (BTuple 2 (SCons (BInt 22) 1 (SCons (BBool false) 0 SNil)))
let mm2 = assert (1 = 1) ; (nSMain__identityTupleNoneable mm1) 

let _ = assert (subtypeOf bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse (getType mm1)) 

// This fails
// let _ = assert (subtypeOf bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse (getType ((BTuple 2 (SCons (BInt 22) 1 (SCons (BBool false) 0 SNil))))))

let _ = assert_norm (subtypeOf bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse (getType ((BTuple 2 (SCons (BInt 22) 1 (SCons (BBool false) 0 SNil))))))

val little_lemma : unit -> Lemma (ensures (subtypeOf bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse (getType ((BTuple 2 (SCons (BInt 22) 1 (SCons (BBool false) 0 SNil)))))))
let little_lemma () = assert_norm (subtypeOf bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse (getType ((BTuple 2 (SCons (BInt 22) 1 (SCons (BBool false) 0 SNil))))))

// let mm3_with_problem = let inside = (BTuple 2 (SCons (BInt 22) 1 (SCons (BBool false) 0 SNil))) in 
//   (nSMain__identityTupleNoneable inside) // Same problem here :( 

let mm3 = let inside = (BTuple 2 (SCons (BInt 22) 1 (SCons (BBool false) 0 SNil))) in
  assert_norm (subtypeOf bTupleType_2BIntType_bUnionType_BBoolType_BNoneTypefalse (getType ((BTuple 2 (SCons (BInt 22) 1 (SCons (BBool false) 0 SNil))))));
  (nSMain__identityTupleNoneable inside) // Same problem here :(  


// // I dont understand this problem. It looks like the type of __tmp_50 is not propagated quite enough
// let a = let y = BInt 20 in 
// let __tmp_50 = (BTuple 2 (SCons y 1 (SCons (BBool false) 0 SNil))) in  
//   let __tmp_49 = (nSMain__identityTupleNoneable __tmp_50) in 
//     let z5 = __tmp_49 in y 