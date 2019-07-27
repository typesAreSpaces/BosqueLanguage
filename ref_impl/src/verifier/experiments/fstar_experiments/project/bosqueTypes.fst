module BosqueTypes

open Sequence
open BosqueTerms

// Convention with UnionTerm: 
// its elements should be unique
noeq type bosqueType =
| BTypeError 
| BTypeNone
| BTypeInt
| BTypeBool
| BTypeUnion : bosqueType -> bosqueType -> bosqueType
// The bool indicates if the Tuple is open or not
| BTypeEmptyTuple
| BTypeTuple : bool -> n:nat -> sequence bosqueType n -> bosqueType
// | BTypeTuple : bool -> n:nat -> sequence bosqueTerm n -> bosqueType


(* --------------------------------------------------------------- *)
(* Operations on Bosque Types *)

(* Definition of equality relation on Bosque types *)
val eqType : bosqueType -> bosqueType -> bool
let eqType x y = match x, y with
| BTypeError, BTypeError -> true 
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
| BTypeUnion _ _ , BTypeUnion _ _ -> true    // FIX: This is incomplete
| BTypeTuple _ _ _, BTypeTuple _ _ _ -> true // FIX: This is incomplete
| _, _ -> false 

val mapTermToType : #n:nat -> sequence bosqueTerm n -> Tot (sequence bosqueType n) 
val getType : bosqueTerm -> Tot bosqueType
let rec getType x = match x with
| BError -> BTypeError
| BNone -> BTypeNone
| BInt _ -> BTypeInt
| BBool _ -> BTypeBool
| BTuple n y -> admit(); BTypeTuple false n (mapTermToType y)
// | BTuple 0 CNil -> BTypeEmptyTuple
// | BTuple n CNil -> BTypeError
// | BTuple 0 (CCons _ _) -> BTypeError
// | BTuple n (CCons hd #m tl) -> 
//   if (m + 1 <> n) then BTypeError 
//   else BTypeTuple false (m + 1) (CCons (getType hd) (mapTermToType #m tl))
and mapTermToType #n x1 = match x1 with
| CNil -> CNil
| CCons y1 #m ys1 -> admit(); CCons (getType y1) (mapTermToType #m ys1)

// forall x y . bosqueSubtypeOf x y <===> x :> y
val bosqueSubtypeOf : bosqueType -> bosqueType -> (Tot bool)
let rec bosqueSubtypeOf x y = match x, y with
| BTypeError, BTypeError -> true
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
| BTypeUnion x1 y1, BTypeUnion x2 y2 -> (bosqueSubtypeOf x1 x2 || bosqueSubtypeOf y1 x2) 
  && (bosqueSubtypeOf x1 y2 || bosqueSubtypeOf y1 y2)
| BTypeUnion x1 y1, z -> bosqueSubtypeOf x1 z || bosqueSubtypeOf y1 z 
// Missing case: BTuple
| _, _ -> false

(* ---------------------------------------------------------------- *)
(* Definition of UnionType *)
type typeUnionIntBool = x:bosqueType{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) x}
type termUnionIntBool = x:bosqueTerm{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (getType x)} 
(* Definition of IntType *)
type termInt = x:bosqueTerm{isInt x} 
(* ---------------------------------------------------------------- *)
