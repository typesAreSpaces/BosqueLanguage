module BosqueTypes

open Sequence
open BosqueTerms

// Convention with UnionTerm: 
// its elements should be unique
type bosqueType =
| BTypeNone
| BTypeInt
| BTypeBool
| BTypeUnion : bosqueType -> bosqueType -> bosqueType
// The bool indicates if the Empty Tuple is open or not
| BTypeEmptyTuple : bool -> bosqueType
// The bool indicates if the Tuple is open or not
| BTypeTuple : bool -> n:nat -> sequence bosqueType n -> bosqueType
| BTypeError 

(* --------------------------------------------------------------- *)
(* Operations on Bosque Types *)

(* Definition of equality relation on Bosque types *)
val eqType : bosqueType -> bosqueType -> bool
let eqType x y = match x, y with
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
| BTypeUnion _ _ , BTypeUnion _ _ -> true    // FIX: This is incomplete
| BTypeEmptyTuple b1, BTypeEmptyTuple b2 -> b1 = b2
| BTypeTuple _ _ _, BTypeTuple _ _ _ -> true // FIX: This is incomplete
| BTypeError, BTypeError -> true 
| _, _ -> false

(* Definition of getType *)
val getType_aux : #n:nat -> (x: sequence bosqueTerm n) -> Tot (sequence bosqueType n) (decreases x)
val getType : x:bosqueTerm -> Tot bosqueType (decreases x)
let rec getType x = match x with
| BError -> BTypeError
| BNone -> BTypeNone
| BInt _ -> BTypeInt
| BBool _ -> BTypeBool
| BTuple n CNil -> if (n <> 0) then BTypeError else BTypeEmptyTuple false 
| BTuple n (CCons y ys) -> BTypeTuple false n (getType_aux #n (CCons y ys))
and 
getType_aux #n x = match x with
| CNil -> CNil
| CCons y ys -> CCons (getType y) (getType_aux ys)

(* Definition to encode the subtype relation on Bosque types *)
// forall x y . bosqueSubtypeOf x y <===> x :> y
val bosqueSubtypeOf : bosqueType -> bosqueType -> (Tot bool)
let rec bosqueSubtypeOf x y = match x, y with
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
| BTypeUnion x1 y1, BTypeUnion x2 y2 -> (bosqueSubtypeOf x1 x2 || bosqueSubtypeOf y1 x2) 
  && (bosqueSubtypeOf x1 y2 || bosqueSubtypeOf y1 y2)
| BTypeUnion x1 y1, z -> bosqueSubtypeOf x1 z || bosqueSubtypeOf y1 z 
| BTypeEmptyTuple b1, BTypeEmptyTuple _ -> b1
// Missing case: BTuple
| BTypeError, BTypeError -> true
| _, _ -> false

(* ---------------------------------------------------------------- *)
(* Definition of UnionType *)
type typeUnionIntBool = x:bosqueType{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) x}
type termUnionIntBool = x:bosqueTerm{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (getType x)} 
(* Definition of IntType *)
type termInt = x:bosqueTerm{isInt x} 
(* ---------------------------------------------------------------- *)
