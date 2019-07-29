module BosquePrelude 

open Sequence

(* Dynamic: depends on the 
   entities created by user *) 
type bosqueTerm = 
| BNone : bosqueTerm
| BInt : int -> bosqueTerm
| BBool : bool -> bosqueTerm
| BTuple : n:nat -> sequence bosqueTerm n -> bosqueTerm 
| BError : bosqueTerm

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

(* Definition of equality relation on Bosque terms *)
val eqTerm : bosqueTerm -> bosqueTerm -> bosqueTerm
let eqTerm x y = match x, y with
| BNone, BNone -> BBool true
| BInt x1, BInt y1 -> BBool (x1 = y1)
| BBool x1, BBool y1 -> BBool (x1 = y1)
// | BError, BError -> BBool true
| _, _ -> BError 

(* Definition of greater than or equal relation on Bosque terms *)
val greaterOrEq : bosqueTerm -> bosqueTerm -> bosqueTerm
let greaterOrEq x y = match x, y with
| BInt x1, BInt y1 -> BBool (x1 >= y1)
| _, _ -> BError

(* Tuple projector *)
val nthTuple : index:int -> dimension:nat -> bosqueTerm -> Tot bosqueTerm
let rec nthTuple index dimension y = match y with
| BTuple 0 CNil -> if (index < 0 || dimension <> 0) then BError else BNone
| BTuple dimension'' (CCons x #dimension' xs) -> 
  if (index < 0 || dimension <> dimension'') then BError else
  if (index >= dimension) then BNone else
  if index = 0 then x
  else nthTuple (index-1) dimension' (BTuple dimension' xs)
| _ -> BError

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


(* --------------------------------- *)
(* Type checkers *)
val isBool : bosqueTerm -> bool
let isBool x = match x with 
| BBool _ -> true
| _ -> false 

val isInt : bosqueTerm -> bool
let isInt x = match x with 
| BInt _ -> true
| _ -> false 

val isTuple : n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> bool
let isTuple n seq x = match x with
| BTuple m seq' -> n = m && (eqType (getType (BTuple m seq')) (BTypeTuple false m seq)) 
| _ -> false
(* --------------------------------- *)

  (* ------------------------------------------------------------------------ *)
(* Extractors *)

(* This is mainly used inside conditionals (in the fstar programming language) 
   and assertions (in the z3 smt solver) *)
val extractBool : x:bosqueTerm{isBool x} -> bool
let extractBool x = match x with
| BBool y -> y

// val extractTuple : n:nat -> x:bosqueTerm{isTuple n x} -> sequence bosqueTerm n
// let extractTuple n x = match x with
// | BTuple _ seq -> seq
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------------------------- *)
(* Definition of UnionType *)
type typeUnionIntBool = x:bosqueType{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) x}
type termUnionIntBool = x:bosqueTerm{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (getType x)} 
(* Definition of IntType *)
type termInt = x:bosqueTerm{isInt x} 
(* ------------------------------------------------------------------------------------------- *)
