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
// 1) its elements should be unique
// 2) There is a unique way to represent any union (normal form)
// the latter was needed for eqType
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
| BTuple n SNil -> if (n <> 0) then BTypeError else BTypeEmptyTuple false 
| BTuple n (SCons y ys) -> BTypeTuple false n (getType_aux #n (SCons y ys))
and 
getType_aux #n x = match x with
| SNil -> SNil
| SCons y ys -> SCons (getType y) (getType_aux ys)

(* Definition of equality relation on Bosque terms *)
val eqTerm_aux : #n:nat -> (x:sequence bosqueTerm n) -> sequence bosqueTerm n -> Tot bosqueTerm (decreases x)
val eqTerm : x:bosqueTerm -> bosqueTerm -> Tot bosqueTerm (decreases x)
let rec eqTerm x y = match x, y with
| BNone, BNone -> BBool true
| BInt x1, BInt y1 -> BBool (x1 = y1)
| BBool x1, BBool y1 -> BBool (x1 = y1)
| BTuple n1 seq1, BTuple n2 seq2 -> if (n1 <> n2) then BError
                                   else eqTerm_aux #n1 seq1 seq2
// | BError, BError -> BBool true
| _, _ -> BError
and 
eqTerm_aux #n x y = match x with
| SNil -> (match y with
         | SNil -> BBool true
         | _ -> BError
         )
| SCons x1 xs1 -> (match y with
                 | SNil -> BError
                 | SCons y1 ys1 -> (match (eqTerm x1 y1) with
                                  | BBool b1 -> (match (eqTerm_aux xs1 ys1) with
                                               | BBool b2 -> BBool (b1 && b2)
                                               | _ -> BError
                                               )
                                  | _ -> BError 
                                  )
                 )

(* Definition of greater than or equal relation on Bosque terms *)
val greaterOrEq : bosqueTerm -> bosqueTerm -> Tot bosqueTerm
let greaterOrEq x y = match x, y with
| BInt x1, BInt y1 -> BBool (x1 >= y1)
| _, _ -> BError

(* Tuple projector *)
val nthTuple : index:int -> dimension:nat -> bosqueTerm -> Tot bosqueTerm
let rec nthTuple index dimension y = match y with
| BTuple 0 SNil -> if (index < 0 || dimension <> 0) then BError else BNone
| BTuple dimension'' (SCons x #dimension' xs) -> 
  if (index < 0 || dimension <> dimension'') then BError else
  if (index >= dimension) then BNone else
  if index = 0 then x
  else nthTuple (index-1) dimension' (BTuple dimension' xs)
| _ -> BError

(* Definition of equality relation on Bosque types *)
val eqType_aux : #n:nat -> (x:sequence bosqueType n) -> sequence bosqueType n -> Tot bool (decreases x)
val eqType : x:bosqueType -> bosqueType -> Tot bool (decreases x)
let rec eqType x y = match x, y with
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
// The following might be incomplete, but if Unions are normalized then it is complete
| BTypeUnion x1 x2 , BTypeUnion y1 y2 -> eqType x1 y1 && eqType x2 y2
| BTypeUnion _ _, _ -> false
| BTypeEmptyTuple b1, BTypeEmptyTuple b2 -> b1 = b2 
| BTypeTuple b1 n1 seq1, BTypeTuple b2 n2 seq2 -> (b1 = b2) && (n1 = n2) && eqType_aux seq1 seq2
| BTypeError, BTypeError -> true
| _, _ -> false
and
eqType_aux #n x y = match x with
| SNil -> (match y with 
  | SNil -> true
  | _ -> false
  )
| SCons x1 xs1 -> let (SCons y1 ys1) = y in 
  eqType x1 y1 && eqType_aux xs1 ys1

(* Definition to encode the subtype relation on Bosque types *)
// forall x y . bosqueSubtypeOf x y <===> x :> y
val bosqueSubtypeOf : bosqueType -> bosqueType -> Tot bool
let rec bosqueSubtypeOf x y = match x, y with
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
| BTypeUnion x1 y1, BTypeUnion x2 y2 -> (bosqueSubtypeOf x1 x2 || bosqueSubtypeOf y1 x2) 
  && (bosqueSubtypeOf x1 y2 || bosqueSubtypeOf y1 y2)
| BTypeUnion x1 y1, z -> bosqueSubtypeOf x1 z || bosqueSubtypeOf y1 z 
| BTypeEmptyTuple b1, BTypeEmptyTuple b2 -> b1 = b2
// FIX: The following doesnt' include the open/close semantics of Tuples
| BTypeTuple _ _ _, BTypeTuple _ _ _ -> true
| BTypeError, BTypeError -> true
| _, _ -> false


(* ----------------------------------------------------------- *)
(* Type checkers *)
val isBool : bosqueTerm -> Tot bool
let isBool x = match x with 
| BBool _ -> true
| _ -> false 

val isInt : bosqueTerm -> Tot bool
let isInt x = match x with 
| BInt _ -> true
| _ -> false 

val isTuple : n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool
let isTuple n seq x = match x with
| BTuple m seq' -> n = m 
  && (eqType (getType (BTuple m seq')) (BTypeTuple false m seq))
| _ -> false
(* ----------------------------------------------------------- *)

(* ------------------------------------------------------------------------ *)
(* Extractors *)

(* This is mainly used inside conditionals (in the fstar programming language) 
   and assertions (in the z3 smt solver) *)
val extractBool : x:bosqueTerm{isBool x} -> Tot bool
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
