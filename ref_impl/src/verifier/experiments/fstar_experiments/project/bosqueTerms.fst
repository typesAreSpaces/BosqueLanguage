module BosqueTerms

open Sequence
open BosqueTypes
open FStar.Ghost

(* Dynamic: depends on the 
   entities created by user *) 
type bosqueTerm = 
| BNone : bosqueTerm
| BInt : int -> bosqueTerm
| BBool : bool -> bosqueTerm
| BTuple : n:nat -> sequence bosqueTerm n -> bosqueTerm 
| BError : bosqueTerm

(* Definition of getType *)
val getType : x:bosqueTerm -> Tot bosqueType
let rec getType x = match x with
| BNone -> BTypeNone
| BInt _ -> BTypeInt
| BBool _ -> BTypeBool
| BTuple n SNil -> if (n <> 0) then BTypeError else BTypeEmptyTuple false 
| BTuple n y -> BTypeTuple false n (mapSequence' (hide x) getType y) 
| BError -> BTypeError

val mapTermsToTypes : #n:nat 
  -> (x: sequence bosqueTerm n) 
  -> Tot (sequence bosqueType n)
let rec mapTermsToTypes #n x = match x with
| SNil -> SNil
| SCons y ys -> SCons (getType y) (mapTermsToTypes ys)

(* --------------------------------------------------------------- *)
(* Casting / Type checkers *)
val isNone : bosqueTerm -> Tot bool
let isNone x = match x with 
| BNone -> true
| _ -> false 

val isInt : bosqueTerm -> Tot bool
let isInt x = match x with 
| BInt _ -> true
| _ -> false 

val isBool : bosqueTerm -> Tot bool
let isBool x = match x with 
| BBool _ -> true
| _ -> false 

val isTuple : n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool
let isTuple n seqTypes x = match x with
| BTuple m seqTerms -> if (n = 0) then (eqType (getType (BTuple m seqTerms)) (BTypeEmptyTuple false))
  else (n = m) && (eqTypeSeq (mapTermsToTypes seqTerms) seqTypes)
| _ -> false

val isError : bosqueTerm -> Tot bool
let isError x = match x with 
| BError -> true
| _ -> false 
(* --------------------------------------------------------------- *)

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

(* Definition of equality relation on Bosque terms *)
val eqTerm_aux : #n:nat 
  -> (x:sequence bosqueTerm n) 
  -> sequence bosqueTerm n 
  -> Tot (z:bosqueTerm{isBool z \/ isError z}) (decreases x)
val eqTerm : x:bosqueTerm 
  -> bosqueTerm 
  -> Tot (z:bosqueTerm{isBool z \/ isError z})  (decreases x)
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
val greaterOrEq : bosqueTerm -> bosqueTerm -> Tot (x:bosqueTerm{isBool x \/ isError x})
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

(* ------------------------------------------------------------------------------------------- *)
(* Type instantiation *)
type typeUnionIntBool = x:bosqueType{subtypeOf (BTypeUnion BTypeInt BTypeBool) x}
type termUnionIntBool = x:bosqueTerm{subtypeOf (BTypeUnion BTypeInt BTypeBool) (getType x)} 
(* Definition of IntType *)
type termInt = x:bosqueTerm{isInt x} 
(* ------------------------------------------------------------------------------------------- *)
