module BosqueTerms

open Sequence
open BosqueTypes
open FStar.Ghost

(* Dynamic: depends on the 
   entities created by user *) 
type bosqueTerm = 
| BNone : bosqueTerm
| BBool : bool -> bosqueTerm
| BInt : int -> bosqueTerm
// No support for Float
// No support for Regex
| BTypedString : value:string -> content_type:bosqueType -> bosqueTerm
| BGUID : string -> int -> bosqueTerm
| BTuple : n:nat -> sequence bosqueTerm n -> bosqueTerm
| BRecord : n:nat -> sequence bosqueTerm n -> bosqueTerm
| BError : bosqueTerm

(* Definition of getType *)
val getType : x:bosqueTerm -> Tot bosqueType
let rec getType x = match x with
| BNone -> BNoneType
| BBool _ -> BBoolType
| BInt _ -> BIntType
| BTypedString _ content_type -> BTypedStringType content_type
| BGUID _ _ -> BGUIDType
| BTuple n SNil -> if (n <> 0) then BErrorType else BTupleType false 0 SNil
| BTuple n y -> BTupleType false n (mapSequence' n (hide x) getType y) 
// FIX: The following is incomplete
| BRecord _ _ -> BRecordType false 0 (SNil)
| BError -> BErrorType

val mapTermsToTypes : #n:nat 
  -> (x: sequence bosqueTerm n) 
  -> Tot (sequence bosqueType n)
let rec mapTermsToTypes #n x = match x with
| SNil -> SNil
| SCons y m ys -> SCons (getType y) m (mapTermsToTypes ys)

(* --------------------------------------------------------------- *)
(* Casting / Type checkers *)
val isNone : bosqueTerm -> Tot bool
let isNone x = match x with 
| BNone -> true
| _ -> false

val isSome : bosqueTerm -> Tot bool
let isSome x = not (isNone x)

val isBool : bosqueTerm -> Tot bool
let isBool x = match x with 
| BBool _ -> true
| _ -> false 

val isInt : bosqueTerm -> Tot bool
let isInt x = match x with 
| BInt _ -> true
| _ -> false 

val isTypedString : bosqueType -> bosqueTerm -> Tot bool
let isTypedString ty x = match x with 
| BTypedString _ ty' -> eqType ty ty'
| _ -> false 

val isGUID : bosqueTerm -> Tot bool
let isGUID x = match x with 
| BGUID _ _ -> true
| _ -> false 

val isTuple : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool
// let isTuple b n seqTypes x = eqType (BTupleType b n seqTypes) (getType x)
// let isTuple b n seqTypes x = match x with
// | BTuple m seqTerms -> if (n = 0) then (eqType (getType (BTuple m seqTerms)) (BTupleType false 0 SNil))
//   else (n = m) && (eqTypeSeq (mapTermsToTypes seqTerms) seqTypes)
// | _ -> false
let isTuple b n seqTypes x = match x with
| BTuple m seqTerms -> (n = m) && eqType (BTupleType b n seqTypes) (getType x)
| _ -> false

val isTuple2 : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool
let isTuple2 b n seqTypes x = match x with
| BTuple m seqTerms -> eqType (BTupleType b n seqTypes) (getType x)
| _ -> false

val isTuple3 : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool
let isTuple3 b n seqTypes x = eqType (BTupleType b n seqTypes) (getType x)

val isRecord : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool
let isRecord b n seqTypes x = eqType (getType x) (BRecordType b n seqTypes)

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
| BBool x1, BBool y1 -> BBool (x1 = y1)
| BInt x1, BInt y1 -> BBool (x1 = y1)
| BTypedString s1 ty1, BTypedString s2 ty2 -> BBool (s1 = s2 && eqType ty1 ty2)
| BGUID s1 n1, BGUID s2 n2 -> BBool (s1 = s2 && n1 = n2)
| BTuple n1 seq1, BTuple n2 seq2 -> if (n1 <> n2) then BError
                                   else eqTerm_aux #n1 seq1 seq2
// FIX: Include case for BRecord
// | BError, BError -> BBool true
| _, _ -> BError
and 
eqTerm_aux #n x y = match x with
| SNil -> (match y with
         | SNil -> BBool true
         | _ -> BError
         )
| SCons x1 m xs1 -> (match y with
                 | SNil -> BError
                 | SCons y1 m' ys1 -> (match (eqTerm x1 y1) with
                                  | BBool b1 -> (match (eqTerm_aux xs1 ys1) with
                                               | BBool b2 -> BBool ((m = m') && b1 && b2)
                                               | _ -> BError
                                               )
                                  | _ -> BError 
                                  )
                 )

(* Definition of greater than or equal relation on Bosque terms *)
val greaterOrEq : bosqueTerm -> bosqueTerm -> Tot (x:bosqueTerm{isBool x \/ isError x})
let greaterOrEq x y = match x, y with
| BInt x1, BInt y1 -> BBool (x1 >= y1)
// FIX: Include case for Strings
| _, _ -> BError

(* Tuple projector *)
val nthTuple : index:int -> dimension:nat -> x:bosqueTerm -> Tot (y:bosqueTerm)
let rec nthTuple index dimension y = match y with
| BTuple 0 SNil -> if (index < 0 || dimension <> 0) then BError else BNone
| BTuple dimension'' (SCons x #dimension' xs) -> 
  if (index < 0 || dimension <> dimension'') then BError else
  if (index >= dimension) then BNone else
  if index = 0 then x
  else nthTuple (index-1) dimension' (BTuple dimension' xs)
| _ -> BError

// FIX: Implement the following function
// (* Record projector *)
// val nthRecord : index:int -> dimension:nat -> bosqueTerm -> Tot bosqueTerm
// let rec nthRecord index dimension y = match y with
// | BTuple 0 SNil -> if (index < 0 || dimension <> 0) then BError else BNone
// | BTuple dimension'' (SCons x #dimension' xs) -> 
//   if (index < 0 || dimension <> dimension'') then BError else
//   if (index >= dimension) then BNone else
//   if index = 0 then x
//   else nthTuple (index-1) dimension' (BTuple dimension' xs)
// | _ -> BError

(* ------------------------------------------------------------------------------------------- *)
(* Type instantiation *)
type typeUnionIntBool = x:bosqueType{subtypeOf (BUnionType BIntType BBoolType) x}
type termUnionIntBool = x:bosqueTerm{subtypeOf (BUnionType BIntType BBoolType) (getType x)} 
(* Definition of IntType *)
type termInt = x:bosqueTerm{isInt x} 
(* ------------------------------------------------------------------------------------------- *)
