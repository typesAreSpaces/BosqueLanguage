module Util

open Sequence
open BosqueTerms
open BosqueTypes

(* Definition of getType *)
val getType_aux : #n:nat -> (x: sequence bosqueTerm n) -> Tot (sequence bosqueType n) (decreases x)
val getType : x:bosqueTerm -> Tot bosqueType (decreases x)
let rec getType x = match x with
| BNone -> BTypeNone
| BInt _ -> BTypeInt
| BBool _ -> BTypeBool
| BTuple n SNil -> if (n <> 0) then BTypeError else BTypeEmptyTuple false 
| BTuple n (SCons y ys) -> BTypeTuple false n (getType_aux #n (SCons y ys))
| BError -> BTypeError
and 
getType_aux #n x = match x with
| SNil -> SNil
| SCons y ys -> SCons (getType y) (getType_aux ys)

(* --------------------------------------------------------------- *)
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

(* ------------------------------------------------------------------------------------------- *)
(* Type instantiation *)
type typeUnionIntBool = x:bosqueType{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) x}
type termUnionIntBool = x:bosqueTerm{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (getType x)} 
(* Definition of IntType *)
type termInt = x:bosqueTerm{isInt x} 
(* ------------------------------------------------------------------------------------------- *)
