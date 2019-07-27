module BosqueTerms

open Sequence

(* Dynamic: depends on the 
   entities created by user *) 
noeq type bosqueTerm = 
| BError : bosqueTerm
| BNone : bosqueTerm
| BInt : int -> bosqueTerm
| BBool : bool -> bosqueTerm
| BTuple : n:nat -> sequence bosqueTerm n -> bosqueTerm 

(* -------------------------------------- *)
(* Type checkers *)
val isBool : bosqueTerm -> bool
let isBool x = match x with 
| BBool _ -> true
| _ -> false 

val isInt : bosqueTerm -> bool
let isInt x = match x with 
| BInt _ -> true
| _ -> false 

val isTuple : n:nat -> x:bosqueTerm -> bool
let isTuple n x = match x with
| BTuple m _ -> n = m
| _ -> false
(* -------------------------------------- *)

(* Definition of equality relation on Bosque terms *)
val eqTerm : bosqueTerm -> bosqueTerm -> bosqueTerm
let eqTerm x y = match x, y with
// | BError, BError -> BBool true
| BNone, BNone -> BBool true
| BInt x1, BInt y1 -> BBool (x1 = y1)
| BBool x1, BBool y1 -> BBool (x1 = y1)
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

(* ----------------------------------------------------------------------------------------- *)
(* Extractors *)

(* This is mainly used inside conditionals (in the fstar programming language) 
   and assertions (in the z3 smt solver) *)
val extractBool : x:bosqueTerm{isBool x} -> bool
let extractBool x = match x with
| BBool y -> y

val extractTuple : n:nat -> x:bosqueTerm{isTuple n x} -> sequence bosqueTerm n
let extractTuple n x = match x with
| BTuple _ seq -> seq
(* ----------------------------------------------------------------------------------------- *)
