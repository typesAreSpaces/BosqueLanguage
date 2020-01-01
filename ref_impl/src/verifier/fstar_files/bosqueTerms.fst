module BosqueTerms

open Sequence
open BosqueTypes

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
// User-defined terms
| BnSMain__Musician: artist: bosqueTerm -> instrument: bosqueTerm ->  bosqueTerm
| BnSMain__Artist: id: bosqueTerm -> isGood: bosqueTerm -> lastName: bosqueTerm -> name: bosqueTerm -> player: bosqueTerm ->  bosqueTerm
| BnSMain__PlayerMark: mark: bosqueTerm ->  bosqueTerm

(* Definition of getType *)
val getTypeSeq : n:nat -> (x: sequence bosqueTerm n) -> Tot (sequence bosqueType n) (decreases x)
val getType : x:bosqueTerm -> Tot bosqueType (decreases x)
let rec getType x = match x with
| BNone -> BNoneType
| BBool _ -> BBoolType
| BInt _ -> BIntType
| BTypedString _ content_type -> BTypedStringType content_type
| BGUID _ _ -> BGUIDType
| BTuple n y -> BTupleType false n (getTypeSeq n y)
// FIX: The following is incomplete
| BRecord _ _ -> BRecordType false 0 SNil
| BError -> BErrorType
// User-defined terms
| BnSMain__Musician _ _ -> BnSMain__MusicianType
| BnSMain__Artist _ _ _ _ _ -> BnSMain__ArtistType
| BnSMain__PlayerMark _ -> BnSMain__PlayerMarkType
and
getTypeSeq n x = match x with
| SNil -> SNil
| SCons y m ys -> SCons (getType y) m (getTypeSeq m ys)

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

val isNonZero : x:bosqueTerm -> Tot bool
let isNonZero x = match x with 
| BInt 0 -> false
| BInt _ -> true
| _ -> false

val isTypedString : bosqueType -> bosqueTerm -> Tot bool
let isTypedString ty x = match x with 
| BTypedString _ ty' -> ty = ty'
| _ -> false 

val isGUID : bosqueTerm -> Tot bool
let isGUID x = match x with 
| BGUID _ _ -> true
| _ -> false 

val isTuple : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool
let isTuple b n seqTypes x = match x with
| BTuple m seqTerms -> (n = m) && (BTupleType b n seqTypes) = (getType x)
| _ -> false

val isTuple2 : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool
let isTuple2 b n seqTypes x = match x with
| BTuple m seqTerms -> (BTupleType b n seqTypes) = (getType x)
| _ -> false

val isTuple3 : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool
let isTuple3 b n seqTypes x = (BTupleType b n seqTypes) = (getType x)

val isRecord : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool
let isRecord b n seqTypes x = (BRecordType b n seqTypes) = (getType x)

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

val extractBool2 : x:bosqueTerm{BBoolType = (getType x)} -> Tot bool
let extractBool2 x = match x with
| BBool y -> y 

val extractBool3 : x:bosqueTerm{subtypeOf BBoolType (getType x)} -> Tot bool
let extractBool3 x = match x with
| BBool y -> y 
(* ------------------------------------------------------------------------ *)

(* Boolean Operations *)

(* Definition of equality relation on Bosque terms *)
val op_eqTerm_aux : n:nat 
    -> (x:sequence bosqueTerm n) 
    -> sequence bosqueTerm n
    -> Tot (z:bosqueTerm{isBool z}) (decreases x)
val op_eqTerm : x:bosqueTerm
      -> bosqueTerm
      -> Tot (z:bosqueTerm{isBool z})  (decreases x)
let rec op_eqTerm x y = match x, y with
| BNone, BNone -> BBool true
| BBool x1, BBool y1 -> BBool (x1 = y1)
| BInt x1, BInt y1 -> BBool (x1 = y1)
| BTypedString s1 ty1, BTypedString s2 ty2 -> BBool (s1 = s2 && ty1 = ty2)
| BGUID s1 n1, BGUID s2 n2 -> BBool (s1 = s2 && n1 = n2)
| BTuple n1 seq1, BTuple n2 seq2 -> if (n1 <> n2) then BBool (false)
                                    else op_eqTerm_aux n1 seq1 seq2
// FIX: Include case for BRecord
// | BError, BError -> BBool true
| _, _ -> BBool (false)
and 
op_eqTerm_aux n x y = match x with
| SNil -> (match y with
          | SNil -> BBool true
          | _ -> BBool (false)
          )
| SCons x1 m xs1 -> (match y with
                    | SNil -> BBool (false)
                    | SCons y1 m' ys1 -> (match (op_eqTerm x1 y1) with
                                         | BBool b1 -> (match (op_eqTerm_aux m xs1 ys1) with
                                                       | BBool b2 -> BBool ((m = m') && b1 && b2)
                                                       | _ -> BBool (false)
                                                       )
                                         | _ -> BBool (false)
                                         )
                    )

val op_notEqTerm : x:bosqueTerm
      -> bosqueTerm
      -> Tot (z:bosqueTerm{isBool z})  (decreases x)
let op_notEqTerm x y = match (op_eqTerm x y) with
| BBool result -> BBool (not result)

val op_not : x:bosqueTerm{isBool x} -> Tot (z:bosqueTerm{isBool z})
let op_not x = match x with
| BBool x1 -> BBool (not x1)

val op_and : x:bosqueTerm{isBool x} -> y:bosqueTerm{isBool y} -> Tot (z:bosqueTerm{isBool z})
let op_and x y = match x, y with
| BBool x1, BBool y1 -> BBool (x1 && y1)

val op_or : x:bosqueTerm{isBool x} -> y:bosqueTerm{isBool y} -> Tot (z:bosqueTerm{isBool z})
let op_or x y = match x, y with
| BBool x1, BBool y1 -> BBool (x1 || y1)

(* Number operations *)
val op_mult : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isInt z})
let op_mult x y = match x, y with
| BInt x1, BInt y1 -> BInt (op_Multiply x1 y1)

val op_sub : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isInt z})
let op_sub x y = match x, y with
| BInt x1, BInt y1 -> BInt (x1 - y1)

val op_add : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isInt z})
let op_add x y = match x, y with
| BInt x1, BInt y1 -> BInt (x1 + y1)

val op_neg : x:bosqueTerm{isInt x} -> Tot (z:bosqueTerm{isInt z})
let op_neg x = match x with
| BInt x1 -> BInt (-x1)

(* Another option *)
val op_neg2 : x:bosqueTerm{BIntType = (getType x)} -> Tot (y:bosqueTerm{squash (BIntType == (getType y))})
let op_neg2 x = match x with
| BInt x1 -> BInt (-x1)

val op_mod : x:bosqueTerm{isInt x} -> y:bosqueTerm{isNonZero y} -> Tot (z:bosqueTerm{isInt z})
let op_mod x y = match x, y with
| BInt x1, BInt y1 -> BInt (x1 % y1)

val op_div : x:bosqueTerm{isInt x} -> y:bosqueTerm{isNonZero y} -> Tot (z:bosqueTerm{isInt z})
let op_div x y = match x, y with
| BInt x1, BInt y1 -> BInt (x1 / y1)

// --------------------------------------------------------------------------------------------------
// TODO: Include case for Strings
val op_greaterOrEq : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isBool z})
let op_greaterOrEq x y = match x, y with
| BInt x1, BInt y1 -> BBool (x1 >= y1) 

val op_greater : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isBool z}) 
let op_greater x y = match x, y with
| BInt x1, BInt y1 -> BBool (x1 > y1) 

val op_lessOrEq : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isBool z}) 
let op_lessOrEq x y = match x, y with
| BInt x1, BInt y1 -> BBool (x1 <= y1) 

val op_less : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isBool z}) 
let op_less x y = match x, y with
| BInt x1, BInt y1 -> BBool (x1 < y1) 
// --------------------------------------------------------------------------------------------------

(* Tuple Type projector *)
val nthTupleType : index:int -> dimension:nat -> x:bosqueTerm -> Tot (bosqueType)
let rec nthTupleType index dimension y = match y with
| BTuple 0 SNil -> if (index < 0 || dimension <> 0) then BErrorType else BNoneType
| BTuple dimension'' (SCons x dimension' xs) -> 
  if (index < 0 || dimension <> dimension'') then BErrorType else
  if (index >= dimension) then BNoneType else
  if index = 0 then getType x
  else nthTupleType (index-1) dimension' (BTuple dimension' xs)
| _ -> BErrorType

(* Tuple projector *)
val nthTuple : index:int -> dimension:nat -> x:bosqueTerm -> Tot (y:bosqueTerm)
let rec nthTuple index dimension y = match y with
| BTuple 0 SNil -> if (index < 0 || dimension <> 0) then BError else BNone
| BTuple dimension'' (SCons x' dimension' xs') -> 
  if (index < 0 || dimension <> dimension'') then BError else
  if (index >= dimension) then BNone else
  if index = 0 then x'
  else nthTuple (index-1) dimension' (BTuple dimension' xs')
| _ -> BError

// TODO: Implement the Record Projector
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