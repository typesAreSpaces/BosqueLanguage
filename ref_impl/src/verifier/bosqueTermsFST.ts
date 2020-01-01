//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { MIRConceptTypeDecl, MIREntityTypeDecl } from "../compiler/mir_assembly";
import { sanitizeName } from "./util";

function printBosqueTermsFST(fstar_files_directory: string, user_defined_types_map: Map<string, MIRConceptTypeDecl | MIREntityTypeDecl>) {
    // TODO: Keep working here

    const fd = FS.openSync(fstar_files_directory + "bosqueTerms.fst", 'w');

    const program_initial = "module BosqueTerms\n\
\n\
open Sequence\n\
open BosqueTypes\n\
\n\
type bosqueTerm = \n\
| BNone : bosqueTerm\n\
| BBool : bool -> bosqueTerm\n\
| BInt : int -> bosqueTerm\n\
// No support for Float\n\
// No support for Regex\n\
| BTypedString : value:string -> content_type:bosqueType -> bosqueTerm\n\
| BGUID : string -> int -> bosqueTerm\n\
| BTuple : n:nat -> sequence bosqueTerm n -> bosqueTerm\n\
| BRecord : n:nat -> sequence bosqueTerm n -> bosqueTerm\n\
| BError : bosqueTerm\n"

    FS.writeSync(fd, program_initial);

    FS.writeSync(fd, "// User-defined terms\n");
    user_defined_types_map.forEach((value, index) => {
        if (!index.includes("NSCore")) {
            FS.writeSync(fd, "| B" + sanitizeName(index) + ": "
                + ((value.fields.length == 0) ? "" : value.fields.map(x => x.name + ": bosqueTerm -> ").join(""))
                + " bosqueTerm\n");
        }
    });

    const program_middle = "\n\
(* Definition of getType *)\n\
val getTypeSeq : n:nat -> (x: sequence bosqueTerm n) -> Tot (sequence bosqueType n) (decreases x)\n\
val getType : x:bosqueTerm -> Tot bosqueType (decreases x)\n\
let rec getType x = match x with\n\
| BNone -> BNoneType\n\
| BBool _ -> BBoolType\n\
| BInt _ -> BIntType\n\
| BTypedString _ content_type -> BTypedStringType content_type\n\
| BGUID _ _ -> BGUIDType\n\
| BTuple n y -> BTupleType false n (getTypeSeq n y)\n\
// FIX: The following is incomplete\n\
| BRecord _ _ -> BRecordType false 0 SNil\n\
| BError -> BErrorType\n"

    FS.writeSync(fd, program_middle);

    FS.writeSync(fd, "// User-defined terms\n");
    user_defined_types_map.forEach((value, index) => {
        if (!index.includes("NSCore")) {
            FS.writeSync(fd, "| B" + sanitizeName(index) + (" _").repeat(value.fields.length)
                + " -> B" + sanitizeName(index) + "Type\n");
        }
    });

    const program_rest = "and\n\
getTypeSeq n x = match x with\n\
| SNil -> SNil\n\
| SCons y m ys -> SCons (getType y) m (getTypeSeq m ys)\n\
\n\
(* --------------------------------------------------------------- *)\n\
(* Casting / Type checkers *)\n\
val isNone : bosqueTerm -> Tot bool\n\
let isNone x = match x with \n\
| BNone -> true\n\
| _ -> false\n\
\n\
val isSome : bosqueTerm -> Tot bool\n\
let isSome x = not (isNone x)\n\
\n\
val isBool : bosqueTerm -> Tot bool\n\
let isBool x = match x with \n\
| BBool _ -> true\n\
| _ -> false \n\
\n\
val isInt : bosqueTerm -> Tot bool\n\
let isInt x = match x with \n\
| BInt _ -> true\n\
| _ -> false \n\
\n\
val isNonZero : x:bosqueTerm -> Tot bool\n\
let isNonZero x = match x with \n\
| BInt 0 -> false\n\
| BInt _ -> true\n\
| _ -> false\n\
\n\
val isTypedString : bosqueType -> bosqueTerm -> Tot bool\n\
let isTypedString ty x = match x with \n\
| BTypedString _ ty' -> ty = ty'\n\
| _ -> false \n\
\n\
val isGUID : bosqueTerm -> Tot bool\n\
let isGUID x = match x with \n\
| BGUID _ _ -> true\n\
| _ -> false \n\
\n\
val isTuple : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool\n\
let isTuple b n seqTypes x = match x with\n\
| BTuple m seqTerms -> (n = m) && (BTupleType b n seqTypes) = (getType x)\n\
| _ -> false\n\
\n\
val isTuple2 : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool\n\
let isTuple2 b n seqTypes x = match x with\n\
| BTuple m seqTerms -> (BTupleType b n seqTypes) = (getType x)\n\
| _ -> false\n\
\n\
val isTuple3 : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool\n\
let isTuple3 b n seqTypes x = (BTupleType b n seqTypes) = (getType x)\n\
\n\
val isRecord : b:bool -> n:nat -> (sequence bosqueType n) -> x:bosqueTerm -> Tot bool\n\
let isRecord b n seqTypes x = (BRecordType b n seqTypes) = (getType x)\n\
\n\
val isError : bosqueTerm -> Tot bool\n\
let isError x = match x with \n\
| BError -> true\n\
| _ -> false \n\
(* --------------------------------------------------------------- *)\n\
\n\
(* ------------------------------------------------------------------------ *)\n\
(* Extractors *)\n\
\n\
(* This is mainly used inside conditionals (in the fstar programming language) \n\
and assertions (in the z3 smt solver) *)\n\
val extractBool : x:bosqueTerm{isBool x} -> Tot bool\n\
let extractBool x = match x with\n\
| BBool y -> y \n\
\n\
val extractBool2 : x:bosqueTerm{BBoolType = (getType x)} -> Tot bool\n\
let extractBool2 x = match x with\n\
| BBool y -> y \n\
\n\
val extractBool3 : x:bosqueTerm{subtypeOf BBoolType (getType x)} -> Tot bool\n\
let extractBool3 x = match x with\n\
| BBool y -> y \n\
(* ------------------------------------------------------------------------ *)\n\
\n\
(* Boolean Operations *)\n\
\n\
(* Definition of equality relation on Bosque terms *)\n\
val op_eqTerm_aux : n:nat \n\
    -> (x:sequence bosqueTerm n) \n\
    -> sequence bosqueTerm n\n\
    -> Tot (z:bosqueTerm{isBool z}) (decreases x)\n\
val op_eqTerm : x:bosqueTerm\n\
      -> bosqueTerm\n\
      -> Tot (z:bosqueTerm{isBool z})  (decreases x)\n\
let rec op_eqTerm x y = match x, y with\n\
| BNone, BNone -> BBool true\n\
| BBool x1, BBool y1 -> BBool (x1 = y1)\n\
| BInt x1, BInt y1 -> BBool (x1 = y1)\n\
| BTypedString s1 ty1, BTypedString s2 ty2 -> BBool (s1 = s2 && ty1 = ty2)\n\
| BGUID s1 n1, BGUID s2 n2 -> BBool (s1 = s2 && n1 = n2)\n\
| BTuple n1 seq1, BTuple n2 seq2 -> if (n1 <> n2) then BBool (false)\n\
                                    else op_eqTerm_aux n1 seq1 seq2\n\
// FIX: Include case for BRecord\n\
// | BError, BError -> BBool true\n\
| _, _ -> BBool (false)\n\
and \n\
op_eqTerm_aux n x y = match x with\n\
| SNil -> (match y with\n\
          | SNil -> BBool true\n\
          | _ -> BBool (false)\n\
          )\n\
| SCons x1 m xs1 -> (match y with\n\
                    | SNil -> BBool (false)\n\
                    | SCons y1 m' ys1 -> (match (op_eqTerm x1 y1) with\n\
                                         | BBool b1 -> (match (op_eqTerm_aux m xs1 ys1) with\n\
                                                       | BBool b2 -> BBool ((m = m') && b1 && b2)\n\
                                                       | _ -> BBool (false)\n\
                                                       )\n\
                                         | _ -> BBool (false)\n\
                                         )\n\
                    )\n\
\n\
val op_notEqTerm : x:bosqueTerm\n\
      -> bosqueTerm\n\
      -> Tot (z:bosqueTerm{isBool z})  (decreases x)\n\
let op_notEqTerm x y = match (op_eqTerm x y) with\n\
| BBool result -> BBool (not result)\n\
\n\
val op_not : x:bosqueTerm{isBool x} -> Tot (z:bosqueTerm{isBool z})\n\
let op_not x = match x with\n\
| BBool x1 -> BBool (not x1)\n\
\n\
val op_and : x:bosqueTerm{isBool x} -> y:bosqueTerm{isBool y} -> Tot (z:bosqueTerm{isBool z})\n\
let op_and x y = match x, y with\n\
| BBool x1, BBool y1 -> BBool (x1 && y1)\n\
\n\
val op_or : x:bosqueTerm{isBool x} -> y:bosqueTerm{isBool y} -> Tot (z:bosqueTerm{isBool z})\n\
let op_or x y = match x, y with\n\
| BBool x1, BBool y1 -> BBool (x1 || y1)\n\
\n\
(* Number operations *)\n\
val op_mult : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isInt z})\n\
let op_mult x y = match x, y with\n\
| BInt x1, BInt y1 -> BInt (op_Multiply x1 y1)\n\
\n\
val op_sub : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isInt z})\n\
let op_sub x y = match x, y with\n\
| BInt x1, BInt y1 -> BInt (x1 - y1)\n\
\n\
val op_add : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isInt z})\n\
let op_add x y = match x, y with\n\
| BInt x1, BInt y1 -> BInt (x1 + y1)\n\
\n\
val op_neg : x:bosqueTerm{isInt x} -> Tot (z:bosqueTerm{isInt z})\n\
let op_neg x = match x with\n\
| BInt x1 -> BInt (-x1)\n\
\n\
(* Another option *)\n\
val op_neg2 : x:bosqueTerm{BIntType = (getType x)} -> Tot (y:bosqueTerm{squash (BIntType == (getType y))})\n\
let op_neg2 x = match x with\n\
| BInt x1 -> BInt (-x1)\n\
\n\
val op_mod : x:bosqueTerm{isInt x} -> y:bosqueTerm{isNonZero y} -> Tot (z:bosqueTerm{isInt z})\n\
let op_mod x y = match x, y with\n\
| BInt x1, BInt y1 -> BInt (x1 % y1)\n\
\n\
val op_div : x:bosqueTerm{isInt x} -> y:bosqueTerm{isNonZero y} -> Tot (z:bosqueTerm{isInt z})\n\
let op_div x y = match x, y with\n\
| BInt x1, BInt y1 -> BInt (x1 / y1)\n\
\n\
// --------------------------------------------------------------------------------------------------\n\
// TODO: Include case for Strings\n\
val op_greaterOrEq : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isBool z})\n\
let op_greaterOrEq x y = match x, y with\n\
| BInt x1, BInt y1 -> BBool (x1 >= y1) \n\
\n\
val op_greater : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isBool z}) \n\
let op_greater x y = match x, y with\n\
| BInt x1, BInt y1 -> BBool (x1 > y1) \n\
\n\
val op_lessOrEq : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isBool z}) \n\
let op_lessOrEq x y = match x, y with\n\
| BInt x1, BInt y1 -> BBool (x1 <= y1) \n\
\n\
val op_less : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> Tot (z:bosqueTerm{isBool z}) \n\
let op_less x y = match x, y with\n\
| BInt x1, BInt y1 -> BBool (x1 < y1) \n\
// --------------------------------------------------------------------------------------------------\n\
\n\
(* Tuple Type projector *)\n\
val nthTupleType : index:int -> dimension:nat -> x:bosqueTerm -> Tot (bosqueType)\n\
let rec nthTupleType index dimension y = match y with\n\
| BTuple 0 SNil -> if (index < 0 || dimension <> 0) then BErrorType else BNoneType\n\
| BTuple dimension'' (SCons x dimension' xs) -> \n\
  if (index < 0 || dimension <> dimension'') then BErrorType else\n\
  if (index >= dimension) then BNoneType else\n\
  if index = 0 then getType x\n\
  else nthTupleType (index-1) dimension' (BTuple dimension' xs)\n\
| _ -> BErrorType\n\
\n\
(* Tuple projector *)\n\
val nthTuple : index:int -> dimension:nat -> x:bosqueTerm -> Tot (y:bosqueTerm)\n\
let rec nthTuple index dimension y = match y with\n\
| BTuple 0 SNil -> if (index < 0 || dimension <> 0) then BError else BNone\n\
| BTuple dimension'' (SCons x' dimension' xs') -> \n\
  if (index < 0 || dimension <> dimension'') then BError else\n\
  if (index >= dimension) then BNone else\n\
  if index = 0 then x'\n\
  else nthTuple (index-1) dimension' (BTuple dimension' xs')\n\
| _ -> BError\n\
\n\
// TODO: Implement the Record Projector\n\
// (* Record projector *)\n\
// val nthRecord : index:int -> dimension:nat -> bosqueTerm -> Tot bosqueTerm\n\
// let rec nthRecord index dimension y = match y with\n\
// | BTuple 0 SNil -> if (index < 0 || dimension <> 0) then BError else BNone\n\
// | BTuple dimension'' (SCons x #dimension' xs) -> \n\
//   if (index < 0 || dimension <> dimension'') then BError else\n\
//   if (index >= dimension) then BNone else\n\
//   if index = 0 then x\n\
//   else nthTuple (index-1) dimension' (BTuple dimension' xs)\n\
// | _ -> BError";

    FS.writeSync(fd, program_rest);
}

export { printBosqueTermsFST }