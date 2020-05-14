"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const FS = require("fs");
const util_1 = require("./util");
const translator_bosque_fstar_1 = require("./translator_bosque_fstar");
// TODO: Include parameter to print extended types
function printBosqueTypesFST(fstar_files_directory, user_defined_types) {
    const fd = FS.openSync(fstar_files_directory + "/bosqueTypes.fst", 'w');
    const fstar_program_core_decl = "module BosqueTypes\n\
  \n\
  open Sequence\n\
  open List\n\
  module Util=Util\n\
  \n\
  // Convention with UnionTerm: \n\
  // 1) its elements should be unique\n\
  // 2) There is a unique way to represent any union (normal form)\n\
  // the latter was needed for eqType\n\
  type bosqueType =\n\
    | BAnyType\n\
    | BSomeType\n\
    | BTruthyType\n\
    | BNoneType\n\
    | BUnionType : bosqueType -> bosqueType -> bosqueType\n\
    | BParsableType\n\
    | BBoolType\n\
    | BIntType\n\
    | BFloatType // Bad news, FStar doesn't provide support for this type\n\
    | BRegexType // Bad news, FStar doesn't provide support for this type\n\
    | BTypedStringType : bosqueType -> bosqueType\n\
    | BGUIDType\n\
  // The bool indicates if the Tuple is open or not\n\
    | BTupleType : bool -> n:nat -> sequence bosqueType n -> bosqueType\n\
  // The bool indicates if the Record is open or not\n\
    | BRecordType : bool -> n:nat -> sequence string n -> sequence bosqueType n -> bosqueType\n\
  // -----------------------------------\n\
  // FIX: The following are incomplete\n\
    | BFunctionType\n\
    | BObjectType\n\
    | BEnumType \n\
    | BCustomKeyType\n\
    | BKeyedType\n\
  // -----------------------------------\n\
    | BErrorType\n\
    | BListType : bosqueType -> bosqueType";
    FS.writeSync(fd, fstar_program_core_decl);
    FS.writeSync(fd, "// User-defined types\n");
    user_defined_types.forEach((_, index) => {
        if (!index.includes("NSCore")) {
            FS.writeSync(fd, "| B" + util_1.sanitizeName(index) + "Type\n");
        }
    });
    FS.writeSync(fd, "\n");
    const fstar_program_subtypeof_initial = "(* Definition of equality relation on Bosque types *)\n\
  val eqTypeSeq : n:nat -> sequence bosqueType n -> sequence bosqueType n -> Tot bool \n\
  let rec eqTypeSeq n x y = match x with\n\
    | SNil -> (match y with \n\
      | SNil -> true\n\
      | _ -> false\n\
    )\n\
    | SCons x1 m xs1 -> (match y with \n\
      | SNil -> false\n\
      | SCons y1 m' ys1 -> (m = m') && x1 = y1 && eqTypeSeq m xs1 ys1\n\
                    )\n\
val eqTypeList : list bosqueType → list bosqueType → Tot bool\n\
let rec eqTypeList x y = match x with\n\
  | LNil → (match y with\n\
    | LNil → true\n\
    | _ → false\n\
  )\n\
  | LCons x1 xs1 → (match y with\n\
    | LNil → false\n\
    | LCons y1 ys1 → x1 = y1 && eqTypeList xs1 ys1\n\
  )\n\
\n\
(* Definition to encode the subtype relation on Bosque types \n\
  i.e.forall x y.subtypeOf x y <===> x :> y *) \n\
val subtypeOfList: x: list bosqueType -> list bosqueType -> Tot bool(decreases x)\n\
val subtypeOfSeq: n: nat -> x: sequence bosqueType n -> sequence bosqueType n -> Tot bool(decreases x) \n\
val subtypeOf: x: bosqueType -> bosqueType -> Tot bool(decreases x) \n\
let rec subtypeOf x y = match x, y with\n\
  | BAnyType, _ -> true\n\
  | BSomeType, _ -> true\n\
  | BTruthyType, BNoneType -> true\n\
  | BNoneType, BNoneType -> true\n\
  | BUnionType x1 y1, BUnionType x2 y2 -> (x1 = x2 && subtypeOf y1 y2) || (subtypeOf y1 (BUnionType x2 y2))\n\
  | BUnionType x1 y1, z -> subtypeOf x1 z || subtypeOf y1 z \n\
  | BParsableType, BParsableType -> true\n\
  | BBoolType, BBoolType -> true\n\
  | BIntType, BIntType -> true\n\
// | BFloatType, ? -> ?\n\
// | BRegexType, ? -> ?\n\
  | BTypedStringType t1, BTypedStringType t2 -> subtypeOf t1 t2\n\
  | BTupleType b1 0 SNil, BTupleType b2 0 SNil -> b1 = b2\n\
  | BTupleType b1 0 SNil, BTupleType _ _ _ -> b1\n\
  | BTupleType b1 n1 seq1, BTupleType b2 n2 seq2 -> \n\
if b1 then \n\
if (n1 > n2) then false\n\
else b1 && (n1 <= n2) && subtypeOfSeq n1 seq1(takeSequence n2 n1 seq2) \n\
else \n\
if b2 then false\n\
else\n\
if (n1 = n2) then(not b1) && (not b2) && (n1 = n2) && subtypeOfSeq n1 seq1 seq2\n\
else false \n\
  | BRecordType b1 0 SNil SNil, BRecordType b2 0 SNil SNil -> b1 = b2\n\
  | BRecordType b1 0 SNil SNil, BRecordType _ _ _ _ -> b1\n\
  | BRecordType b1 n1 _ seq1, BRecordType b2 n2 _ seq2 ->\n\
if b1 then\n\
if (n1 > n2) then false\n\
else b1 && (n1 <= n2) && subtypeOfSeq n1 seq1(takeSequence n2 n1 seq2)\n\
else\n\
if b2 then false\n\
else\n\
if (n1 = n2) then(not b1) && (not b2) && (n1 = n2) && subtypeOfSeq n1 seq1 seq2\n\
else false\n\
// | BFunctionType, ? -> ?\n\
// | BObjectType, ? -> ?\n\
// | BEnumType, ? -> ?\n\
// | BCustomType, ? -> ?\n\
// | BKeyedType, ? -> ?\n\
  | BListType t1 , BListType t2 -> subtypeOf t1 t2\n";
    FS.writeSync(fd, fstar_program_subtypeof_initial);
    FS.writeSync(fd, "// User-defined types\n");
    FS.writeSync(fd, "// Reflexivity relation\n");
    user_defined_types.forEach((_, index) => {
        if (!index.includes("NSCore")) {
            const element = "B" + util_1.sanitizeName(index) + "Type";
            FS.writeSync(fd, "| " + element + ", " + element + " -> true\n");
        }
    });
    FS.writeSync(fd, "// Provide relation\n");
    user_defined_types.forEach((value, index) => {
        let value_to_type;
        if (index.includes("NSCore"))
            value_to_type = translator_bosque_fstar_1.TranslatorBosqueFStar.stringVarToTypeExpr(index).fstar_type_encoding;
        else
            value_to_type = "B" + util_1.sanitizeName(index) + "Type";
        value.forEach(element => FS.writeSync(fd, "| " + value_to_type + ", B" + util_1.sanitizeName(element) + "Type -> true\n"));
    });
    const fstar_program_subtypeof_rest = "| _, _ -> false\n\
and \n\
subtypeOfSeq n x y = match x with\n\
  | SNil -> (match y with\n\
    | SNil -> true\n\
    | _ -> false\n\
  ) \n\
  | SCons x1 m xs1 -> (match y with \n\
    | SNil -> false\n\
    | SCons y1 m' ys1 -> (m = m') && (subtypeOf x1 y1) && subtypeOfSeq m xs1 ys1  \n\
                    )\n\
and\n\
subtypeOfList x y = match x with\n\
  | LNil → (match y with\n\
    | LNil → true\n\
    | _ → false\n\
  )\n\
  | LCons x1 xs1 → (match y with\n\
    | LNil → false\n\
    | LCons y1 ys1 → subtypeOf x1 y1 && subtypeOfList xs1 ys1\n\
  )";
    FS.writeSync(fd, fstar_program_subtypeof_rest);
    FS.closeSync(fd);
}
exports.printBosqueTypesFST = printBosqueTypesFST;
//# sourceMappingURL=bosqueTypesFST.js.map