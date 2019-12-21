//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";

// TODO: Include parameter to print extended types

function printBosqueTypesFST() {

    const fd = FS.openSync("fstar_files/bosqueTypes.fst", 'w');

    const fstar_program_core_decl = "module BosqueTypes\n\
\n\
open Sequence\n\
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
| BParseableType\n\
| BBoolType\n\
| BIntType\n\
| BFloatType // Bad news, FStar doesn't provide support for this type\n\
| BRegexType // Bad news, FStar doesn't provide support for this type\n\
| BTypedStringType : bosqueType -> bosqueType\n\
| BGUIDType\n\
// The bool indicates if the Tuple is open or not\n\
| BTupleType : bool -> n:nat -> sequence bosqueType n -> bosqueType\n\
// FIX: The following is wrong\n\
// The bool indicates if the Record is open or not\n\
| BRecordType : bool -> n:nat -> sequence bosqueType n -> bosqueType\n\
// FIX: The following is incomplete\n\
| BFunctionType\n\
// FIX: The following is incomplete\n\
| BObjectType\n\
// FIX: The following is incomplete\n\
| BEnumType \n\
// FIX: The following is incomplete\n\
| BCustomKeyType\n\
// FIX: The following is incomplete\n\
| BKeyedType\n\
| BErrorType\n";

// // User-defined types\n\
// | BnSMain__PlayerMarkType\n\
// | BnSMain__ArtistType\n\
// | BnSMain__MusicianType\n\
// \n\

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
\n\
(* Definition to encode the subtype relation on Bosque types \n\
   i.e.forall x y.subtypeOf x y <===> x :> y *) \n\
val subtypeOfSeq: n: nat -> x: sequence bosqueType n -> sequence bosqueType n -> Tot bool(decreases x) \n\
val subtypeOf: x: bosqueType -> bosqueType -> Tot bool(decreases x) \n\
let rec subtypeOf x y = match x, y with\n\
| BAnyType, _ -> true\n\
| BSomeType, BAnyType -> false\n\
| BSomeType, BTruthyType -> false\n\
| BSomeType, BNoneType -> false\n\
| BSomeType, _ -> true\n\
| BTruthyType, BNoneType -> true\n\
| BNoneType, BNoneType -> true\n\
| BUnionType x1 y1, BUnionType x2 y2 -> (subtypeOf x1 x2 || subtypeOf x1 y2) && (subtypeOf y1 x2 || subtypeOf y1 y2) \n\
| BUnionType x1 y1, z -> subtypeOf x1 z || subtypeOf y1 z \n\
// | BParseabletype, ? -> ?\n\
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
        else b1 && (n1 <= n2) && subtypeOfSeq n1 seq1(take n2 n1 seq2) \n\
    else \n\
        if b2 then false \n\
        else \n\
            if (n1 = n2) then(not b1) && (not b2) && (n1 = n2) && subtypeOfSeq n1 seq1 seq2\n\
            else false \n\
// | BRecordType, ? -> ?\n\
// | BFunctionType, ? -> ?\n\
// | BObjectType, ? -> ?\n\
// | BEnumType, ? -> ?\n\
// | BCustomType, ? -> ?\n\
// | BKeyedType, ? -> ?\n";

// // User-defined types: TODO: Implement proper subtyping\n\
// // relations via the provide relation\n\
// | BnSMain__PlayerMarkType, BnSMain__PlayerMarkType -> true\n\
// | BnSMain__ArtistType, BnSMain__ArtistType -> true\n\
// | BnSMain__MusicianType, BnSMain__MusicianType -> true\n\
// \n\

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
                       ) \n";

    const fstar_program = fstar_program_core_decl + "\n" + fstar_program_subtypeof_initial + "\n" + fstar_program_subtypeof_rest;

    FS.writeSync(fd, fstar_program);
    FS.closeSync(fd);
}

export { printBosqueTypesFST }