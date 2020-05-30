module BosqueTypes

open Sequence
module Util=Util

// Convention with UnionTerm: 
// 1) its elements should be unique
// 2) There is a unique way to represent any union (normal form)
// the latter was needed for eqType
type bosqueType =
| BAnyType
| BSomeType
| BTruthyType
| BNoneType
| BUnionType : bosqueType -> bosqueType -> bosqueType
| BParseableType
| BBoolType
| BIntType
| BFloatType // Bad news, FStar doesn't provide support for this type
| BRegexType // Bad news, FStar doesn't provide support for this type
| BTypedStringType : bosqueType -> bosqueType
| BGUIDType
// The bool indicates if the Tuple is open or not
| BTupleType : bool -> n:nat -> sequence bosqueType n -> bosqueType
// FIX: The following is wrong
// The bool indicates if the Record is open or not
| BRecordType : bool -> n:nat -> sequence bosqueType n -> bosqueType
// FIX: The following is incomplete
| BFunctionType
// FIX: The following is incomplete
| BObjectType
// FIX: The following is incomplete
| BEnumType 
// FIX: The following is incomplete
| BCustomKeyType
// FIX: The following is incomplete
| BKeyedType
| BErrorType

(* Definition of equality relation on Bosque types *)
val eqTypeSeq : #n:nat -> (x:sequence bosqueType n) -> sequence bosqueType n -> Tot bool (decreases x)
val eqType : x:bosqueType -> bosqueType -> Tot bool (decreases x)
let rec eqType x y = match x, y with
| BAnyType, BAnyType -> true
| BSomeType, BSomeType -> true
| BTruthyType, BTruthyType -> true
| BNoneType, BNoneType -> true
// The following might be incomplete, but if Unions are normalized then it is complete
| BUnionType x1 x2 , BUnionType y1 y2 -> eqType x1 y1 && eqType x2 y2
| BParseableType, BParseableType -> true 
| BBoolType, BBoolType -> true
| BIntType, BIntType -> true
| BFloatType, BFloatType -> true
| BRegexType, BRegexType -> true
| BTypedStringType t1, BTypedStringType t2 -> (eqType t1 t2)
| BGUIDType, BGUIDType -> true 
| BTupleType b1 n1 seq1, BTupleType b2 n2 seq2 -> (b1 = b2) && (n1 = n2) && eqTypeSeq seq1 seq2
// FIX: The following is wrong
| BRecordType _ _ _, BRecordType _ _ _ -> true
// FIX: The following is wrong
| BFunctionType, BFunctionType -> true
// FIX: The following is wrong
| BObjectType, BObjectType -> true
// FIX: The following is wrong
| BEnumType, BEnumType -> true
// FIX: The following is wrong
| BCustomKeyType, BCustomKeyType -> true
// FIX: The following is wrong
| BKeyedType, BKeyedType -> true
| BErrorType, BErrorType -> true
| _, _ -> false
and
eqTypeSeq #n x y = match x with
| SNil -> (match y with 
  | SNil -> true
  | _ -> false
  )
| SCons x1 xs1 -> (match y with 
                 | SNil -> false
                 | SCons y1 ys1 -> eqType x1 y1 && eqTypeSeq xs1 ys1  
                 )

(* Definition to encode the subtype relation on Bosque types 
   i.e. forall x y . subtypeOf x y <===> x :> y *)
val subtypeOfSeq : #n:nat -> (x:sequence bosqueType n) -> sequence bosqueType n -> Tot bool (decreases x)
val subtypeOf : x:bosqueType -> bosqueType -> Tot bool (decreases x)
let rec subtypeOf x y = match x, y with
| BAnyType, _ -> true
| BNoneType, BNoneType -> true
| BIntType, BIntType -> true
| BBoolType, BBoolType -> true
| BUnionType x1 y1, BUnionType x2 y2 -> (subtypeOf x1 x2 || subtypeOf y1 x2)
  && (subtypeOf x1 y2 || subtypeOf y1 y2)
| BUnionType x1 y1, z -> subtypeOf x1 z || subtypeOf y1 z 
| BTupleType b1 0 SNil, BTupleType b2 0 SNil -> b1 = b2
| BTupleType b1 0 SNil, BTupleType _ _ _ -> b1
| BTupleType b1 n1 seq1, BTupleType b2 n2 seq2 -> 
  if b1 then 
    if (n1 > n2) then false
    else subtypeOfSeq seq1 (take n1 seq2)
  else 
    if b2 then false 
    else 
      if (n1 = n2) then subtypeOfSeq seq1 seq2
      else false 
| BErrorType, BErrorType -> true
| _, _ -> false
and 
subtypeOfSeq #n x y = match x with
| SNil -> (match y with
  | SNil -> true
  | _ -> false
  )
| SCons x1 xs1 -> (match y with 
                 | SNil -> false
                 | SCons y1 ys1 -> eqType x1 y1 && eqTypeSeq xs1 ys1  
                 )