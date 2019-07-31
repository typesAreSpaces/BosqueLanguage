module BosqueTypes

open Sequence
module Util=Util

// Convention with UnionTerm: 
// 1) its elements should be unique
// 2) There is a unique way to represent any union (normal form)
// the latter was needed for eqType
type bosqueType =
| BAnyType
| BNoneType
| BIntType
| BBoolType
| BUnionType : bosqueType -> bosqueType -> bosqueType
// The bool indicates if the Empty Tuple is open or not
| BEmptyTupleType : bool -> bosqueType
// The bool indicates if the Tuple is open or not
| BTupleType : bool -> n:nat -> sequence bosqueType n -> bosqueType
| BErrorType

(* Definition of equality relation on Bosque types *)
val eqTypeSeq : #n:nat -> (x:sequence bosqueType n) -> sequence bosqueType n -> Tot bool (decreases x)
val eqType : x:bosqueType -> bosqueType -> Tot bool (decreases x)
let rec eqType x y = match x, y with
| BAnyType, BAnyType -> true
| BNoneType, BNoneType -> true
| BIntType, BIntType -> true
| BBoolType, BBoolType -> true
// The following might be incomplete, but if Unions are normalized then it is complete
| BUnionType x1 x2 , BUnionType y1 y2 -> eqType x1 y1 && eqType x2 y2
| BUnionType _ _, _ -> false
| BEmptyTupleType b1, BEmptyTupleType b2 -> b1 = b2 
| BTupleType b1 n1 seq1, BTupleType b2 n2 seq2 -> (b1 = b2) && (n1 = n2) && eqTypeSeq seq1 seq2
| BErrorType, BErrorType -> true
| _, _ -> false
and
eqTypeSeq #n x y = match x with
| SNil -> (match y with 
  | SNil -> true
  | _ -> false
  )
| SCons x1 xs1 -> let (SCons y1 ys1) = y in 
  eqType x1 y1 && eqTypeSeq xs1 ys1

(* Definition to encode the subtype relation on Bosque types 
   i.e. forall x y . subtypeOf x y <===> x :> y *)
val subtypeOf : bosqueType -> bosqueType -> Tot bool
let rec subtypeOf x y = match x, y with
| BAnyType, _ -> true
| BNoneType, BNoneType -> true
| BIntType, BIntType -> true
| BBoolType, BBoolType -> true
| BUnionType x1 y1, BUnionType x2 y2 -> (subtypeOf x1 x2 || subtypeOf y1 x2) 
  && (subtypeOf x1 y2 || subtypeOf y1 y2)
| BUnionType x1 y1, z -> subtypeOf x1 z || subtypeOf y1 z 
| BEmptyTupleType b1, BEmptyTupleType b2 -> b1 = b2
| BEmptyTupleType b1, BTupleType _ _ _ -> b1
// FIX: the following definition needs to be discussed
// with Mark
| BTupleType b1 n1 seq1, BTupleType b2 n2 seq2 -> 
  if b1 then 
    if b2 then 
      if (n1 > n2) then false
      else eqTypeSeq seq1 (take n1 seq2)
    else let p = Util.min n1 n2 in eqTypeSeq (take p seq1) (take p seq2)
  else 
    if b2 then false 
    else 
      if (n1 >= n2) then eqTypeSeq (take n2 seq1) seq2
      else false 
| BErrorType, BErrorType -> true
| _, _ -> false
