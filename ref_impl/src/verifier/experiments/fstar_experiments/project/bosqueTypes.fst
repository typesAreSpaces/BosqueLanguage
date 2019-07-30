module BosqueTypes

open Sequence
open Util

// Convention with UnionTerm: 
// 1) its elements should be unique
// 2) There is a unique way to represent any union (normal form)
// the latter was needed for eqType
type bosqueType =
| BTypeNone
| BTypeInt
| BTypeBool
| BTypeUnion : bosqueType -> bosqueType -> bosqueType
// The bool indicates if the Empty Tuple is open or not
| BTypeEmptyTuple : bool -> bosqueType
// The bool indicates if the Tuple is open or not
| BTypeTuple : bool -> n:nat -> sequence bosqueType n -> bosqueType
| BTypeError

(* Definition of equality relation on Bosque types *)
val eqTypeSeq : #n:nat -> (x:sequence bosqueType n) -> sequence bosqueType n -> Tot bool (decreases x)
val eqType : x:bosqueType -> bosqueType -> Tot bool (decreases x)
let rec eqType x y = match x, y with
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
// The following might be incomplete, but if Unions are normalized then it is complete
| BTypeUnion x1 x2 , BTypeUnion y1 y2 -> eqType x1 y1 && eqType x2 y2
| BTypeUnion _ _, _ -> false
| BTypeEmptyTuple b1, BTypeEmptyTuple b2 -> b1 = b2 
| BTypeTuple b1 n1 seq1, BTypeTuple b2 n2 seq2 -> (b1 = b2) && (n1 = n2) && eqTypeSeq seq1 seq2
| BTypeError, BTypeError -> true
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
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
| BTypeUnion x1 y1, BTypeUnion x2 y2 -> (subtypeOf x1 x2 || subtypeOf y1 x2) 
  && (subtypeOf x1 y2 || subtypeOf y1 y2)
| BTypeUnion x1 y1, z -> subtypeOf x1 z || subtypeOf y1 z 
| BTypeEmptyTuple b1, BTypeEmptyTuple b2 -> b1 = b2
| BTypeTuple b1 n1 seq1, BTypeTuple b2 n2 seq2 -> 
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
| BTypeError, BTypeError -> true
| _, _ -> false
