module BosqueTypes

#set-options "--z3rlimit 15"

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
val eqTypeSeq : n:nat -> (x:sequence bosqueType n) -> sequence bosqueType n -> Tot bool (decreases x)
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
| BTupleType b1 n1 seq1, BTupleType b2 n2 seq2 -> (b1 = b2) && (n1 = n2) && eqTypeSeq n1 seq1 seq2
// FIX: The following is wrong
| BRecordType _ _ _, BRecordType _ _ _ -> true
// FIX: The following is incomplete
| BFunctionType, BFunctionType -> true
// FIX: The following is incomplete
| BObjectType, BObjectType -> true
// FIX: The following is incomplete
| BEnumType, BEnumType -> true
// FIX: The following is incomplete
| BCustomKeyType, BCustomKeyType -> true
// FIX: The following is incomplete
| BKeyedType, BKeyedType -> true
| BErrorType, BErrorType -> true
| _, _ -> false
and
eqTypeSeq n x y = match x with
| SNil -> (match y with 
  | SNil -> true
  | _ -> false
  )
| SCons x1 m xs1 -> (match y with 
                 | SNil -> false
                 | SCons y1 m' ys1 -> (m = m') && eqType x1 y1 && eqTypeSeq m xs1 ys1
                 )

val lemma_eqType_refl : x:bosqueType -> Lemma (ensures eqType x x) (decreases x)
val lemma_eqTypeSeq_refl : n:nat -> x:sequence bosqueType n -> Lemma (ensures eqTypeSeq n x x) (decreases x)
let rec lemma_eqType_refl x = match x with
| BAnyType -> ()
| BSomeType -> ()
| BTruthyType -> ()
| BNoneType -> ()
| BUnionType t1 t2 -> lemma_eqType_refl t1; lemma_eqType_refl t2
| BParseableType -> ()
| BBoolType -> ()
| BIntType -> ()
| BFloatType -> ()
| BRegexType -> ()
| BTypedStringType t -> lemma_eqType_refl t
| BGUIDType -> ()
| BTupleType _ n seq -> lemma_eqTypeSeq_refl n seq
| BRecordType _ n seq -> lemma_eqTypeSeq_refl n seq
| BFunctionType -> ()
| BObjectType -> ()
| BEnumType -> ()
| BCustomKeyType -> ()
| BKeyedType -> ()
| BErrorType -> ()
and 
lemma_eqTypeSeq_refl n x = match x with
| SNil -> ()
| SCons hd m tl -> lemma_eqType_refl hd; lemma_eqTypeSeq_refl m tl

val lemma_eqType_sym : x:bosqueType -> y:bosqueType 
  -> Lemma (requires eqType x y) (ensures eqType y x) (decreases x)
val lemma_eqTypeSeq_sym : n:nat -> x:sequence bosqueType n -> y:sequence bosqueType n 
  -> Lemma (requires eqTypeSeq n x y) (ensures eqTypeSeq n y x) (decreases x)
let rec lemma_eqType_sym x y = match x with 
| BAnyType -> ()
| BSomeType -> ()
| BTruthyType -> ()
| BNoneType -> ()
| BUnionType t1 t2 -> (match y with
                     | BUnionType t1' t2' -> lemma_eqType_sym t1 t1'; lemma_eqType_sym t2 t2'
                     | _ -> ()
                     )
| BParseableType -> ()
| BBoolType -> ()
| BIntType -> ()
| BFloatType -> ()
| BRegexType -> ()
| BTypedStringType t -> (match y with
                       | BTypedStringType t' -> lemma_eqType_sym t t'
                       | _ -> ()
                       )
| BGUIDType -> ()
| BTupleType b n seq -> (match y with
                       | BTupleType b' n' seq' -> lemma_eqTypeSeq_sym n' seq seq'
                       | _ -> ()
                       )
| BRecordType b n seq -> (match y with
                        | BTupleType b' n' seq' -> lemma_eqTypeSeq_sym n' seq seq'
                        | _ -> ()
                        )
| BFunctionType -> ()
| BObjectType -> ()
| BEnumType -> ()
| BCustomKeyType -> ()
| BKeyedType -> ()
| BErrorType -> ()
and 
lemma_eqTypeSeq_sym n x y = match x with
| SNil -> ()
| SCons hd m tl -> (match y with
                  | SNil -> () 
                  | SCons hd' m' tl' -> lemma_eqType_sym hd hd'; lemma_eqTypeSeq_sym m tl tl'
                  )

// val lemma_eqTypeSeq_trans : n:nat -> (x:sequence bosqueType n)
//   -> (y:sequence bosqueType n) 
//   -> (z:sequence bosqueType n)
//   -> Lemma (requires (eqTypeSeq n x y) && (eqTypeSeq n y z)) (ensures (eqTypeSeq n x z)) (decreases %[x; y; z])
// val lemma_eqType_trans : x:bosqueType
//   -> y:bosqueType 
//   -> z:bosqueType 
//   -> Lemma (requires (eqType x y) && (eqType y z)) (ensures (eqType x z)) (decreases %[x; y; z])
// let rec lemma_eqType_trans x y z = match x with
// | BAnyType -> ()
// | BSomeType -> ()
// | BTruthyType -> ()
// | BNoneType -> ()
// | BUnionType t1 t2 -> (match y with
//                      | BUnionType t1' t2' -> (match z with
//                                             | BUnionType t1'' t2'' -> lemma_eqType_trans t1 t1' t1''; 
//                                                                      lemma_eqType_trans t2 t2' t2'' 
//                                             | _ -> ()
//                                             )
//                      | _ -> ()
//                      )
// | BParseableType -> ()
// | BBoolType -> ()
// | BIntType -> ()
// | BFloatType -> ()
// | BRegexType -> ()
// | BTypedStringType t -> (match y with
//                        | BTypedStringType t' -> (match z with
//                                                | BTypedStringType t'' -> lemma_eqType_trans t t' t''
//                                                | _ -> ()
//                                                )
//                        | _ -> ()
//                        )
// | BGUIDType -> ()
// | BTupleType _ n seq -> (match y with
//                      | BTupleType _ n' seq' -> (match z with
//                                             | BTupleType _ n'' seq'' -> lemma_eqTypeSeq_trans n seq seq' seq''
//                                             | _ -> ()
//                                             )
//                      | _ -> ()
//                      )
// | BRecordType _ n seq -> ()
// | BFunctionType -> ()
// | BObjectType -> ()
// | BEnumType -> ()
// | BCustomKeyType -> ()
// | BKeyedType -> ()
// | BErrorType -> ()
// and 
// lemma_eqTypeSeq_trans n x y z = match x with
// | SNil -> (match y with 
//          | SNil -> ()
//          | SCons hd' m' tl' -> (match z with 
//                               | SNil -> ()
//                               | SCons hd'' m'' tl'' -> ()
//                               )
//          )
// | SCons hd m tl -> (match y with 
//                   | SNil -> ()
//                   | SCons hd' m' tl' -> (match z with 
//                                        | SNil -> ()
//                                        | SCons hd'' m'' tl'' -> lemma_eqType_trans hd hd' hd''; 
//                                                                lemma_eqTypeSeq_trans m tl tl' tl''
//                                        )
//                   )

(* Definition to encode the subtype relation on Bosque types 
   i.e. forall x y . subtypeOf x y <===> x :> y *)
val subtypeOfSeq : n:nat -> (x:sequence bosqueType n) -> sequence bosqueType n -> Tot bool (decreases x)
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
    else b1 && (n1 <= n2) && subtypeOfSeq n1 seq1 (take n2 n1 seq2)
  else 
    if b2 then false 
    else 
      if (n1 = n2) then (not b1) && (not b2) && (n1 = n2) && subtypeOfSeq n1 seq1 seq2
      else false 
| BErrorType, BErrorType -> true
| _, _ -> false
and 
subtypeOfSeq n x y = match x with
| SNil -> (match y with
  | SNil -> true
  | _ -> false
  )
| SCons x1 m xs1 -> (match y with 
                 | SNil -> false
                 | SCons y1 m' ys1 -> (m = m') && eqType x1 y1 && eqTypeSeq m xs1 ys1  
                 )
