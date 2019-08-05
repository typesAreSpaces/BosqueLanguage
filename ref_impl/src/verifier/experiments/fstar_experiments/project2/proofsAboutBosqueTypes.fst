module ProofsAboutBosqueTypes

#set-options "--z3rlimit 15"

open Sequence
open BosqueTypes

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

val lemma_eqTypeSeq_trans : n:nat -> (x:sequence bosqueType n)
  -> (y:sequence bosqueType n) 
  -> (z:sequence bosqueType n)
  -> Lemma (requires (eqTypeSeq n x y) && (eqTypeSeq n y z)) (ensures (eqTypeSeq n x z)) (decreases %[x; y; z])
val lemma_eqType_trans : x:bosqueType
  -> y:bosqueType 
  -> z:bosqueType 
  -> Lemma (requires (eqType x y) && (eqType y z)) (ensures (eqType x z)) (decreases %[x; y; z])
let rec lemma_eqType_trans x y z = match x with
| BAnyType -> ()
| BSomeType -> ()
| BTruthyType -> ()
| BNoneType -> ()
| BUnionType t1 t2 -> (match y with
                     | BUnionType t1' t2' -> (match z with
                                            | BUnionType t1'' t2'' -> lemma_eqType_trans t1 t1' t1''; 
                                                                     lemma_eqType_trans t2 t2' t2'' 
                                            | _ -> ()
                                            )
                     | _ -> ()
                     )
| BParseableType -> ()
| BBoolType -> ()
| BIntType -> ()
| BFloatType -> ()
| BRegexType -> ()
| BTypedStringType t -> (match y with
                       | BTypedStringType t' -> (match z with
                                               | BTypedStringType t'' -> lemma_eqType_trans t t' t''
                                               | _ -> ()
                                               )
                       | _ -> ()
                       )
| BGUIDType -> ()
| BTupleType _ n seq -> (match y with
                     | BTupleType _ n' seq' -> (match z with
                                            | BTupleType _ n'' seq'' -> lemma_eqTypeSeq_trans n seq seq' seq''
                                            | _ -> ()
                                            )
                     | _ -> ()
                     )
| BRecordType _ n seq -> ()
| BFunctionType -> ()
| BObjectType -> ()
| BEnumType -> ()
| BCustomKeyType -> ()
| BKeyedType -> ()
| BErrorType -> ()
and 
lemma_eqTypeSeq_trans n x y z = match x with
| SNil -> (match y with 
         | SNil -> ()
         | SCons hd' m' tl' -> (match z with 
                              | SNil -> ()
                              | SCons hd'' m'' tl'' -> ()
                              )
         )
| SCons hd m tl -> (match y with 
                  | SNil -> ()
                  | SCons hd' m' tl' -> (match z with 
                                       | SNil -> ()
                                       | SCons hd'' m'' tl'' -> lemma_eqType_trans hd hd' hd''; 
                                                               lemma_eqTypeSeq_trans m tl tl' tl''
                                       )
                  )
