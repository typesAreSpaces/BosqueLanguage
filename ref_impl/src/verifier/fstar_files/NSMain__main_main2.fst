module NSMain__main_main2
open Sequence
open BosqueTypes
open BosqueTerms

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))
let bUnionType_BIntType_BNoneType = (BUnionType BIntType BNoneType)

(* Concept Declarations *)

(* Entity Declarations *)

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__max : (x1:bosqueTerm{subtypeOf bUnionType_BIntType_BNoneType (getType x1)}) -> (x2:bosqueTerm{subtypeOf BIntType (getType x2)}) -> Tot (x3:bosqueTerm{subtypeOf BIntType (getType x3)})
let nSMain__max x y = 
 let __tmp_0 = (isNone x) in 
  if __tmp_0 then 
   let __ir_ret___2 = y in 
    let __ir_ret___3 = __ir_ret___2 in 
     let _return_ = __ir_ret___3 in 
      _return_
  else 
   let __tmp_4 = (extractBool (op_greaterOrEq x y)) in 
    if __tmp_4 then 
     let __ir_ret___1 = x in 
      let __ir_ret___3 = __ir_ret___1 in 
       let _return_ = __ir_ret___3 in 
        _return_
    else 
     let __ir_ret__ = y in 
      let __ir_ret___3 = __ir_ret__ in 
       let _return_ = __ir_ret___3 in 
        _return_ 


// val nthTuple : index:int -> dimension:nat -> x:bosqueTerm -> Tot (y:bosqueTerm)
// let rec nthTuple index dimension y = match y with
// | BTuple 0 SNil -> if (index < 0 || dimension <> 0) then BError else BNone
// | BTuple dimension'' (SCons x' dimension' xs') -> 
//   if (index < 0 || dimension <> dimension'') then BError else
//   if (index >= dimension) then BNone else
//   if index = 0 then x'
//   else nthTuple (index-1) dimension' (BTuple dimension' xs')
// | _ -> BError

// | BTuple : n:nat -> sequence bosqueTerm n -> bosqueTerm

// (* Tuple Type projector *)
val nthTupleType2 : index:int -> dimension:nat 
  -> x:(sequence bosqueTerm dimension) 
  -> Tot (y:bosqueType)
let rec nthTupleType2 index dimension y = match y with
| SNil -> if (index < 0 || dimension <> 0) then BErrorType else BNoneType
| SCons z dimension' zs -> 
  if (index < 0) then BErrorType else
  if (index >= dimension) then BNoneType else
  if index = 0 then (getType z)
  else nthTupleType2 (index-1) dimension' zs

(* Tuple projector *)
val nthTuple2 : index:int -> dimension:nat 
  -> x:(sequence bosqueTerm dimension) 
  -> Tot (y:bosqueTerm)
let rec nthTuple2 index dimension y = match y with
| SNil -> if (index < 0 || dimension <> 0) then BError else BNone
| SCons z dimension' zs -> 
  if (index < 0) then BError else
  if (index >= dimension) then BNone else
  if index = 0 then z
  else nthTuple2 (index - 1) dimension' zs

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

val lemma_nthTuple_index0 : dimension : nat -> x : (sequence bosqueTerm dimension) -> 
Lemma (ensures (eqType (nthTupleType2 0 dimension x) (getType (nthTuple2 0 dimension x))))
let lemma_nthTuple_index0 dimension x = match x with
| SNil -> ()
| SCons z dimension' zs -> lemma_eqType_refl (getType z)

val lemma_nthTuple :index : int -> dimension : nat -> x : (sequence bosqueTerm dimension) -> 
Lemma (ensures (eqType (nthTupleType2 index dimension x) (getType (nthTuple2 index dimension x))))
let rec lemma_nthTuple index dimension y = match y with
| SNil -> ()
| SCons z dimension' zs -> 
  if (index < 0) then () else
  if (index >= dimension) then () else 
  if (index = 0) then lemma_nthTuple_index0 dimension (SCons z dimension' zs)
  else lemma_nthTuple (index-1) dimension' zs

val lemma_subtypeof_eqtype : t1 : bosqueType -> t2 : bosqueType -> t3 : bosqueType 
  ->  Lemma (requires (subtypeOf t1 t2) /\ (eqType t2 t3)) (ensures subtypeOf t1 t3)
let rec lemma_subtypeof_eqtype t1 t2 t3 = match t1 with
| BAnyType -> ()
| BSomeType -> ()
| BTruthyType -> ()
| BNoneType -> ()
| BUnionType t1' t2' -> admit() // Keep working here
| BParseableType -> ()
| BBoolType -> ()
| BIntType -> ()
| BFloatType -> ()
| BRegexType -> ()
| BTypedStringType t' -> admit()
| BGUIDType -> ()
| BTupleType _ n seq -> admit()
| BRecordType _ n seq -> admit()
| BFunctionType -> ()
| BObjectType -> ()
| BEnumType -> ()
| BCustomKeyType -> ()
| BKeyedType -> ()
| BErrorType -> ()

val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__main  = 
 let what = (SCons (BInt 10) 1 (SCons (BInt 30) 0 SNil)) in
  let __tmp_0 = (BTuple 2 what) in 
   let xTuple2 = __tmp_0 in 
    let y = (BInt 20) in 
    lemma_nthTuple 0 2 what;
     let __tmp_7 = (nthTuple2 0 2 what) in 
      let __tmp_4 = (nSMain__max __tmp_7 y) in 
       let z = __tmp_4 in 
        let __ir_ret__ = z in 
         let _return_ = __ir_ret__ in 
          _return_