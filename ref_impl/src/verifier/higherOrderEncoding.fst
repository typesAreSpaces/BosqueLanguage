module HigherOrderEncoding

type sequence 'a : nat -> Type = 
| SNil : sequence 'a 0
| SCons : hd : 'a -> n:nat -> tl:sequence 'a n -> sequence 'a (n + 1)

type bosqueType =
| BAnyType
| BSomeType
| BNoneType
| BIntType
| BBoolType
| BUnionType : bosqueType -> bosqueType -> bosqueType 
// | BTupleType : bool -> n:nat -> sequence bosqueType n -> bosqueType

type n_sequence : n:nat -> (sequence bosqueType n) -> Type =
| NNil : n_sequence 0 SNil 
| NCons : hd : bosqueType -> n:nat -> tl:sequence bosqueType n-> n_sequence (n+1) (SCons hd n tl)

type bosqueTerm : bosqueType -> Type =  
| BNone : bosqueTerm (BNoneType)
| BBool : bool -> bosqueTerm (BBoolType)
| BInt : int -> bosqueTerm (BIntType)
| BUnionInj1 : t1:bosqueType ->  t2:bosqueType -> bosqueTerm t1 -> bosqueTerm (BUnionType t1 t2) 
| BUnionInj2 : t1:bosqueType ->  t2:bosqueType -> bosqueTerm t2 -> bosqueTerm (BUnionType t1 t2)
// | BTuple :  
// b:bool -> n:nat -> seq:sequence bosqueType n 
// -> sequence (bosqueTerm BAnyType) n -> bosqueTerm (BTupleType b n seq) 

assume val cast : t1:Type -> t2:Type -> x:t1 -> Tot t2

val extractInt : x:bosqueTerm (BIntType) -> int
let extractInt (BInt x) = x

val max : x:bosqueTerm (BIntType) -> y : bosqueTerm (BIntType) -> bosqueTerm (BIntType)
let max x y = if (extractInt x > extractInt y) then x else y

val max2 : x:bosqueTerm (BIntType) -> y : bosqueTerm (BIntType) -> bosqueTerm (BIntType)
let max2 (BInt x) (BInt y) = if (x > y) then BInt x else BInt y

val maxUnion : x:bosqueTerm (BUnionType BIntType BNoneType) -> y:bosqueTerm (BIntType) -> bosqueTerm (BIntType)
let maxUnion x y = match x with 
| BUnionInj1 BIntType BNoneType x -> if (extractInt x > extractInt y) then x else y
| BUnionInj2 BIntType BNoneType (BNone) -> y

val isInt : x:bosqueTerm (BUnionType BIntType BNoneType) -> Tot bool
let isInt x = match x with
| BUnionInj1 BIntType BNoneType _ -> true
| _ -> false

let _ = assert (forall x y . isInt x -> extractInt (maxUnion x y) >= extractInt y)
