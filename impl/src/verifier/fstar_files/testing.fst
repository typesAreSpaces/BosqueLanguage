module Testing
 
open Sequence
open BosqueTerms
open BosqueTypes

(* ------------------------------------------------------------------------------------------- *)
(* Type instantiation *)
type typeUnionIntBool = x:bosqueType{subtypeOf (BUnionType BIntType BBoolType) x}
type termUnionIntBool = x:bosqueTerm{subtypeOf (BUnionType BIntType BBoolType) (getType x)}
(* Definition of IntType *)
type termInt = x:bosqueTerm{isInt x} 
(* ------------------------------------------------------------------------------------------- *)

(* --------------------------------------------------------------- *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))
let bTupleType_16BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_bTupleType_2BIntType_BIntTypefalse_bTypedStringType_BAnyType_BBoolType_BBoolTypefalse = BTupleType false 16 (SCons BIntType 15 (SCons BIntType 14 (SCons BIntType 13 (SCons BIntType 12 (SCons BIntType 11 (SCons BIntType 10 (SCons BIntType 9 (SCons BIntType 8 (SCons BIntType 7 (SCons BIntType 6 (SCons BIntType 5 (SCons BIntType 4 (SCons bTupleType_2BIntType_BIntTypefalse 3 (SCons bTypedStringType_BAnyType 2 (SCons BBoolType 1 (SCons BBoolType 0 SNil))))))))))))))))
let testString = BTypedString "hello" BAnyType
let testString2 = BTypedString "hello" bTypedStringType_BAnyType
let testString3 = BTypedString "hello" bTupleType_16BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_bTupleType_2BIntType_BIntTypefalse_bTypedStringType_BAnyType_BBoolType_BBoolTypefalse

let test_a = BTuple 2 (SCons (BInt 3) 1 (SCons (BBool true) 0 SNil))

let oktest = BTuple 2 (SCons (BInt 3) 1 (SCons (BBool true) 0 SNil))
let oktest2 = nthTupleType 10 2 oktest

(* Testing: subtypeOf *)
let testa0 = subtypeOf (BUnionType BIntType BBoolType) BIntType 
let testa0' = subtypeOf (BUnionType BIntType BBoolType) (BUnionType BBoolType BIntType)
let testa1 = subtypeOf (BUnionType BIntType BBoolType) (BNoneType)
let testa2 = subtypeOf (BUnionType BIntType BBoolType) (BUnionType BNoneType BBoolType)
let testa3 = subtypeOf (BUnionType BIntType BBoolType) (BUnionType BIntType (BUnionType BNoneType BBoolType))
let testa4 = subtypeOf (BUnionType BIntType BBoolType) (BUnionType BBoolType BIntType)
let testa5 = subtypeOf (BTupleType false 1 (SCons BIntType 0 SNil)) (BTupleType false 1 (SCons BIntType 0 SNil))
let testa6 = subtypeOf (BTupleType false 1 (SCons BIntType 0 SNil)) (BTupleType false 1 (SCons BBoolType 0 SNil))
let testa7 = subtypeOf (BTupleType false 2 (SCons BIntType 1 (SCons BBoolType 0 SNil))) (BTupleType false 1 (SCons BBoolType 0 SNil))
let testa8 = subtypeOf (BTupleType false 2 (SCons BIntType 1 (SCons BBoolType 0 SNil))) (BTupleType false 2 (SCons BIntType 1 (SCons BBoolType 0 SNil)))
let testa9 = subtypeOf (BTupleType false 1 (SCons BIntType 0 SNil)) (BTupleType false 2 (SCons BIntType 1 (SCons BBoolType 0 SNil)))
let testa10 = subtypeOf (BTupleType true 1 (SCons BIntType 0 SNil)) (BTupleType false 1 (SCons BIntType 0 SNil))
let testa11 = subtypeOf (BTupleType true 1 (SCons BIntType 0 SNil)) (BTupleType false 2 (SCons BIntType 1 (SCons BBoolType 0 SNil)))
let testa12 = subtypeOf (BTupleType false 1 (SCons BIntType 0 SNil)) (BTupleType true 1 (SCons BIntType 0 SNil))
let testa13 = subtypeOf (BTupleType true 0 SNil) (BTupleType false 2 (SCons BIntType 1 (SCons BBoolType 0 SNil)))

(* Testing: BTuple *)
let testb0 = BTuple 2 (SCons (BInt 342) 1 (SCons (BBool true) 0 SNil))
// The following fails, as expected
// let test0a1 = BTuple 3 (SCons (BInt 342) (SCons (BBool true) (SNil)))
let testb1 = BTuple 0 SNil
let testb2 = isTuple false 0 SNil testb0
let testb2' = isTuple false 2 (SCons BIntType 1 (SCons BBoolType 0 SNil)) testb0
let testb2'' = isTuple true 2 (SCons BIntType 1 (SCons BBoolType 0 SNil)) testb0
// The following fails, as expected
// let testb2_ = isTuple 1 SNil testb0
// let testb3 = isTuple 3 testb0
// let testb4 = isTuple 2 (BInt 234)
let testb5 = nthTuple 0 2 testb0
let testb6 = nthTuple 0 3 testb0
let testb7 = nthTuple 1 2 testb0
let testb8 = nthTuple 2 2 testb0
let testb9 = nthTuple 2 10000 testb0
let testb10 = nthTuple 10001 10000 testb0
let testb11 = nthTuple (-1) 2 testb0
let testb12 = BTuple 0 SNil
// let testb13 = isTuple 0 testb12
// let testb14 = isTuple 10 testb12

(* Testing: getType *)
let testc1 = BTuple 2 (SCons test_a 1 ((SCons testb0) 0 SNil))
let testc2 = getType testb0
let testc3 = getType testb1
let testc4 = getType testc1

(* -------------------------------------------------------------------------------------------------------------- *)

(* Examples *)

val maxWithUnion : termUnionIntBool -> x:bosqueTerm{subtypeOf BIntType (getType x)} -> y:bosqueTerm{subtypeOf BIntType (getType x)}
let maxWithUnion x y = match x with 
| BBool z -> (match y with 
  | BInt x2 -> BInt x2
) 
| BInt x1 -> (match y with 
  | BInt x2 -> if (x1 > x2) then BInt x1 else BInt x2
)

// New version of maxWithUnion
val maxWithUnion' : termUnionIntBool -> x:bosqueTerm{subtypeOf BIntType (getType x)} -> y:bosqueTerm{subtypeOf BIntType (getType y)}
let maxWithUnion' x y = match x with 
| BBool z -> y
| BInt x1 -> (match y with 
  | BInt x2 -> if (x1 > x2) then x else BInt x2
)

(* Testing: maxWithUnion *)
let testd1 = maxWithUnion (BInt 12) (BInt 10)
let testd2 = maxWithUnion (BInt 10) (BInt 12)
let testd3 = maxWithUnion (BBool false) (BInt 12)

(* The following assertion proves that maxWithUnion is correctly implemented *)
let _ = assert (forall x y z. extractBool (op_greaterOrEq (maxWithUnion (BInt x) (BInt y)) (BInt x)) 
&& extractBool (op_greaterOrEq (maxWithUnion (BInt x) (BInt y)) (BInt y))
&& (extractBool (op_eqTerm (maxWithUnion (BInt x) (BInt y)) (BInt x)) || extractBool (op_eqTerm (maxWithUnion (BInt x) (BInt y)) (BInt y)))
&& extractBool ((op_eqTerm (maxWithUnion (BBool z) (BInt x)) (BInt x)))
)

(* The following assertion proves that maxWithUnion' is correctly implemented *)
let _ = assert (forall x y z. extractBool (op_greaterOrEq (maxWithUnion' (BInt x) (BInt y)) (BInt x)) 
&& extractBool (op_greaterOrEq (maxWithUnion' (BInt x) (BInt y)) (BInt y))
&& (extractBool (op_eqTerm (maxWithUnion' (BInt x) (BInt y)) (BInt x)) || extractBool (op_eqTerm (maxWithUnion' (BInt x) (BInt y)) (BInt y)))
&& extractBool ((op_eqTerm (maxWithUnion' (BBool z) (BInt x)) (BInt x)))
)

val maxWithUnion2 : termUnionIntBool -> termInt -> termInt
let maxWithUnion2 x y = match x with 
| BBool _ -> y 
| BInt _ -> if (extractBool (op_greaterOrEq x y)) then x else y 

let _ = assert (forall x y z. extractBool (op_greaterOrEq (maxWithUnion2 (BInt x) (BInt y)) (BInt x)) 
&& extractBool (op_greaterOrEq (maxWithUnion2 (BInt x) (BInt y)) (BInt y))
&& (extractBool (op_eqTerm (maxWithUnion2 (BInt x) (BInt y)) (BInt x)) || extractBool (op_eqTerm (maxWithUnion2 (BInt x) (BInt y)) (BInt y)))
&& (extractBool ((op_eqTerm (maxWithUnion2 (BBool z) (BInt x)) (BInt x))))
)

// type termUnionIntBool = x:bosqueTerm{subtypeOf (BUnionType BIntType BBoolType) (getType x)}

val maxWithUnion3 : termUnionIntBool -> termInt -> termInt
let maxWithUnion3 x y = match x with 
| BBool _ -> y 
| _ -> if (extractBool (op_greaterOrEq x y)) then x else y

let _ = assert (forall x y z. extractBool (op_greaterOrEq (maxWithUnion3 (BInt x) (BInt y)) (BInt x)) 
&& extractBool (op_greaterOrEq (maxWithUnion3 (BInt x) (BInt y)) (BInt y))
&& (extractBool (op_eqTerm (maxWithUnion3 (BInt x) (BInt y)) (BInt x)) || extractBool (op_eqTerm (maxWithUnion3 (BInt x) (BInt y)) (BInt y)))
&& (extractBool ((op_eqTerm (maxWithUnion3 (BBool z) (BInt x)) (BInt x))))
)

val maxWithUnion4 : termUnionIntBool -> termInt -> termInt
let maxWithUnion4 x y = if (isBool x) then y else if (extractBool (op_greaterOrEq x y)) then x else y

let _ = assert (forall x y z. extractBool (op_greaterOrEq (maxWithUnion4 (BInt x) (BInt y)) (BInt x)) 
&& extractBool (op_greaterOrEq (maxWithUnion4 (BInt x) (BInt y)) (BInt y))
&& (extractBool (op_eqTerm (maxWithUnion4 (BInt x) (BInt y)) (BInt x)) || extractBool (op_eqTerm (maxWithUnion4 (BInt x) (BInt y)) (BInt y)))
   && (extractBool ((op_eqTerm (maxWithUnion4 (BBool z) (BInt x)) (BInt x))))) 

let unionTypeIntBool = BUnionType BIntType BBoolType

val maxWithUnion5 : x:bosqueTerm{subtypeOf unionTypeIntBool (getType x)} -> x:bosqueTerm{subtypeOf BIntType (getType x)} -> x:bosqueTerm{subtypeOf BIntType (getType x)}
let maxWithUnion5 x y = if (isBool x) then y else if (extractBool (op_greaterOrEq x y)) then x else y

let _ = assert (forall x y z. extractBool (op_greaterOrEq (maxWithUnion5 (BInt x) (BInt y)) (BInt x)) 
&& extractBool (op_greaterOrEq (maxWithUnion5 (BInt x) (BInt y)) (BInt y))
&& (extractBool (op_eqTerm (maxWithUnion5 (BInt x) (BInt y)) (BInt x)) || extractBool (op_eqTerm (maxWithUnion5 (BInt x) (BInt y)) (BInt y)))
   && (extractBool ((op_eqTerm (maxWithUnion5 (BBool z) (BInt x)) (BInt x))))) 

(* -------------------------------------------------------------------------------------------------------------------------------------- *)

val max : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> z:bosqueTerm{isInt z}
let max x y = if (extractBool (op_greaterOrEq x y)) then x else y

let _ = assert (forall x y. extractBool (op_greaterOrEq (max (BInt x) (BInt y)) (BInt x) )
&& extractBool (op_greaterOrEq (max (BInt x) (BInt y)) (BInt y))
&& (extractBool (op_eqTerm (max (BInt x) (BInt y)) (BInt x)) || extractBool (op_eqTerm (max (BInt x) (BInt y)) (BInt y)))
)

// New version of max using subtypeOf
val max' : x:bosqueTerm{subtypeOf (BIntType) (getType x)} -> y:bosqueTerm{subtypeOf (BIntType) (getType y)} -> z:bosqueTerm{subtypeOf (BIntType) (getType z)}
let max' x y = if (extractBool (op_greaterOrEq x y)) then x else y

let _ = assert (forall x y. extractBool (op_greaterOrEq (max' (BInt x) (BInt y)) (BInt x) )
&& extractBool (op_greaterOrEq (max' (BInt x) (BInt y)) (BInt y))
&& (extractBool (op_eqTerm (max' (BInt x) (BInt y)) (BInt x)) || extractBool (op_eqTerm (max' (BInt x) (BInt y)) (BInt y)))
)

// // The following fails, as expected
// let _ = assert (forall x y z. extractBool (op_greaterOrEq (max (BInt x) (BInt y)) (BInt x) )
// && extractBool (op_greaterOrEq (max (BInt x) (BInt y)) (BInt y))
// && (extractBool (op_eqTerm (max (BInt x) (BInt y)) (BInt x)) || extractBool (op_eqTerm (max (BInt x) (BInt y)) (BInt y)))
// && (extractBool (op_eqTerm (max (BInt x) (BBool z)) (BInt x)))
// )

(* -------------------------------------------------------------------------------------------------------------------------------------- *)

val maxWithTuple : x:bosqueTerm{isTuple false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)) x}
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm{isInt z}
let maxWithTuple x y = 
  let xAt0 = nthTuple 0 2 x in 
    if (extractBool (op_greaterOrEq xAt0 y)) then xAt0 
    else y

let typeTuple2BIntBBool = BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))

// New version of maxWithTuple using subtypeOf
val maxWithTuple' : x:bosqueTerm{subtypeOf typeTuple2BIntBBool (getType x)}
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm{isInt z}
let maxWithTuple' x y = 
  let xAt0 = nthTuple 0 2 x in 
    if (extractBool (op_greaterOrEq xAt0 y)) then xAt0 
    else y
    
(* Testing: maxWithTuple *)
let teste0 = maxWithTuple (testb0) (BInt 1203)
let teste1 = maxWithTuple (testb0) (BInt (-12))
let teste0' = maxWithTuple' (testb0) (BInt 1203)
let teste1' = maxWithTuple' (testb0) (BInt (-12))

let _ = assert (forall x y . extractBool (op_greaterOrEq (maxWithTuple x y) (nthTuple 0 2 x)))

let _ = assert (forall x y . (BIntType = (getType (nthTuple 0 2 x))) ==> extractBool (op_greaterOrEq (maxWithTuple x y) (nthTuple 0 2 x)))

(* -------------------------------------------------------------------------------------------------------------------------------------- *)

val maxWithTuple'' : x:bosqueTerm{isTuple false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)) x} 
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm{isInt z}
let maxWithTuple'' x y = match x with 
| BTuple 2 seq -> 
  let xAt0 = nthTuple 0 2 x in 
    match xAt0 with 
    | BInt x1 -> if (extractBool (op_greaterOrEq xAt0 y)) then xAt0 else y
    | _ -> BError

(* Testing: maxWithTuple'' *)
let test5a = maxWithTuple'' (testb0) (BInt 1203)
let test5b = maxWithTuple'' (testb0) (BInt (-12))

// let _ = assert (forall x y . extractBool (op_greaterOrEq (maxWithTuple2 x y) (nthTuple 0 2 x)))

let _ = assert (forall x y . (BIntType = (getType (nthTuple 0 2 x))) ==> extractBool (op_greaterOrEq (maxWithTuple'' x y) (nthTuple 0 2 x)))

(* -------------------------------------------------------------------------------------------------------------------------------------- *)

let closedTuple2_Int_Bool = (BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)))

// New version of maxWithTuple'' using subtypeOf
val maxWithTuple''' : x:bosqueTerm{(subtypeOf closedTuple2_Int_Bool (getType x))} 
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm{isInt z}
let maxWithTuple''' x y = match x with 
| BTuple 2 seq -> 
  let xAt0 = nthTuple 0 2 x in 
    if (extractBool (op_greaterOrEq xAt0 y)) then xAt0 else y

// New version of maxWithTuple''' (shorter representation)
val maxWithTuple'''' : x:bosqueTerm{(subtypeOf closedTuple2_Int_Bool (getType x))} 
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm{isInt z}
let maxWithTuple'''' x y = let xAt0 = nthTuple 0 2 x in 
    if (extractBool (op_greaterOrEq xAt0 y)) then xAt0 else y 
  
// // Idk why the following doesn't work like maxWithTuple''''
// val maxWithTuple''''' : x:bosqueTerm{subtypeOf (BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))) (getType x)} 
//   -> y:bosqueTerm{isInt y} 
//   -> z:bosqueTerm
// let maxWithTuple''''' x y = match x with 
// | BTuple 2 seq -> 
//   let xAt0 = nthTuple 0 2 x in 
//     if (extractBool (op_greaterOrEq xAt0 y)) then xAt0 else y

// // The following two examples are interesting because they maxWithTuple'''' fails to
// // type check the fact that (BTuple 2 (SCons (BInt 2) 1 (SCons (BBool true) 0 SNil))) has
// // type [BIntType, BBoolType]
// let testh0 = let whatt = (BTuple 2 (SCons (BInt 2) 1 (SCons (BBool true) 0 SNil))) in maxWithTuple'''' whatt (BInt 33)
// let testh1 = maxWithTuple'''' (BTuple 2 (SCons (BInt 2) 1 (SCons (BBool true) 0 SNil))) (BInt 33) 

let tupleTypeExample = (BTuple 2 (SCons (BInt 2) 1 (SCons (BBool true) 0 SNil))) 

let testg0 = subtypeOf (BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))) (getType tupleTypeExample)
let testg1 = subtypeOf (BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))) (getType (BTuple 2 (SCons (BInt 2) 1 (SCons (BBool true) 0 SNil)))) 

// This approach `fixes` testh0 and testh1
let testg2 = maxWithTuple'''' tupleTypeExample (BInt 33)

(* -------------------------------------------------------------------------------------------------------------------------------------- *)

// val withClosedTuple : x:bosqueTerm{subtypeOf (BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))) (getType x)} -> Tot int
// let withClosedTuple x = match x with 
// | BTuple _ _ -> 0

val withOpenTuple : x:bosqueTerm{subtypeOf (BTupleType true 0 SNil) (getType x)} -> Tot bool
let withOpenTuple x = match x with 
| BTuple m seq -> false

// // Idk why the following doesn't work
// val withOpenTuple2 : x:bosqueTerm{subtypeOf (BTupleType true 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))) (getType x)} -> Tot bool
// let withOpenTuple2 x = match x with
// | BTuple 2 seq -> false
// | BTuple 3 seq -> false 
// | BTuple m seq -> true

let openTuple2_Int_Bool = (BTupleType true 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)))

// This new version of withOpenTuple2 works! It needed the type to be declare (?!)
val withOpenTuple2' : x:bosqueTerm{subtypeOf openTuple2_Int_Bool (getType x)} -> Tot bool
let withOpenTuple2' x = match x with
| BTuple 2 seq -> false
| BTuple 3 seq -> true
| BTuple m seq -> true 

let testf0 = BTuple 1 (SCons (BInt 3) 0 SNil)
let testf1 = BTuple 2 (SCons (BBool true) 1 (SCons (BInt 3) 0 SNil) )
let testf2 = BTuple 2 (SCons (BInt 0) 1 (SCons (BBool true) 0 SNil) )
let testf3 = BTuple 3 (SCons (BInt 0) 2 (SCons (BBool true) 1 (SCons (BInt 12) 0 SNil)) )
// Demo: change the testfx where x is {0, 1, 2, 3}
let testf4 = withOpenTuple2' testf3

let openTuple2_openTuple2Int_Bool_Bool = (BTupleType true 2 (SCons 
((BTupleType true 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))))
1 (SCons (BBoolType) 0 SNil)))  

val withOpenTupleTuple : x:bosqueTerm{subtypeOf openTuple2_openTuple2Int_Bool_Bool (getType x)} -> Tot (bool)
let withOpenTupleTuple x = match x with
| BTuple 2 seq -> false
| BTuple 3 seq -> true
| BTuple m seq -> true  

val withOpenTupleTuple' : x:bosqueTerm{openTuple2_openTuple2Int_Bool_Bool = (getType x)} -> Tot (y:bosqueTerm{isInt y})
let withOpenTupleTuple' x = match x with
| BTuple 2 seq -> let temp1 = nthTuple 0 2 x in let temp2 = nthTuple 0 2 temp1 in let _ = assert_norm(isInt temp2) in temp2
| BTuple 3 seq -> let temp1 = nthTuple 0 2 x in let temp2 = nthTuple 0 2 temp1 in temp2
| BTuple m seq -> let temp1 = nthTuple 0 2 x in let temp2 = nthTuple 0 2 temp1 in temp2

(* -------------------------------------------------------------------------------------------------------------------------------------- *)
