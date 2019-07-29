module Testing
 
open Sequence
open BosqueTerms
open BosqueTypes

(* --------------------------------------------------------------- *)

let aaa = BTuple 2 (CCons (BInt 3) (CCons (BBool true) CNil))
let bb = extractTuple 2 aaa

(* Testing: bosqueSubtypeOf *)
let testa0 = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) BTypeInt
let testa1 = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeNone)
let testa2 = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeNone BTypeBool)
let testa3 = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeInt (BTypeUnion BTypeNone BTypeBool))
let testa4 = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeBool BTypeInt)

(* Testing: BTuple *)
let testb0 = BTuple 2 (CCons (BInt 342) (CCons (BBool true) (CNil)))
// The following fails, as expected
// let test0a1 = BTuple 3 (CCons (BInt 342) (CCons (BBool true) (CNil)))
let testb1 = BTuple 0 (CNil)
let testb2 = isTuple 2 testb0
let testb3 = isTuple 3 testb0
let testb4 = isTuple 2 (BInt 234)
let testb5 = nthTuple 0 2 testb0
let testb6 = nthTuple 0 3 testb0
let testb7 = nthTuple 1 2 testb0
let testb8 = nthTuple 2 2 testb0
let testb9 = nthTuple 2 10000 testb0
let testb10 = nthTuple 10001 10000 testb0
let testb11 = nthTuple (-1) 2 testb0
let testb12 = BTuple 0 CNil
let testb13 = isTuple 0 testb12
let testb14 = isTuple 10 testb12

(* Testing: getType *)
let testc1 = BTuple 2 (CCons aaa ((CCons testb0) CNil))
let testc2 = getType testb0
let testc3 = getType testb1
let testc4 = getType testc1

(* -------------------------------------------------------------------------------------------------------------- *)

(* Examples *)

val maxWithUnion : termUnionIntBool -> bosqueTerm -> bosqueTerm
let maxWithUnion x y = match x with 
| BBool z -> (match y with 
  | BInt x2 -> BInt x2
  | _ -> BError
) 
| BInt x1 -> (match y with 
  | BInt x2 -> if (x1 > x2) then BInt x1 else BInt x2
  | _ -> BError
)
| _ -> BError

(* Testing: maxWithUnion *)
let testd1 = maxWithUnion (BInt 12) (BInt 10)
let testd2 = maxWithUnion (BInt 10) (BInt 12)
let testd3 = maxWithUnion (BBool false) (BInt 12)

(* The following assertion proves that maxWithUnion is correctly implemented *)
let _ = assert (forall x y z. extractBool (greaterOrEq (maxWithUnion (BInt x) (BInt y)) (BInt x)) 
&& extractBool (greaterOrEq (maxWithUnion (BInt x) (BInt y)) (BInt y))
&& (extractBool (eqTerm (maxWithUnion (BInt x) (BInt y)) (BInt x)) || extractBool (eqTerm (maxWithUnion (BInt x) (BInt y)) (BInt y)))
&& extractBool ((eqTerm (maxWithUnion (BBool z) (BInt x)) (BInt x)))
)

val maxWithUnion2 : termUnionIntBool -> termInt -> termInt
let maxWithUnion2 x y = match x with 
| BBool z -> (match y with 
  | BInt x2 -> BInt x2
  | _ -> BError
) 
| BInt x1 -> if (extractBool (greaterOrEq x y)) then x else y
| _ -> BError

let _ = assert (forall x y z. extractBool (greaterOrEq (maxWithUnion2 (BInt x) (BInt y)) (BInt x)) 
&& extractBool (greaterOrEq (maxWithUnion2 (BInt x) (BInt y)) (BInt y))
&& (extractBool (eqTerm (maxWithUnion2 (BInt x) (BInt y)) (BInt x)) || extractBool (eqTerm (maxWithUnion2 (BInt x) (BInt y)) (BInt y)))
&& (extractBool ((eqTerm (maxWithUnion2 (BBool z) (BInt x)) (BInt x))))
)

val max : x:bosqueTerm{isInt x} -> y:bosqueTerm{isInt y} -> z:bosqueTerm{isInt z}
let max x y = if (extractBool (greaterOrEq x y)) then x else y

let _ = assert (forall x y. extractBool (greaterOrEq (max (BInt x) (BInt y)) (BInt x) )
&& extractBool (greaterOrEq (max (BInt x) (BInt y)) (BInt y))
&& (extractBool (eqTerm (max (BInt x) (BInt y)) (BInt x)) || extractBool (eqTerm (max (BInt x) (BInt y)) (BInt y)))
)

// The following fails, as expected
// let _ = assert (forall x y z. extractBool (greaterOrEq (max (BInt x) (BInt y)) (BInt x) )
// && extractBool (greaterOrEq (max (BInt x) (BInt y)) (BInt y))
// && (extractBool (eqTerm (max (BInt x) (BInt y)) (BInt x)) || extractBool (eqTerm (max (BInt x) (BInt y)) (BInt y)))
// && (extractBool (eqTerm (max (BInt x) (BBool z)) (BInt x)))
// )

// val maxWithTuple : x:bosqueTerm{isTuple 2 x} -> y:bosqueTerm{isInt y} -> z:bosqueTerm{isInt z}
// let maxWithTuple x y = if (extractBool (greaterOrEq (nthTuple 0 2 x) y)) then (nthTuple 0 2 x) else y

val maxWithTuple : x:bosqueTerm{isTuple 2 x} -> y:bosqueTerm{isInt y} -> bosqueTerm
let maxWithTuple x y = let xAt0 = nthTuple 0 2 x in match xAt0 with 
| BInt x1 -> if (extractBool (greaterOrEq xAt0 y)) then xAt0 else y
| _ -> BError

(* Testing: maxWithTuple *)
let test4a = maxWithTuple (testb0) (BInt 1203)
let test4b = maxWithTuple (testb0) (BInt (-12))

// The following fails, as expected
// let _ = assert (forall x y . extractBool (greaterOrEq (maxWithTuple x y) (nthTuple 0 2 x)))

let _ = assert (forall x y . (eqType (getType (nthTuple 0 2 x)) (BTypeInt)) ==> extractBool (greaterOrEq (maxWithTuple x y) (nthTuple 0 2 x)))

(* ---------------------------------------------------------------- *)

