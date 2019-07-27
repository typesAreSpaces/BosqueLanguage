module Testing
 
open Sequence
open BosqueTerms
open BosqueTypes

(* --------------------------------------------------------------- *)

let aaa = BTuple 2 (CCons (BInt 3) (CCons (BBool true) CNil))
let bb = extractTuple 2 aaa

(* Testing: bosqueSubtypeOf *)
let test1a = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) BTypeInt
let test1b = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeNone)
let test1c = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeNone BTypeBool)
let test1d = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeInt (BTypeUnion BTypeNone BTypeBool))
let test1e = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeBool BTypeInt)

(* Testing: BTuple *)
let test0a = BTuple 2 (CCons (BInt 342) (CCons (BBool true) (CNil)))
let test0b = isTuple 2 test0a
let test0b0 = isTuple 3 test0a
let test0c = isTuple 2 (BInt 234)
let test0d0 = nthTuple 0 2 test0a  
let test0d00 = nthTuple 0 3 test0a
let test0d1 = nthTuple 1 2 test0a
let test0d2 = nthTuple 2 2 test0a
let test0d20 = nthTuple 2 10000 test0a
let test0d200 = nthTuple 10001 10000 test0a
let test0d3 = nthTuple (-1) 2 test0a
let test0a_ = BTuple 0 CNil
let test0b_ = isTuple 0 test0a_
let test0c_ = isTuple 10 test0a_

(* Testing: BTypeUnion *)
let test2a = f BTypeInt
let test2b = f BTypeBool
let test2c = f (BTypeUnion BTypeInt BTypeBool)
let test2d = f (BTypeUnion BTypeBool BTypeInt)
// The following fails, as expected
// let test2e = f (BTypeNone)

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
let test3a = maxWithUnion (BInt 12) (BInt 10)
let test3b = maxWithUnion (BInt 10) (BInt 12)
let test3c = maxWithUnion (BBool false) (BInt 12)

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
let test4a = maxWithTuple (test0a) (BInt 1203)
let test4b = maxWithTuple (test0a) (BInt (-12))

// The following fails, as expected
// let _ = assert (forall x y . extractBool (greaterOrEq (maxWithTuple x y) (nthTuple 0 2 x)))

let _ = assert (forall x y . (eqType (getType (nthTuple 0 2 x)) (BTypeInt)) ==> extractBool (greaterOrEq (maxWithTuple x y) (nthTuple 0 2 x)))

(* ---------------------------------------------------------------- *)

