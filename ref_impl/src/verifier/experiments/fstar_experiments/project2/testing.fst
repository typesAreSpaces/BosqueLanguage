module Testing
 
open Sequence
open BosqueTerms
open BosqueTypes

(* --------------------------------------------------------------- *)

let aaa = BTuple 2 (SCons (BInt 3) 1 (SCons (BBool true) 0 SNil))
// let bb = extractTuple 2 aaa

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
let testc1 = BTuple 2 (SCons aaa 1 ((SCons testb0) 0 SNil))
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
| BBool _ -> y 
| BInt _ -> if (extractBool (greaterOrEq x y)) then x else y

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

// // The following fails, as expected
// let _ = assert (forall x y z. extractBool (greaterOrEq (max (BInt x) (BInt y)) (BInt x) )
// && extractBool (greaterOrEq (max (BInt x) (BInt y)) (BInt y))
// && (extractBool (eqTerm (max (BInt x) (BInt y)) (BInt x)) || extractBool (eqTerm (max (BInt x) (BInt y)) (BInt y)))
// && (extractBool (eqTerm (max (BInt x) (BBool z)) (BInt x)))
// )

val maxWithTuple : x:bosqueTerm{isTuple false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)) x}
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm{isInt z}
let maxWithTuple x y = 
  let xAt0 = nthTuple 0 2 x in 
    if (extractBool (greaterOrEq xAt0 y)) then xAt0 
    else y
    
(* Testing: maxWithTuple *)
let test4a = maxWithTuple (testb0) (BInt 1203)
let test4b = maxWithTuple (testb0) (BInt (-12))

let _ = assert (forall x y . extractBool (greaterOrEq (maxWithTuple x y) (nthTuple 0 2 x)))

let _ = assert (forall x y . (eqType (getType (nthTuple 0 2 x)) BIntType) ==> extractBool (greaterOrEq (maxWithTuple x y) (nthTuple 0 2 x)))

val maxWithTuple2 : x:bosqueTerm{isTuple false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)) x} 
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm{isInt z}
let maxWithTuple2 x y = match x with 
| BTuple 2 seq -> 
  let xAt0 = nthTuple 0 2 x in 
    match xAt0 with 
    | BInt x1 -> if (extractBool (greaterOrEq xAt0 y)) then xAt0 else y
    | _ -> BError

val withOpenTuple : x:bosqueTerm{subtypeOf (BTupleType true 0 SNil) (getType x)} -> Tot bool
let withOpenTuple x = match x with 
| BTuple m seq -> false

// val withClosedTuple : x:bosqueTerm{subtypeOf (BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))) (getType x)} -> Tot int
// let withClosedTuple x = match x with 
// | BTuple _ _ -> 0

let closedTuple2_Int_Bool = (BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)))

val maxWithTuple2'' : x:bosqueTerm{(subtypeOf closedTuple2_Int_Bool (getType x))} 
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm{isInt z}
let maxWithTuple2'' x y = match x with 
| BTuple 2 seq -> 
  let xAt0 = nthTuple 0 2 x in 
    if (extractBool (greaterOrEq xAt0 y)) then xAt0 else y

val maxWithTuple2''' : x:bosqueTerm{(subtypeOf closedTuple2_Int_Bool (getType x))} 
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm{isInt z}
let maxWithTuple2''' x y = let xAt0 = nthTuple 0 2 x in 
    if (extractBool (greaterOrEq xAt0 y)) then xAt0 else y
  
// // Idk why the following doesn't work like maxWithTuple2''
// val maxWithTuple2' : x:bosqueTerm{subtypeOf (BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))) (getType x)} 
//   -> y:bosqueTerm{isInt y} 
//   -> z:bosqueTerm
// let maxWithTuple2' x y = match x with 
// | BTuple 2 seq -> 
//   let xAt0 = nthTuple 0 2 x in 
//     if (extractBool (greaterOrEq xAt0 y)) then xAt0 else y

let openTuple2_Int_Bool = (BTupleType true 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)))

val withOpenTuple2 : x:bosqueTerm{subtypeOf openTuple2_Int_Bool (getType x)} -> Tot bool
let withOpenTuple2 x = match x with
| BTuple 2 seq -> false
| BTuple 3 seq -> true
| BTuple m seq -> true

let ahhhh1 = BTuple 1 (SCons (BInt 3) 0 SNil)
let ahhhh2 = BTuple 2 (SCons (BBool true) 1 (SCons (BInt 3) 0 SNil) )
let ahhhh2' = BTuple 2 (SCons (BInt 0) 1 (SCons (BBool true) 0 SNil) )
let ahhhh3 = BTuple 3 (SCons (BInt 0) 2 (SCons (BBool true) 1 (SCons (BInt 12) 0 SNil)) )
// Demo: change the ahhhhx where x is {1, 2, 2', 3}
let bhhhh = withOpenTuple2 ahhhh3

let openTuple2_openTuple2Int_Bool_Bool = (BTupleType true 2 (SCons ((BTupleType true 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)))) 1 (SCons (BBoolType) 0 SNil)))

val withOpenTupleTuple2 : x:bosqueTerm{subtypeOf openTuple2_openTuple2Int_Bool_Bool (getType x)} -> Tot (bool)
let withOpenTupleTuple2 x = match x with
| BTuple 2 seq -> false
| BTuple 3 seq -> true
| BTuple m seq -> true

val withOpenTupleTuple3 : x:bosqueTerm{subtypeOf openTuple2_openTuple2Int_Bool_Bool (getType x)} -> Tot (y:bosqueTerm{isInt y})
let withOpenTupleTuple3 x = match x with
| BTuple 2 seq -> let temp1 = nthTuple 0 2 x in let temp2 = nthTuple 0 2 temp1 in temp2
| BTuple 3 seq -> let temp1 = nthTuple 0 2 x in let temp2 = nthTuple 0 2 temp1 in temp2
| BTuple m seq -> let temp1 = nthTuple 0 2 x in let temp2 = nthTuple 0 2 temp1 in temp2

// // Idk why the following doesn't work like withOpenTuple2'
// val withOpenTuple2' : x:bosqueTerm{subtypeOf (BTupleType true 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))) (getType x)} -> Tot bool
// let withOpenTuple2' x = match x with
// | BTuple 2 seq -> false
// | BTuple 3 seq -> false 
// | BTuple m seq -> true



let tupleTypeExample = (BTuple 2 (SCons (BInt 2) 1 (SCons (BBool true) 0 SNil)))

let testing = subtypeOf (BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))) (getType tupleTypeExample)
let testing2 = subtypeOf (BTupleType false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil))) (getType (BTuple 2 (SCons (BInt 2) 1 (SCons (BBool true) 0 SNil))))

let hmm = maxWithTuple2'' tupleTypeExample (BInt 33)

// let hmm2 = let whatt = (BTuple 2 (SCons (BInt 2) 1 (SCons (BBool true) 0 SNil))) in maxWithTuple2'' whatt (BInt 33)

let hmm3 = maxWithTuple2'' (BTuple 2 (SCons (BInt 2) 1 (SCons (BBool true) 0 SNil))) (BInt 33)

val maxWithTuple3 : x:bosqueTerm{isTuple true 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)) x} 
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm
let maxWithTuple3 x y = match x with 
| BTuple 2 seq ->
  let xAt0 = nthTuple 0 2 x in 
    assert (isInt xAt0);
    match xAt0 with 
    | BInt x1 -> if (extractBool (greaterOrEq xAt0 y)) then xAt0 else y
    | _ -> BError

val maxWithTuple4 : x:bosqueTerm{isTuple2 false 2 (SCons (BIntType) 1 (SCons (BBoolType) 0 SNil)) x} 
  -> y:bosqueTerm{isInt y} 
  -> z:bosqueTerm{isInt z}
let maxWithTuple4 x y = 
  let xAt0 = nthTuple 0 2 x in 
    assert (isInt xAt0);
    match xAt0 with 
    | BInt x1 -> if (extractBool (greaterOrEq xAt0 y)) then xAt0 else y
    | _ -> BError

(* Testing: maxWithTuple2 *)
let test5a = maxWithTuple2 (testb0) (BInt 1203)
let test5b = maxWithTuple2 (testb0) (BInt (-12))

// let _ = assert (forall x y . extractBool (greaterOrEq (maxWithTuple2 x y) (nthTuple 0 2 x)))

let _ = assert (forall x y . (eqType (getType (nthTuple 0 2 x)) BIntType) ==> extractBool (greaterOrEq (maxWithTuple2 x y) (nthTuple 0 2 x)))

(* ---------------------------------------------------------------- *)
