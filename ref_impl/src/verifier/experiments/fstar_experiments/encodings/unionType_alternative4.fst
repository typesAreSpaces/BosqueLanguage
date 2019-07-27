module UnionType_alternative4

// TODO: Implement tuples as recursive structures
// Same for records
 
type sequence 'a : nat -> Type = 
| CNil : sequence 'a 0
| CCons : hd:'a -> #n:nat -> tl : sequence 'a n -> sequence 'a (n + 1) 

val mapSequence : ('a -> Tot 'b) -> #n:nat -> (sequence 'a n) -> Tot (sequence 'b n)
let rec mapSequence f #n seq = match seq with
| CNil -> CNil
| CCons hd tl -> CCons (f hd) (mapSequence f tl)

(* Dynamic: depends on the 
   entities created by user *) 
noeq type bosqueTerm = 
| BError : bosqueTerm
| BNone : bosqueTerm
| BInt : int -> bosqueTerm
| BBool : bool -> bosqueTerm
| BTuple : n:nat -> sequence bosqueTerm n -> bosqueTerm 

// Convention with UnionTerm: 
// its elements should be unique
type bosqueType =
| BTypeError 
| BTypeNone
| BTypeInt
| BTypeBool
| BTypeUnion : bosqueType -> bosqueType -> bosqueType
// The bool indicates if the Tuple is open or not
| BTypeEmptyTuple
| BTypeTuple : bool -> n:nat -> sequence bosqueType n -> bosqueType

val nthTuple : index:int -> dimension:int -> bosqueTerm -> Tot bosqueTerm
let rec nthTuple index dimension y = match y with
| BTuple 0 CNil -> if (index < 0 || dimension <> 0) then BError else BNone
| BTuple dimension'' (CCons x #dimension' xs) -> 
  if (index < 0 || dimension <> dimension'') then BError else
  if (index >= dimension) then BNone else
  if index = 0 then x
  else nthTuple (index-1) dimension' (BTuple dimension' xs)
| _ -> BError 

val isTuple : n:nat -> x:bosqueTerm -> bool
let isTuple n x = match x with
| BTuple m _ -> n = m
| _ -> false

val extractTuple : n:nat -> x:bosqueTerm{isTuple n x} -> sequence bosqueTerm n
let extractTuple n x = match x with
| BTuple _ seq -> seq

let aaa = BTuple 2 (CCons (BInt 3) (CCons (BBool true) CNil))
let bb = extractTuple 2 aaa

val getType : bosqueTerm -> Tot bosqueType
let rec getType x = match x with
| BError -> BTypeError
| BNone -> BTypeNone
| BInt _ -> BTypeInt
| BBool _ -> BTypeBool
| BTuple 0 CNil -> BTypeEmptyTuple
| BTuple n CNil -> BTypeError
| BTuple 0 (CCons _ _) -> BTypeError
| BTuple n (CCons hd #m tl) -> 
  if (m + 1 <> n) then BTypeError 
  else BTypeTuple false (m + 1) (mapSequence getType (CCons hd tl))
// | BTuple n (CCons hd #m tl) -> if (m + 1 <> n) then BTypeError else BTypeTuple false (m+1) (mapSequence getType (CCons hd tl))
// | BTuple n y -> BTypeTuple false n (mapSequence getType y)

// forall x y . bosqueSubtypeOf x y <===> x :> y
val bosqueSubtypeOf : bosqueType -> bosqueType -> (Tot bool)
let rec bosqueSubtypeOf x y = match x, y with
| BTypeError, BTypeError -> true
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
| BTypeUnion x1 y1, BTypeUnion x2 y2 -> (bosqueSubtypeOf x1 x2 || bosqueSubtypeOf y1 x2) 
  && (bosqueSubtypeOf x1 y2 || bosqueSubtypeOf y1 y2)
| BTypeUnion x1 y1, z -> bosqueSubtypeOf x1 z || bosqueSubtypeOf y1 z 
// Missing: BTuple ? ?, x
| _, _ -> false

(* Testing: bosqueSubtypeOf *)
let test1a = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) BTypeInt
let test1b = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeNone)
let test1c = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeNone BTypeBool)
let test1d = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeInt (BTypeUnion BTypeNone BTypeBool))
let test1e = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeBool BTypeInt)

(* ---------------------------------------------------------------- *)
(* Type checkers *)
val isBool : bosqueTerm -> bool
let isBool x = match x with 
| BBool _ -> true
| _ -> false 

val isInt : bosqueTerm -> bool
let isInt x = match x with 
| BInt _ -> true
| _ -> false 

val isTuple' : n:int -> x:bosqueTerm -> bool
let isTuple' n x = match x with
| BTuple m _ -> n = m
| _ -> false
(* ---------------------------------------------------------------- *)

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

(* ---------------------------------------------------------------- *)
(* Function to extract boolean, mainly used inside conditionals (fstar programming language) 
   and assertions (z3 smt solver) *)
val extractBool : x:bosqueTerm{isBool x} -> bool
let extractBool x = match x with
| BBool y -> y
(* ---------------------------------------------------------------- *)

(* ---------------------------------------------------------------- *)
(* Definition of UnionType *)
type typeUnionIntBool = x:bosqueType{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) x}
type termUnionIntBool = x:bosqueTerm{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (getType x)} 
(* Definition of IntType *)
type termInt = x:bosqueTerm{isInt x} 
(* ---------------------------------------------------------------- *)

(* Function with union as argument *)
val f : x : typeUnionIntBool -> bosqueType
let f x = x

(* Testing: BTypeUnion *)
let test2a = f BTypeInt
let test2b = f BTypeBool
let test2c = f (BTypeUnion BTypeInt BTypeBool)
let test2d = f (BTypeUnion BTypeBool BTypeInt)
// The following fails, as expected
// let test2e = f (BTypeNone)

(* Definition of equality relation on terms *)
val eqType : bosqueType -> bosqueType -> bool
let eqType x y = match x, y with
| BTypeError, BTypeError -> true 
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
| BTypeUnion _ _ , BTypeUnion _ _ -> true // FIX: This is incomplete
| BTypeTuple, BTypeTuple -> true
| _, _ -> false 


val eqTerm : bosqueTerm -> bosqueTerm -> bosqueTerm
let eqTerm x y = match x, y with
// | BError, BError -> BBool true
| BNone, BNone -> BBool true
| BInt x1, BInt y1 -> BBool (x1 = y1)
| BBool x1, BBool y1 -> BBool (x1 = y1)
| _, _ -> BError 

(* Definition of greater than or equal relation on terms *)
val greaterOrEq : bosqueTerm -> bosqueTerm -> bosqueTerm
let greaterOrEq x y = match x, y with
| BInt x1, BInt y1 -> BBool (x1 >= y1)
| _, _ -> BError

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

