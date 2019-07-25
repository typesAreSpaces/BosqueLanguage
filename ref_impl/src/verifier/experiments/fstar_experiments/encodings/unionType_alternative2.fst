module UnionType_alternative2

type tuple__2 (t_1 : Type) (t_2 : Type) =
| Mktuple__2: _1:t_1 -> _2:t_2 -> tuple__2 t_1 t_2 

(* Dynamic: depends on the tuples, records, 
   and entities created by user *)
noeq type bosqueTerm = 
| BError : bosqueTerm
| BNone : bosqueTerm
| BInt : int -> bosqueTerm
| BBool : bool -> bosqueTerm
| BTuple__2 : tuple__2 (t_1 : Type) (t_2 : Type) -> bosqueTerm

// Convention with UnionTerm: 
// its elements should be unique
type bosqueType = 
| BTypeError 
| BTypeNone
| BTypeInt
| BTypeBool
| BTypeUnion : bosqueType -> bosqueType -> bosqueType
| BTypeTuple__2

// let test0a = Mktuple__2 (BInt 2) (BInt 4)

val getType : bosqueTerm -> bosqueType
let getType x = match x with
| BError -> BTypeError
| BNone -> BTypeNone
| BInt _ -> BTypeInt
| BBool _ -> BTypeBool
| BTuple__2 _ -> BTypeTuple__2

// forall x y . bosqueSubtypeOf x y <===> x :> y
val bosqueSubtypeOf : bosqueType -> bosqueType -> (Tot bool)
let rec bosqueSubtypeOf x y = match x, y with
| BTypeError, BTypeError -> true
| BTypeNone, BTypeNone -> true
| BTypeInt, BTypeInt -> true
| BTypeBool, BTypeBool -> true
| BTypeTuple__2, BTypeTuple__2 -> true // FIX: This is wrong, but I just want to see how it behaves
| BTypeUnion x1 y1, BTypeUnion x2 y2 -> (bosqueSubtypeOf x1 x2 || bosqueSubtypeOf y1 x2) && (bosqueSubtypeOf x1 y2 || bosqueSubtypeOf y1 y2)
| BTypeUnion x1 y1, z -> bosqueSubtypeOf x1 z || bosqueSubtypeOf y1 z 
| _, _ -> false

(* Testing *)
let test1a = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) BTypeInt
let test1b = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeNone)
let test1c = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeNone BTypeBool)
let test1d = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeInt (BTypeUnion BTypeNone BTypeBool))
let test1e = bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (BTypeUnion BTypeBool BTypeInt)

(* ---------------------------------------------------------------- *)
(* Type projectors *)
val isBool : bosqueTerm -> bool
let isBool x = match x with 
| BBool _ -> true
| _ -> false 

val isInt : bosqueTerm -> bool
let isInt x = match x with 
| BInt _ -> true
| _ -> false 
(* ---------------------------------------------------------------- *)

(* ---------------------------------------------------------------- *)
(* Function to extract boolean, mainly used inside conditionals and assertions *)
val extractBool : x:bosqueTerm{isBool x} -> bool
let extractBool x = match x with
| BBool y -> y
(* ---------------------------------------------------------------- *)

(* ---------------------------------------------------------------- *)
(* Definition of UnionType *)
type typeUnionIntBool = x:bosqueType{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) x}
type termUnionIntBool = x:bosqueTerm{bosqueSubtypeOf (BTypeUnion BTypeInt BTypeBool) (getType x)}

type termInt = x:bosqueTerm{isInt x}
(* ---------------------------------------------------------------- *)

(* Function with union as argument *)
val f : x : typeUnionIntBool -> bosqueType
let f x = x

(* Testing *)
let test2a = f BTypeInt
let test2b = f BTypeBool
let test2c = f (BTypeUnion BTypeInt BTypeBool)
let test2d = f (BTypeUnion BTypeBool BTypeInt)
// The following fails, as expected
// let test2e = f (BTypeNone)

(* Definition of equality relation on terms *)
val eqTerm : bosqueTerm -> bosqueTerm -> bosqueTerm
let eqTerm x y = match x, y with
| BError, BError -> BBool true
| BNone, BNone -> BBool true
| BInt x1, BInt y1 -> BBool (x1 = y1)
| BBool x1, BBool y1 -> BBool (x1 = y1)
| BTuple__2 _, BTuple__2 _ -> BBool true // FIX: This is wrong, but I just want to see how it behaves
| _, _ -> BError 

(* Definition of greater than or equal relation on terms *)
val greaterOrEq : bosqueTerm -> bosqueTerm -> bosqueTerm
let greaterOrEq x y = match x, y with
| BInt x1, BInt y1 -> BBool (x1 >= y1)
| _, _ -> BError






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

(* Testing *)
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
| BInt x1 -> if (extractBool (greaterOrEq x y)) then BInt x1 else y
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

let _ = assert (forall x y z. extractBool (greaterOrEq (max (BInt x) (BInt y)) (BInt x) )
&& extractBool (greaterOrEq (max (BInt x) (BInt y)) (BInt y))
&& (extractBool (eqTerm (max (BInt x) (BInt y)) (BInt x)) || extractBool (eqTerm (max (BInt x) (BInt y)) (BInt y)))
&& (extractBool (eqTerm (max (BInt x) (BBool z)) (BInt x)))
)
(* ---------------------------------------------------------------- *)
