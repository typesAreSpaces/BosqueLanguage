module UnionType_alternative2

type bosqueTerm = 
| ErrorTerm : bosqueTerm
| NoneTerm : bosqueTerm
| IntTerm : int -> bosqueTerm
| BoolTerm : bool -> bosqueTerm

// Convention with UnionTerm: 
// its elements should be unique
type bosqueType = 
| ErrorType 
| NoneType
| IntType
| BoolType
| UnionType : bosqueType -> bosqueType -> bosqueType

val getType : bosqueTerm -> bosqueType
let getType x = match x with
| ErrorTerm -> ErrorType
| NoneTerm -> NoneType
| IntTerm _ -> IntType
| BoolTerm _ -> BoolType

// forall x y . bosqueSubtypeOf x y <===> x :> y
val bosqueSubtypeOf : bosqueType -> bosqueType -> (Tot bool)
let rec bosqueSubtypeOf x y = match x, y with
| ErrorType, ErrorType -> true
| NoneType, NoneType -> true
| IntType, IntType -> true
| BoolType, BoolType -> true
| UnionType x1 y1, UnionType x2 y2 -> (bosqueSubtypeOf x1 x2 || bosqueSubtypeOf y1 x2) && (bosqueSubtypeOf x1 y2 || bosqueSubtypeOf y1 y2)
| UnionType x1 y1, z -> bosqueSubtypeOf x1 z || bosqueSubtypeOf y1 z 
| _, _ -> false 

(* Testing *)
let test = bosqueSubtypeOf (UnionType IntType BoolType) IntType
let test2 = bosqueSubtypeOf (UnionType IntType BoolType) (NoneType)
let test2_ = bosqueSubtypeOf (UnionType IntType BoolType) (UnionType NoneType BoolType)
let test2__ = bosqueSubtypeOf (UnionType IntType BoolType) (UnionType IntType (UnionType NoneType BoolType))
let test2___ = bosqueSubtypeOf (UnionType IntType BoolType) (UnionType BoolType IntType)


type typeUnionIntBool = x:bosqueType{bosqueSubtypeOf (UnionType IntType BoolType) x}
type termUnionIntBool = x:bosqueTerm{bosqueSubtypeOf (UnionType IntType BoolType) (getType x)}

(* Function with union as argument *)
val f : x : typeUnionIntBool -> bosqueType
let f x = x

(* Testing *)
let test4 = f IntType
let test44 = f BoolType
let test45 = f (UnionType IntType BoolType)
let test456 = f (UnionType BoolType IntType)
// The following fails, as expected
// let test444 = f (NoneType)

val maxWithUnion : termUnionIntBool -> bosqueTerm -> bosqueTerm
let maxWithUnion x y = match x with 
| BoolTerm z -> (match y with 
  | IntTerm x2 -> IntTerm x2
  | _ -> ErrorTerm
) 
| IntTerm x1 -> (match y with 
  | IntTerm x2 -> if (x1 > x2) then IntTerm x1 else IntTerm x2
  | _ -> ErrorTerm
)
| _ -> ErrorTerm

(* Testing *)
let test5 = maxWithUnion (IntTerm 12) (IntTerm 10)
let test6 = maxWithUnion (IntTerm 10) (IntTerm 12)
let test7 = maxWithUnion (BoolTerm false) (IntTerm 12)

val eqTerm : bosqueTerm -> bosqueTerm -> bool
let eqTerm x y = match x, y with
| ErrorTerm, ErrorTerm -> true
| NoneTerm, NoneTerm -> true
| IntTerm x1, IntTerm y1 -> x1 = y1
| BoolTerm x1, BoolTerm y1 -> x1 = y1
| _, _ -> false 

val greaterOrEq : bosqueTerm -> bosqueTerm -> bool
let greaterOrEq x y = match x, y with
| IntTerm x1, IntTerm y1 -> x1 >= y1
| _, _ -> false 

let _ = assert (forall x y z. greaterOrEq (maxWithUnion (IntTerm x) (IntTerm y)) (IntTerm x) 
&& greaterOrEq (maxWithUnion (IntTerm x) (IntTerm y)) (IntTerm y)
&& (eqTerm (maxWithUnion (IntTerm x) (IntTerm y)) (IntTerm x) || eqTerm (maxWithUnion (IntTerm x) (IntTerm y)) (IntTerm y))
&& (eqTerm (maxWithUnion (BoolTerm z) (IntTerm x)) (IntTerm x))
)
