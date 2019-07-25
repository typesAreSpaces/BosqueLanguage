module Example 

type term_ = 
| ErrorTerm : term_
| NoneTerm : term_
| IntTerm : int -> term_
| BoolTerm : bool -> term_
| UnionTerm : term_ -> term_ -> term_

type type_ = 
| ErrorType 
| NoneType
| IntType
| BoolType
| UnionType

// Convention with UnionTerm: 
// its elements should be unique
val getType : term_ -> type_
let getType x = match x with
| ErrorTerm -> ErrorType
| NoneTerm -> NoneType
| IntTerm _ -> IntType
| BoolTerm _ -> BoolType
| UnionTerm _ _ -> UnionType

// I.e. subtype_ x y <-> x :> y
val subtype_ : term_ -> y:term_ -> (Tot bool)
let rec subtype_ x y = match x, y with
| ErrorTerm, ErrorTerm -> true
| NoneTerm, NoneTerm -> true
| IntTerm _, IntTerm _ -> true
| BoolTerm _, BoolTerm _ -> true
| UnionTerm x1 y1, UnionTerm x2 y2 -> (subtype_ x1 x2 || subtype_ y1 x2) && (subtype_ x1 y2 || subtype_ y1 y2)
| UnionTerm x1 y1, z -> subtype_ x1 z || subtype_ y1 z 
| _, _ -> false 
 
let test = subtype_ (UnionTerm (IntTerm 2) (BoolTerm true)) (IntTerm 323)
let test2 = subtype_ (UnionTerm (IntTerm 2) (BoolTerm true)) (NoneTerm)
let test2_ = subtype_ (UnionTerm (IntTerm 2) (BoolTerm true)) (UnionTerm NoneTerm (BoolTerm true))
let test2__ = subtype_ (UnionTerm (IntTerm 2) (BoolTerm true)) (UnionTerm (IntTerm 2) (UnionTerm NoneTerm (BoolTerm true)))
let test2___ = subtype_ (UnionTerm (IntTerm 2) (BoolTerm true)) (UnionTerm (BoolTerm true) (IntTerm 2))

(* Function with union as argument *)
type unionIntBool = x:term_{subtype_ (UnionTerm (IntTerm 19) (BoolTerm true)) x}

val f : x : unionIntBool -> term_ 
let f x = x

let test4 = f (IntTerm 100)
let test44 = f (BoolTerm true)
let test45 = f (UnionTerm (IntTerm 1) (BoolTerm false))
let test456 = f (UnionTerm (BoolTerm false) (IntTerm 1))
// let test444 = f (NoneTerm)

val maxWithUnion : unionIntBool -> term_ -> term_
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

let test5 = maxWithUnion (IntTerm 12) (IntTerm 10)
let test6 = maxWithUnion (IntTerm 10) (IntTerm 12)
let test7 = maxWithUnion (BoolTerm false) (IntTerm 12)

val eqTerm : term_ -> term_ -> bool
let eqTerm x y = match x, y with
| ErrorTerm, ErrorTerm -> true
| NoneTerm, NoneTerm -> true
| IntTerm x1, IntTerm y1 -> x1 = y1
| BoolTerm x1, BoolTerm y1 -> x1 = y1
| _, _ -> false 

val greaterOrEq : term_ -> term_ -> bool
let greaterOrEq x y = match x, y with
| IntTerm x1, IntTerm y1 -> x1 >= y1
| _, _ -> false 

let _ = assert (forall x y z. greaterOrEq (maxWithUnion (IntTerm x) (IntTerm y)) (IntTerm x) 
&& greaterOrEq (maxWithUnion (IntTerm x) (IntTerm y)) (IntTerm x)
&& (eqTerm (maxWithUnion (IntTerm x) (IntTerm y)) (IntTerm x) || eqTerm (maxWithUnion (IntTerm x) (IntTerm y)) (IntTerm y))
&& (eqTerm (maxWithUnion (BoolTerm z) (IntTerm x)) (IntTerm x))
)
