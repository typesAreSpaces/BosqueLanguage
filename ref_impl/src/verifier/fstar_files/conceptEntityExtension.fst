module ConceptEntityExtension 

open Sequence
open BosqueTypes
open BosqueTerms

(* ------------------------------------------------------------------------- *)
(* Extending the types with user defined classes --------------------------- *)
type person = 
| MkPerson : x:bosqueTerm{subtypeOf BIntType (getType x)} -> person

type employer = 
| MkEmployer : x:bosqueTerm{subtypeOf BIntType (getType x)} -> person -> employer

let person1 = MkPerson (BInt 3)
let person2 = MkPerson (BInt 4)

let employer1 = MkEmployer (BInt 4) (MkPerson (BInt 3))
let employer1' = MkEmployer (BInt 4) person1
let employer2 = MkEmployer (BInt 4) person2

let compareTestPerson = person1 = person2
let compareTestEmployer1 = employer1 = employer1'
let compareTestEmployer2 = employer1 = employer2 

type string_string =
| MkString_String : 
  x1:bosqueTerm{subtypeOf (BTypedStringType BAnyType) (getType x1)}
  ->  x2:bosqueTerm{subtypeOf (BTypedStringType BAnyType) (getType x2)}
  -> string_string

let test_ss =  MkString_String (BTypedString "Hello" BAnyType) (BTypedString "Bye" BIntType) 

type string_tuple0 = 
| MkString_Tuple0 : 
  x1:bosqueTerm{subtypeOf (BTypedStringType BAnyType) (getType x1)} 
  -> x2:bosqueTerm{subtypeOf (BTupleType false 0 SNil) (getType x2)} 
  -> string_tuple0
  
let test_st0 = MkString_Tuple0 (BTypedString "Hello" BAnyType) (BTuple 0 (SNil))

type string_tuple1 = 
| MkString_Tuple1 : 
  x1:bosqueTerm{subtypeOf (BTypedStringType BAnyType) (getType x1)} 
  -> x2:bosqueTerm{subtypeOf (BTupleType false 1 (SCons (BIntType) 0 SNil)) (getType x2)}
  -> string_tuple1

let bt1 = (BTuple 1 (SCons (BInt 3) 0 SNil))
let bt1_fake = (BTuple 1 (SCons (BNone) 0 SNil))

val whatf : x2:bosqueTerm{subtypeOf (BTupleType false 1 (SCons (BIntType) 0 SNil)) (getType x2)} -> x2:bosqueTerm{subtypeOf (BTupleType false 1 (SCons (BIntType) 0 SNil)) (getType x2)}
let whatf x = x

let hmm = whatf bt1

let test_st1 = MkString_Tuple1 (BTypedString "Hello" BAnyType) bt1

// The following breaks
// let test_st2 = MkString_Tuple1 (BTypedString "Hello" BAnyType) bt1_fake 

(* ---------------------------------------------------------------------------------------------- *)
(* This doesn't seems to work *)
// let hmm = whatf (BTuple 1 (SCons (BInt 3) 0 SNil)) 
// let test_st1 = MkString_Tuple2 (BTypedString "Hello" BAnyType) (BTuple 1 (SCons (BInt 3) 0 SNil))
(* ---------------------------------------------------------------------------------------------- *)


type string_tuple2 = 
| MkString_Tuple2 : 
  x1:bosqueTerm{subtypeOf (BTypedStringType BAnyType) (getType x1)} 
  -> x2:bosqueTerm{subtypeOf (BTupleType false 2 (SCons (BIntType) 1 (SCons (BIntType) 0 SNil))) (getType x2)} 
  -> string_tuple2

let bt2 = (BTuple 2 (SCons (BInt 3) 1 (SCons (BInt 4) 0 SNil)))
let test_st2 = MkString_Tuple2 (BTypedString "Hello" BAnyType) bt2   
(* ------------------------------------------------------------------------- *)
