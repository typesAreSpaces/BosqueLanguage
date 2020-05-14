module NSMain__main_main

open Sequence
open List
open BosqueTypes
open BosqueTerms
open BosqueCollections
open Util

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
