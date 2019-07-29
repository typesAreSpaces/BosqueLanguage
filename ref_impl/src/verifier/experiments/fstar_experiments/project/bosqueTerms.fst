module BosqueTerms

open Sequence

(* Dynamic: depends on the 
   entities created by user *) 
type bosqueTerm = 
| BNone : bosqueTerm
| BInt : int -> bosqueTerm
| BBool : bool -> bosqueTerm
| BTuple : n:nat -> sequence bosqueTerm n -> bosqueTerm 
| BError : bosqueTerm

(* Definition of equality relation on Bosque terms *)
val eqTerm_aux : #n:nat -> (x:sequence bosqueTerm n) -> sequence bosqueTerm n -> Tot bosqueTerm (decreases x)
val eqTerm : x:bosqueTerm -> bosqueTerm -> Tot bosqueTerm (decreases x)
let rec eqTerm x y = match x, y with
| BNone, BNone -> BBool true
| BInt x1, BInt y1 -> BBool (x1 = y1)
| BBool x1, BBool y1 -> BBool (x1 = y1)
| BTuple n1 seq1, BTuple n2 seq2 -> if (n1 <> n2) then BError
                                   else eqTerm_aux #n1 seq1 seq2
// | BError, BError -> BBool true
| _, _ -> BError
and 
eqTerm_aux #n x y = match x with
| SNil -> (match y with
         | SNil -> BBool true
         | _ -> BError
         )
| SCons x1 xs1 -> (match y with
                 | SNil -> BError
                 | SCons y1 ys1 -> (match (eqTerm x1 y1) with
                                  | BBool b1 -> (match (eqTerm_aux xs1 ys1) with
                                               | BBool b2 -> BBool (b1 && b2)
                                               | _ -> BError
                                               )
                                  | _ -> BError 
                                  )
                 )

(* Definition of greater than or equal relation on Bosque terms *)
val greaterOrEq : bosqueTerm -> bosqueTerm -> Tot bosqueTerm
let greaterOrEq x y = match x, y with
| BInt x1, BInt y1 -> BBool (x1 >= y1)
| _, _ -> BError

(* Tuple projector *)
val nthTuple : index:int -> dimension:nat -> bosqueTerm -> Tot bosqueTerm
let rec nthTuple index dimension y = match y with
| BTuple 0 SNil -> if (index < 0 || dimension <> 0) then BError else BNone
| BTuple dimension'' (SCons x #dimension' xs) -> 
  if (index < 0 || dimension <> dimension'') then BError else
  if (index >= dimension) then BNone else
  if index = 0 then x
  else nthTuple (index-1) dimension' (BTuple dimension' xs)
| _ -> BError


