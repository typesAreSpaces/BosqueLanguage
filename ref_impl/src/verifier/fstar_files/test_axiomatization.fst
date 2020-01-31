module Test_axiomatization

open List
open BosqueTypes
open BosqueTerms
open BosqueCollections

val m_length : (p : bosqueTerm -> bool) -> ty:bosqueType -> x:bosqueTerm{isList ty x} -> Tot nat
let m_length p ty x = match x with 
| BList _ l -> (lengthList l) - (lengthList (filterList p l))
