module Test_axiomatization

open List
open BosqueTypes
open BosqueTerms 

// Comment either one or the other
// of the following lines

// open BosqueCollections

assume AxiomLengthFilter :
forall (p : bosqueTerm -> bool) (x : list bosqueTerm) . 
  {:pattern (filterList x p)} 
  lengthList x >= lengthList (filterList x p)

val m_length : (p : bosqueTerm -> bool) -> ty:bosqueType -> x:bosqueTerm{isList ty x} -> Tot nat
let m_length p ty x = match x with 
| BList _ l -> (lengthList l) - (lengthList (filterList l p))
