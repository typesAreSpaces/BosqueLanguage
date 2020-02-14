module BosqueCollections 

// Contains the axiomatization of 
// the collections used in Bosque

open BosqueTerms
open List 

assume AxiomLengthAppend : 
forall (x y : list bosqueTerm) . {:pattern (appendList x y)} lengthList x + lengthList y = lengthList (appendList x y)

assume AxiomLengthFilter : 
forall (p : bosqueTerm -> bool) (x : list bosqueTerm) . 
  {:pattern (filterList x p)} 
  lengthList x >= lengthList (filterList x p)

assume AxiomLengthFilter :
forall (p : bosqueTerm -> bool) (x : list bosqueTerm) . 
  {:pattern (filterList x p)} 
  lengthList x >= lengthList (filterList x p)

assume AxiomFilterAppend : 
forall (p : bosqueTerm -> bool) (x y : list bosqueTerm) . 
  {:pattern (filterList (appendList x y))} 
  appendList (filterList x p) (filterList y p) == filterList (appendList x y) p
