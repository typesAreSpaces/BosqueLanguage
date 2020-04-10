module BosqueCollections  

// Contains an axiomatization of 
// the Bosque collection library

open BosqueTerms
open List 

// assume AxiomLengthAppend1 : 
assume AxiomEmpty1 : 
forall (x : list bosqueTerm) . {:pattern (emptyList x)} (emptyList x) = (x = LNil)

assume AxiomEmpty2 : 
forall (x : list bosqueTerm) . {:pattern (x = LNil)} (emptyList x) = (x = LNil)

// forall (x y : list bosqueTerm) . {:pattern (appendList x y)} lengthList x + lengthList y = lengthList (appendList x y) 

// assume AxiomLengthAppend2 : 
// forall (x y : list bosqueTerm) . {:pattern (lengthList x); (lengthList y)} lengthList x + lengthList y = lengthList (appendList x y) 

// assume AxiomLengthFilter : 
// forall (p : bosqueTerm -> bool) (x : list bosqueTerm) . 
  // {:pattern (filterList x p)} 
  // lengthList x >= lengthList (filterList x p)

// assume AxiomLengthFilter :
// forall (p : bosqueTerm -> bool) (x : list bosqueTerm) . 
  // {:pattern (filterList x p)} 
  // lengthList x >= lengthList (filterList x p)

// assume AxiomFilterAppend : 
// forall (p : bosqueTerm -> bool) (x y : list bosqueTerm) . 
//   {:pattern (filterList (appendList x y))} 
//   appendList (filterList x p) (filterList y p) == filterList (appendList x y) p 

let x = LCons (BInt 2) LNil
let _ = assert_norm (not (emptyList x))
let _ = assert_norm (not (x = LNil))