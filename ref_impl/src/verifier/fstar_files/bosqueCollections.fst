module BosqueCollections  

// Contains an axiomatization of 
// the Bosque collection library

open BosqueTerms
open List 
// Signature
assume val local_empty : list bosqueTerm -> Tot bool
assume val local_size : list bosqueTerm -> Tot int
assume val local_at: list bosqueTerm -> int -> Tot bosqueTerm
assume val local_push: list bosqueTerm -> bosqueTerm -> Tot (list bosqueTerm)
assume val local_set: list bosqueTerm -> bosqueTerm -> Tot (list bosqueTerm)

// Axioms
assume AxiomEmpty1 : 
forall (x : list bosqueTerm) . 
  {:pattern (local_empty x)} 
  (local_empty x) = (x = LNil)

assume AxiomEmpty2 : 
forall (x : list bosqueTerm) . 
  {:pattern (x = LNil)} 
  (local_empty x) = (x = LNil)

assume AxiomSize1 : 
forall (x : list bosqueTerm) . 
  {:pattern (local_size x)} 
  local_size x >= 0

assume AxiomSize2 : 
forall (x : list bosqueTerm) . 
  {:pattern (local_size x)}
  (x = LNil) = (local_size x = 0) 

assume AxiomsSize3 : 
forall (

assume AxiomPush : // Check patterns here
forall (la la' : list bosqueTerm) (x : bosqueTerm) . 
  {:pattern (local_push la x) ; (local_size la')} 
  (la' = local_push la x) ==> (local_size la' = local_size la + 1)

// Tests
let y = LCons (BInt 2) LNil
let _ = assert_norm (not (local_empty y))
let _ = assert_norm (not (y = LNil))
let _ = assert_norm ( not ( local_size y = (- 5) ) )

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

