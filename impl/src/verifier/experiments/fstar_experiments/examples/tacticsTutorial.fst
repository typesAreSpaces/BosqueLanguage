module TacticsTutorial

open FStar.Tactics
open FStar.List
  
val ex1 : unit -> Lemma True
let ex1 () = assert_by_tactic True idtac

  
  

let tau3 () : Tac unit = 
  Tactics.split ();
  dump "After split";
  smt ()
  

let ex3 (x: nat) = 
  assert_by_tactic (x + x >= 0 /\ List.length [4;5;1] == 3) tau3
