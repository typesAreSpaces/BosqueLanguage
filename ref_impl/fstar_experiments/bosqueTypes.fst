module BosqueTypes


// ---------------------
// Bosque Concepts------
type bosque__Any       = 
type bosque__Some      = 
type bosque__Truthy    = 
type bosque__Parseable = 
// ---------------------

type bosque__None = | Bosque__None

type bosque__Union__Int_Bool : Type -> Type = 
| Bosque__Int  : int -> bosque__Union__Int_Bool int  
| Bosque__Bool : bool -> bosque__Union__Int_Bool bool  

val bosque__subtype : t1:Type0 -> t2:Type0 -> Tot bool
let bosque__subtype x y = 
match x with 
| bosque__Any -> true
| bosque_Some -> true
| bosque__Truthy ->
  match y with
  | bosque__None -> true
  | _ -> false 
| _ -> false 
type triple = {fst : int; snd : int; third : int;}
// val f : ({fst : int; snd : int; third : int;}) -> Tot int
val f : triple -> Tot int
let f = fun x -> x.fst + x.third

type ttriple = int * int
val g : ttriple -> ttriple 
