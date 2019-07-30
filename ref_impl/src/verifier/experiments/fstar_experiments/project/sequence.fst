module Sequence

open FStar.Ghost

type sequence 'a : nat -> Type = 
| SNil : sequence 'a 0
| SCons : hd:'a -> #n:nat -> tl : sequence 'a n -> sequence 'a (n + 1) 

val mapSequence : (#a:Type) -> (#b:Type) -> (#n:nat) 
  -> (a -> Tot b) -> (sequence a n) 
  -> Tot (sequence b n)
let rec mapSequence #a #b #n f seq = match seq with
| SNil -> SNil
| SCons hd tl -> SCons (f hd) (mapSequence f tl)

val mapSequence' : (#a:Type) -> (#b:Type) -> (#n:nat) 
  -> (x:erased a) -> ((x':a{x' << reveal x}) -> Tot b) -> (y : sequence a n{ y << reveal x}) 
  -> Tot (sequence b n)
let rec mapSequence' #a #b #n x f seq = match seq with
| SNil -> SNil
| SCons hd tl -> SCons (f hd) (mapSequence' x f tl)

val fold_leftSequence : #a:Type -> #b:Type -> #n:nat -> (a -> b -> Tot b) -> (sequence a n) -> b -> Tot b
let rec fold_leftSequence #a #b #n f l x = match l with 
| SNil -> x
| SCons hd tl -> f hd (fold_leftSequence f tl x)

val zipSequence : #a:Type -> #b:Type -> #n:nat -> sequence a n -> sequence b n -> Tot (sequence (a * b) n)
let rec zipSequence #a #b #n v1 v2 = match v1 with
  | SNil -> SNil
  | SCons a tl1 ->
    let SCons b tl2 = v2 in
    SCons (a, b) (zipSequence tl1 tl2)

val zipSequence': #a:Type -> #b:Type -> #n:nat 
  -> (x:erased a)
  -> (y:sequence a n{y << reveal x}) -> (z:sequence b n{z << reveal x}) -> Tot (sequence (a * b) n)
let rec zipSequence' #a #b #n x v1 v2 = match v1 with
  | SNil -> SNil
  | SCons a tl1 ->
    let SCons b tl2 = v2 in
    SCons (a, b) (zipSequence' x tl1 tl2)
