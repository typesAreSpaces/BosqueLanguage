module List

open FStar.Ghost

type list 'a : Type = 
| SNil : sequence 'a
| SCons : hd:'a -> tl : list 'a -> list 'a
