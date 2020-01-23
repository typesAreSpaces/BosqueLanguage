module List

open FStar.Ghost

type list 'a : Type = 
| LNil : list 'a
| LCons : hd:'a -> tl : list 'a -> list 'a

val mapList : (#a:Type) -> (#b:Type)
  -> (a -> Tot b) -> (list a) 
  -> Tot (list b)
let rec mapList #a #b f l = match l with
| LNil ->  LNil
| LCons hd tl -> LCons (f hd) (mapList f tl)

val mapList' : (#a:Type) -> (#b:Type)
  -> (x:erased a) -> ((x':a{x' << reveal x}) -> Tot b) -> (y : list a { y << reveal x}) 
  -> Tot (list b)
let rec mapList' #a #b x f l = match l with
| LNil -> LNil
| LCons hd tl -> LCons (f hd) (mapList' x f tl)

val fold_leftList : #a:Type -> #b:Type -> (a -> b -> Tot b) -> (list a) -> b -> Tot b
let rec fold_leftList #a #b f l x = match l with 
| LNil -> x
| LCons hd tl -> f hd (fold_leftList f tl x)

val zipList : #a:Type -> #b:Type -> list a -> list b -> Tot (list (a * b))
let rec zipList #a #b v1 v2 = match v1 with
| LNil -> LNil
| LCons a tl1 -> match v2 with
  | LNil -> LNil
  | LCons b tl2 -> LCons (a, b) (zipList tl1 tl2)


val zipList': #a:Type -> #b:Type
  -> (x:erased a)
  -> (y:list a {y << reveal x}) -> (z:list b {z << reveal x}) -> Tot (list (a * b))
let rec zipList' #a #b x v1 v2 = match v1 with
| LNil -> LNil
| LCons a tl1 -> match v2 with
  | LNil -> LNil
  | LCons b tl2 -> LCons (a, b) (zipList' x tl1 tl2)

val takeList : #a:Type -> m:nat -> list a -> list a
let rec takeList #a m x = match x with
| LNil -> LNil
| LCons hd tl -> 
  if (m = 0) then LNil 
  else LCons hd (takeList (m - 1) tl)


