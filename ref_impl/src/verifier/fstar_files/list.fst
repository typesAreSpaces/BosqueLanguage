module List

open FStar.Ghost

type list 'a : Type = 
| LNil : list 'a
| LCons : hd:'a -> tl : list 'a -> list 'a

// val mapList : (#a:Type) -> (#b:Type)
//   -> (a -> Tot b) -> (list a) 
//   -> Tot (list b)
// let rec mapList #a #b f seq = match seq with
// | LNil -> LNil
// | LCons hd tl -> LCons (f hd) (mapList f tl)

val fold_leftList : #a:Type -> #b:Type -> (a -> b -> Tot b) -> (list a) -> b -> Tot b
let rec fold_leftList #a #b f l x = match l with 
| LNil -> x
| LCons hd tl -> f hd (fold_leftList f tl x)

val zipList : #a:Type -> #b:Type -> list a -> list b -> Tot (list (a * b))
let rec zipList #a #b v1 v2 = match v1 with
| LNil -> LNil
| LCons a tl1 -> match v2 with 
  | LNil -> LNil
  | LCons b tl2 ->  LCons (a, b) (zipList tl1 tl2)

val takeList : #a:Type ->  m:nat -> list a -> Tot (list a)
let rec takeList #a m x = match x with
| LNil -> LNil
| LCons hd tl -> 
  if (m = 0) then LNil 
  else LCons hd (takeList (m - 1) tl)

val appendList : list 'a -> list 'a -> Tot (list 'a)
let rec appendList x y = match x with
| LNil -> y
| LCons hd tl -> LCons hd (appendList tl y) 

// val filterList : ('a -> bool) -> list 'a -> Tot (list 'a)
// let rec filterList p x = match x with
// | LNil -> LNil
// | LCons hd tl -> if (p hd) then LCons (hd) (filterList p tl) else (filterList p tl)

// -------------------------------------------------------------------------------------

val lengthList : list 'a -> Tot nat
let rec lengthList x = match x with
| LNil -> 0
| LCons _ tl -> 1 + lengthList tl

val atList : l:list 'a -> n:nat {n < lengthList l} -> Tot 'a
let rec atList xs pos = match pos with
| 0 -> (match xs with
      | LCons hd _ -> hd
      )
| _ -> (match xs with
      | LCons _ tl -> atList tl (pos - 1)
      )

val existsList' : l:list 'a -> n:nat -> ('a -> bool) -> Tot bool (decreases (lengthList l-n))
let rec existsList' xs pos p = 
  if (pos >= lengthList xs) then false 
  else 
    let v = atList xs pos in 
    if (p v) then true
    else existsList' xs (pos + 1) p

val allList' : l:list 'a -> n:nat -> ('a -> bool) -> Tot bool (decreases (lengthList l-n))
let rec allList' xs pos p = 
  if (pos >= lengthList xs) then true
  else 
    let v = atList xs pos in 
    if (not (p v)) then false
    else allList' xs (pos + 1) p

val filterList' : l1:list 'a -> n:nat -> l2:list 'a -> ('a -> bool) -> Tot (list 'a) (decreases (lengthList l1 - n))
let rec filterList' xs1 pos xs2 p = 
  if (pos >= lengthList xs1) then xs2
  else
    let v = atList xs1 pos in
    if (p v) then filterList' xs1 (pos + 1) (appendList xs2 (LCons v LNil)) p
    else filterList' xs1 (pos + 1) xs2 p

val mapList' : l1:list 'a -> n:nat -> l2:list 'b -> ('a -> 'b) -> Tot (list 'b) (decreases (lengthList l1 - n))
let rec mapList' l1 pos l2 f = 
  if (pos >= lengthList l1) then l2
  else 
    let v = atList l1 pos in 
    mapList' l1 (pos + 1) (appendList l2 (LCons (f v) LNil)) f 

val emptyList : list 'a -> Tot(bool)
let emptyList l = lengthList l = 0

val pushList : list 'a -> 'a -> Tot (list 'a)
let pushList l element = appendList l (LCons element LNil)

val setList : l:list 'a -> n:nat {n < lengthList l} -> 'a -> Tot (list 'a)
let rec setList xs pos elem = match pos with 
| 0 -> (match xs with
      | LCons _ tl -> LCons elem tl
      )
| _ -> (match xs with
      | LCons hd tl -> LCons hd (setList tl (pos - 1) elem)
      ) 

val existsList : list 'a -> ('a -> bool) -> Tot bool
let existsList l p = existsList' l 0 p

val allList : list 'a -> ('a -> bool) -> Tot bool
let allList l p = allList' l 0 p

val filterList : list 'a -> ('a -> bool) -> Tot (list 'a)
let filterList l p = filterList' l 0 LNil p

val mapList : list 'a -> ('a -> 'b) -> Tot (list 'b)
let mapList l f = mapList' l 0 LNil f
