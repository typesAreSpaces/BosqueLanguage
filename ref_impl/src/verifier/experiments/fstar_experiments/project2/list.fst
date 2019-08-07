module List

type list 'a : Type = 
| LNil : list 'a
| LCons : hd : 'a -> tl : list 'a -> list 'a

val lengthList : #a : Type -> (l : list a) -> nat
let rec lengthList #a l = match l with
| LNil -> 0
| LCons hd tl -> 1 + lengthList tl

assume val setList : #a : Type -> idx : int -> v : a -> list a

val anyList : #a : Type -> (l : list a) -> (p:(a -> bool)) -> b:bool{}
let rec anyList #a l p = match l with
| LNil -> false 
| LCons hd tl -> (match (p hd) with
                | true -> true
                | false -> anyList tl p
                )

// This one is wrong
val findIndexList : #a : Type -> (l : list a) -> (p:(a -> bool)) -> b:bool
let rec findIndexList #a l p = match l with
| LNil -> false 
| LCons hd tl -> (match (p hd) with
                | true -> true
                | false -> anyList tl p
                )

// val lemma_anyList : #a:Type -> (l : list a) -> (p : (a -> bool)) -> Lemma (requires (p l)) (ensures )
// let rec lemma_anyList #a l p = admit()

val filterList : #a : Type -> (l : list a) -> (p : (a -> bool)) -> l2:list a
let rec filterList #a l p = match l with
| LNil -> LNil
| LCons hd tl -> (match (p hd) with
                | true -> LCons hd (filterList tl p)
                | false -> filterList tl p
                )

assume val uniformList : #a : Type -> (l : list a) -> (rnd : int) -> a

val atList : #a : Type -> (l : list a{lengthList l > 0}) -> (idx : nat{idx < lengthList l}) -> a
let rec atList #a l idx = match l with
| LCons hd tl -> (match idx with 
                | 0 -> hd
                | _ -> atList tl (idx - 1)
                )
