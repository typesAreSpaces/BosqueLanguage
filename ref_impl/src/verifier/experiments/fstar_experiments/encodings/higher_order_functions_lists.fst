module Higher_order_functions_lists
open BosqueOption

val append : l1 : list 'a -> l2 : list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with 
| [] -> l2
| hd :: tl -> hd :: append tl l2

(* Lemma: append is an associative operation *) 
val append_assoc : l1 : list 'a -> l2 : list 'a -> l3 : list 'a -> Lemma (append l1 (append l2 l3) == append (append l1 l2) l3)
let rec append_assoc l1 l2 l3 = match l1 with 
| [] -> ()
| _ :: tl -> append_assoc tl l2 l3


let rec reverse = function
| [] -> []
| hd :: tl -> append (reverse tl) [hd]

let rec find f l = match l with
| [] -> BosqueNone 
| hd :: tl -> if f hd then BosqueSome hd else find f tl

val fold_left : f : ('a -> 'b -> 'b) -> l : list 'a -> (x : 'b) -> Tot 'b
let rec fold_left f l x = match l with 
| [] -> x
| hd::tl -> fold_left f tl (f hd x)

(* Lemma: fold_left with cons reverses back a list  *)
val fold_left_cons_is_reverse : l : list 'a -> l' : list 'a -> Lemma (fold_left Cons l l' == append (reverse l) l') 
let rec fold_left_cons_is_reverse l1 l = match l1 with 
| [] -> ()
| x :: xs -> 
append_assoc (reverse xs) ([x]) l; 
fold_left_cons_is_reverse xs (x :: l)

let rec map f l = match l with
| [] -> []
| hd :: tl -> f hd :: map f tl

val length : list 'a -> Tot nat
let rec length = function 
| [] -> 0
| _ :: xs -> 1 + length xs

(* Lemma: map preserves the length of a list *)
val lemma_length_map : f : ('a -> 'b) -> l : list 'a -> Lemma (length (map f l) == length l)
let rec lemma_length_map f = function 
| [] -> ()
| x :: xs -> lemma_length_map f xs

(*-------------------------------------------- findByIndex --------------------------------------------*)
val findByIndex : x : int -> l : list 'a -> bosqueOption 'a
let rec findByIndex x l = if (x < 0) then BosqueError else match x with 
| 0 -> (match l with 
      | [] -> BosqueNone
      | x :: _ -> BosqueSome x
      )
| n -> (match l with 
      | [] -> BosqueNone
      | _ :: xs  -> findByIndex (n - 1) xs
      )
(*-------------------------------------------- findByIndex --------------------------------------------*)

val lemma_map_index_case_BosqueError : index:int
-> f : ('a -> 'b) 
-> l : list 'a 
-> Lemma (requires findByIndex index l == BosqueError) (ensures (findByIndex index (map f l) == BosqueError))
let rec lemma_map_index_case_BosqueError index f l = 
  if (index < 0) then ()
  else match index with
       | 0 -> ()
       | n -> match l with 
             | [] -> ()
             | _ :: tl -> lemma_map_index_case_BosqueError (index - 1) f tl

val lemma_map_index_case_BosqueNone : index:int
-> f : ('a -> 'b) 
-> l : list 'a 
-> Lemma (requires findByIndex index l == BosqueNone) (ensures (findByIndex index (map f l) == BosqueNone))
let rec lemma_map_index_case_BosqueNone index f l = 
  if (index < 0) then ()
  else match index with
       | 0 -> ()
       | n -> match l with 
             | [] -> ()
             | _ :: tl -> lemma_map_index_case_BosqueNone (index - 1) f tl

val lemma_map_index_case_BosqueSome : index:nat 
-> output : 'a 
-> f : ('a -> 'b) 
-> l : list 'a 
-> Lemma (requires findByIndex index l == BosqueSome output) (ensures (findByIndex index (map f l) == BosqueSome (f output)))
let rec lemma_map_index_case_BosqueSome index output f l = 
  if (index < 0) then () 
  else match index with 
       | 0 -> ()
       | n -> match l with 
             | [] -> ()
             | _ :: tl -> lemma_map_index_case_BosqueSome (index - 1) output f tl

val lemma_map_index : index:int 
-> f : ('a -> 'b) 
-> l : list 'a -> Lemma (ensures (findByIndex index (map f l) == (lift_bosqueOption f) (findByIndex index l)))

let lemma_map_index index f l = match (findByIndex index l) with 
| BosqueError -> lemma_map_index_case_BosqueError index f l
| BosqueNone -> lemma_map_index_case_BosqueNone index f l
| BosqueSome v -> lemma_map_index_case_BosqueSome index v f l

(*-------------------------------------------- example --------------------------------------------*)
val f : x:int -> f : (int -> int) -> Tot int
let f x f =  lemma_map_index x f [1;2;3]; x + 1

val f3 : int -> Tot int
let f3 x = lemma_map_index x (function x -> x + 1) ([1; 2]); x + 1

let ahh = f3 1

let _ = assert (forall l (y : int) . length #(a:Type) (map (function x -> x) l) >= 0)
(*-------------------------------------------- example --------------------------------------------*)
