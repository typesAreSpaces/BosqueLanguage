module Higher_order_functions_lists

val append : l1 : list 'a -> l2 : list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with 
| [] -> l2
| hd :: tl -> hd :: append tl l2

val cons_append : x : 'a -> xs : list 'a -> Lemma (append [x] xs == x :: xs)
let rec cons_append x y = match y with 
| [] -> ()
| _ :: tl -> cons_append x tl

val append_assoc : l1 : list 'a -> l2 : list 'a -> l3 : list 'a -> Lemma (append l1 (append l2 l3) == append (append l1 l2) l3)
let rec append_assoc l1 l2 l3 = match l1 with 
| [] -> ()
| _ :: tl -> append_assoc tl l2 l3

let rec reverse = function
| [] -> []
| hd :: tl -> append (reverse tl) [hd]

type option 'a = 
| None : option 'a
| Some : v : 'a -> option 'a

let rec find f l = match l with
| [] -> None
| hd :: tl -> if f hd then Some hd else find f tl

val lemma1 : x : 'a -> f : ('a -> bool) -> l : list 'a -> Lemma
  (requires (find f l == Some x)) 
  (ensures (f x == true))
 
let rec lemma1 x f l = match l with 
| [] -> ()
| hd :: tl -> match (f hd) with 
  | true -> ()
  | false -> lemma1 x f tl

val fold_left : f : ('a -> 'b -> 'b) -> l : list 'a -> (x : 'b) -> Tot 'b
let rec fold_left f l x = match l with 
| [] -> x
| hd::tl -> fold_left f tl (f hd x)

val fold_left_cons_is_reverse : l : list 'a -> l' : list 'a -> Lemma (fold_left Cons l l' == append (reverse l) l') 
let rec fold_left_cons_is_reverse l1 l = match l1 with 
| [] -> ()
| x :: xs -> 
append_assoc (reverse xs) ([x]) l; 
fold_left_cons_is_reverse xs (x :: l)

(**------------------------------------------ mapPreservesLength ------------------------------------------**)

let rec map f l = match l with
| [] -> []
| hd :: tl -> f hd :: map f tl

val length : list 'a -> Tot nat
let rec length = function 
| [] -> 0
| _ :: xs -> 1 + length xs

val lemma_length_map : f : ('a -> 'b) -> l : list 'a -> Lemma (length (map f l) == length l)
let rec lemma_length_map f = function 
| [] -> ()
| x :: xs -> lemma_length_map f xs

(**------------------------------------------ mapPreservesLength ------------------------------------------**)

(**-------------------------------------------- findByIndex --------------------------------------------**)

val findByIndex : x : int -> l : list 'a -> option 'a
let rec findByIndex x l = if (x < 0) then None else match x with 
| 0 -> (match l with 
      | [] -> None
      | x :: _ -> Some x
      )
| n -> (match l with 
      | [] -> None
      | _ :: xs  -> findByIndex (n - 1) xs
      )

val lemma_map_index_case_Some : index:nat 
-> output : 'a 
-> f : ('a -> 'b) 
-> l : list 'a 
-> Lemma (requires findByIndex index l == Some output) (ensures (findByIndex index (map f l) == Some (f output)))

let rec lemma_map_index_case_Some index output f l = 
  if (index < 0) then () 
  else match index with 
       | 0 -> ()
       | n -> match l with 
             | [] -> ()
             | _ :: tl -> lemma_map_index_case_Some (index - 1) output f tl

val lemma_map_index_case_None : index:int
-> f : ('a -> 'b) 
-> l : list 'a 
-> Lemma (requires findByIndex index l == None) (ensures (findByIndex index (map f l) == None))

let rec lemma_map_index_case_None index f l = 
  if (index < 0) then ()
  else match index with
       | 0 -> ()
       | n -> match l with 
             | [] -> ()
             | _ :: tl -> lemma_map_index_case_None (index - 1) f tl

let lift_option_function (f : ('a -> 'b)) : (option 'a -> option 'b) = function n -> match n with 
| None -> None 
| Some v -> Some (f v)

val lemma_map_index : index:int 
-> f : ('a -> 'b) 
-> l : list 'a 
-> Lemma (ensures (findByIndex index (map f l) == (lift_option_function f) (findByIndex index l)))

let rec lemma_map_index index f l = match (findByIndex index l) with 
| None -> lemma_map_index_case_None index f l
| Some v -> lemma_map_index_case_Some index v f l

(**-------------------------------------------- findByIndex --------------------------------------------**)

val f : x:int -> f : (int -> int) -> Tot int
let f x f =  lemma_map_index x f [1;2;3]; x + 1

val f3 : int -> Tot int
let f3 x = lemma_map_index x (function x -> x + 1) ([1; 2]); x + 1

let ahh = f3 1

let _ = assert (forall l (y : int) . length #(a:Type) (map (function x -> x) l) >= 0)

