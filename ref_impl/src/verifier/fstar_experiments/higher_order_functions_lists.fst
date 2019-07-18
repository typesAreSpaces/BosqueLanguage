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

let rec map f l = match l with
| [] -> []
| hd :: tl -> f hd :: map f tl

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

