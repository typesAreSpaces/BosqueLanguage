module Vector_example

type vector 'a : nat -> Type =
  | VNil : vector 'a 0
  | VCons : hd:'a
         -> #n:nat
         -> tl:vector 'a n
         -> vector 'a (n + 1)

val head: #a:Type -> #n:pos -> vector a n -> Tot a
let head #a #n v = match v with
  | VCons x xs -> x

val nth : n:nat -> #m:nat{m > n} -> vector 'a m -> Tot 'a
let rec nth n #m (VCons x #m' xs) =
  if n = 0
  then x
  else nth (n-1) #m' xs

val append: #a:Type -> #n1:nat -> #n2:nat -> l:vector a n1 -> vector a n2 ->  Tot (vector a (n1 + n2)) //implicit n1 decreases
let rec append #a #n1 #n2 v1 v2 =
  match v1 with
    | VNil -> v2
    | VCons hd tl -> VCons hd (append tl v2)

val reverse: #a:Type -> #n:nat -> vector a n -> Tot (vector a n) //the implicitly computed n decreases
let rec reverse #a #n v = match v with
  | VNil -> VNil
  | VCons hd tl -> append (reverse tl) (VCons hd VNil)

val mapT: ('a -> Tot 'b) -> #n:nat -> vector 'a n -> Tot (vector 'b n)
let rec mapT f #n v = match v with
  | VNil -> VNil
  | VCons hd tl -> VCons (f hd) (mapT f tl)

val fold_left: ('b -> 'a -> Tot 'b) -> 'b -> #n:nat -> vector 'a n -> Tot 'b (decreases n)
let rec fold_left f acc #n v = match v with
  | VNil -> acc
  | VCons hd tl -> fold_left f (f acc hd) tl

val fold_right: ('a -> 'b -> Tot 'b) -> #n:nat -> vector 'a n -> 'b -> Tot 'b
let rec fold_right f #n v acc = match v with
  | VNil -> acc
  | VCons hd tl -> f hd (fold_right f tl acc)

val find: f:('a -> Tot bool) -> #n:nat -> vector 'a n -> Tot (option (x:'a{f x}))
let rec find f #n v = match v with
  | VNil -> None
  | VCons hd tl ->
    if f hd
    then Some hd
    else find f tl

val zip': #a:Type -> #b:Type -> #n:nat -> vector a n -> vector b n -> Tot (vector (a * b) n)
let rec zip' #a #b #n v1 v2 = match v1 with
  | VNil -> VNil
  | VCons a tl1 ->
    let VCons b tl2 = v2 in
    VCons (a, b) (zip' tl1 tl2)


val add_vector : #n:nat -> vector int n -> vector int n -> Tot (vector int n)
let rec add_vector #n x y = match x with 
| VNil -> VNil
| VCons hd1 tl1 -> 
  let VCons hd2 tl2 = y in
  VCons (hd1 + hd2) (add_vector tl1 tl2)

// val add_vector : n:nat -> vector int n -> vector int n -> Tot (vector int n)
// let rec add_vector #n x y = match x, y with 
// | 0, VNil, VNil -> VNil
// | n, (VCons hd1 tl1), (VCons hd2 tl2) -> VCons (hd1 + hd2) (add_vector tl1 tl2)

let test1 = VCons 3 (VCons 45 VNil)
let test2 = VCons 98 (VCons 83 VNil)
let test3 = VCons 98 (VCons 83 (VCons 34 VNil))
let add_test = add_vector test1 test2
// let add_test_2 = add_vector test1 test3