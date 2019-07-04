module Max_example

val max : int -> int -> Tot int
let max x y = if (x >= y) then x else y

type tuple_int = int * int

val max_tuple : tuple_int -> Tot int
let max_tuple x = match x with 
| y, z -> max y z

let _ = assert (forall x y . max x y >= x && max x y >= y && (max x y = x || max x y = y))

let _ = assert (forall x y . max_tuple (x, y) >= x && max_tuple (x, y) >= y && (max_tuple (x, y) = x || max_tuple (x, y) = y))

