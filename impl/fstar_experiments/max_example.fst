module Max_example

val max : int -> int -> Tot int
let max x y = if (x >= y) then x else y


val max_tuple : int * int -> Tot int
let max_tuple (y, z) = max y z

type record_int = {x : int; y : int}

val max_record : record_int -> Tot int
let max_record ({x  = _x; y = _y}) = max _x _y

let _ = assert (forall x y . max x y >= x && max x y >= y && (max x y = x || max x y = y))

let _ = assert (forall x y . max_tuple (x, y) >= x && max_tuple (x, y) >= y && (max_tuple (x, y) = x || max_tuple (x, y) = y))

let _ = assert (forall x y . max_record ({x = x; y = y}) >= x && max_record ({x = x; y = y}) >= y && (max_record ({x = x; y = y}) = x || max_record ({x = x; y = y}) = y))

