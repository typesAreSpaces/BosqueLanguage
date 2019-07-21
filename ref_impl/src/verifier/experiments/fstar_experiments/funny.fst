module Funny

open FStar.All

val im_about_to_end_this_mans_whole_carrer : int -> int
let im_about_to_end_this_mans_whole_carrer = fun n -> n

// fails 
// let _ = assert (exists x . im_about_to_end_this_mans_whole_carrer x = x)

val mmm : int -> int
let mmm n = n

// also fails
// let _ = assert (exists x . mmm x = x)

let _ = assert (~( ~ (forall x . not (mmm x <> x))))
let _ = assert (~(forall x . (mmm x <> x)))

// My confusion might be between prims.logical and prims.bool
// interaction. However, the first assertion should be provable, right?




