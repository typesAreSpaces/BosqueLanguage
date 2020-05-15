module Util

val max : nat -> nat -> nat
let max x y = if (x > y) then x else y

val min : nat -> nat -> nat
let min x y = if (x > y) then y else x

assume val cast (t1 : Type) (t2 : Type) (a : t1) : t2
