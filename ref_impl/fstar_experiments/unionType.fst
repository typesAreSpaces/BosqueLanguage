module UnionType  

open FStar.All

type intUnionBool 'a = x:'a{x:int \/ x:bool}

val test : intUnionBool 'a -> int
let test n = if (n == true) then 1 else if (n == false) then 2 else n
