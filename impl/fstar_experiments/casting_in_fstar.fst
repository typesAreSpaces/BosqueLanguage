module A

open FStar.Integers

let ex12 (x:int_32{cast_ok (Unsigned W32) x}) (y : uint_32{ok (+) (cast x) y}) = cast x + y

