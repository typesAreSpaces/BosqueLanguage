module ProvingEquivalence


val isZero : n:nat -> Tot bool
let rec isZero x = if (x = 0) then true else false

val f : n:nat{isZero n} -> n:nat{n=1}
let f x = x + 1

val isZero2 : n:nat -> Tot bool
let rec isZero2 x = if (x = 0) then true else if (x = 1) then false else isZero2 (x - 1)

val lemmaIsZeroEquiv : n:nat -> Lemma (ensures (isZero n) = (isZero2 n))
let rec lemmaIsZeroEquiv n = if (n = 0) then () else lemmaIsZeroEquiv (n - 1)

val f2 : n:nat{isZero n} -> n:nat{n=1}
let f2 x = lemmaIsZeroEquiv x; x + 1
