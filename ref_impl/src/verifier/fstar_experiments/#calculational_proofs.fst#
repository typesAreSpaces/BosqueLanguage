module Calculational_proofs

open FStar.Calc

let lem1 (a : pos) : Lemma (op_Multiply 2 a > a) = ()

let calc0 (a : pos) : Lemma (a + a > a) = 
calc (>) {
a + a;
== {}
op_Multiply 2 a;
> {lem1 a}
a;

}
