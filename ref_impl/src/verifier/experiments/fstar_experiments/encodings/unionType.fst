module UnionType  

open BosqueOption

(* First approach: Doesn't keep track of the types involved in the union type *)
// type union_IntBool = 
// | InjectIntfromUnionIntBool : x:int -> unionIntBool
// | InjectIntfromUnionIntBool : x:bool -> unionIntBool

(* Second approach: Solves previous issue *)
type union_IntBool : Type -> Type -> Type = 
| InjectIntfromUnionIntBool : x : int -> union_IntBool int bool
| InjectBoolfromUnionIntBool : x : bool -> union_IntBool int bool

val projectIntfromUnionIntBool : (union_IntBool int bool) -> bosqueOption int
let projectIntfromUnionIntBool x = match x with 
| InjectIntfromUnionIntBool x -> BosqueSome x
| _ -> BosqueNone

val projectBoolfromUnionIntBool : (union_IntBool int bool) -> bosqueOption bool
let projectBoolfromUnionIntBool x = match x with 
| InjectBoolfromUnionIntBool x -> BosqueSome x
| _ -> BosqueNone

(* Test *)
let var1 = InjectIntfromUnionIntBool 3423
let var2 = InjectBoolfromUnionIntBool true
let test1 = projectIntfromUnionIntBool var1
let test2 = projectBoolfromUnionIntBool var1
