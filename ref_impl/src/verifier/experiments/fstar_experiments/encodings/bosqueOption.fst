module BosqueOption

type bosqueOption (a : Type) = 
| BosqueError : bosqueOption a
| BosqueNone : bosqueOption a
| BosqueSome : v:a -> bosqueOption a

let lift_bosqueOption (f : ('a -> 'b)) : (bosqueOption 'a -> bosqueOption 'b) = function n -> match n with 
| BosqueError -> BosqueError
| BosqueNone -> BosqueNone 
| BosqueSome v -> BosqueSome (f v)