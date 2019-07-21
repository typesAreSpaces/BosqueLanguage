module Nik_comment

//This is an unusual encoding of a tagged type
//you'd be better off just using `either a b`
type cases a b : Type u#1 = 
  (t:Type u#0 & 
     x:t &
        either (squash (t == a)) (squash (t == b)))

let elim_cases (#a #b #c:Type u#0) (x:cases a b) (f:a -> c) (g:b -> c) =
  let (| _, v, p |) = x in match p with
      | Inl _ -> f v
        | Inr _ -> g v

let branch0 (x:bool) : cases int string =
  if x then (| int, 0, Inl () |)
    else (| string, "hello", Inr () |)

let branch1 (x:bool) : either int string =
  if x then Inl 0
    else Inr "hello"

//here's another way of doing it with dependent types
let branch2 (x:bool)  : (if x then int else string) =
  if x then 0 else "hello"


let f (x : bool) : int = if x then 0 else 1

let g (x : either int bool) : int = 
  match x with 
  | Inl i -> i
  | _ -> 0
