module NSMain__main_main
open BosqueOption

type union__bool0int0singletonBosqueNone: Type -> Type -> Type ->Type =
| Injectboolfrombool0int0singletonBosqueNone: x : bool -> union__bool0int0singletonBosqueNone bool int singletonBosqueNone
| Injectintfrombool0int0singletonBosqueNone: x : int -> union__bool0int0singletonBosqueNone bool int singletonBosqueNone
| InjectsingletonBosqueNonefrombool0int0singletonBosqueNone: x : singletonBosqueNone -> union__bool0int0singletonBosqueNone bool int singletonBosqueNone

val projectboolfrombool0int0singletonBosqueNone : (union__bool0int0singletonBosqueNone bool int singletonBosqueNone) -> bosqueOption bool
let projectboolfrombool0int0singletonBosqueNone x = match x with
| Injectboolfrombool0int0singletonBosqueNone x -> BosqueSome x
| _ -> BosqueNone

val projectintfrombool0int0singletonBosqueNone : (union__bool0int0singletonBosqueNone bool int singletonBosqueNone) -> bosqueOption int
let projectintfrombool0int0singletonBosqueNone x = match x with
| Injectintfrombool0int0singletonBosqueNone x -> BosqueSome x
| _ -> BosqueNone

val projectsingletonBosqueNonefrombool0int0singletonBosqueNone : (union__bool0int0singletonBosqueNone bool int singletonBosqueNone) -> bosqueOption singletonBosqueNone
let projectsingletonBosqueNonefrombool0int0singletonBosqueNone x = match x with
| InjectsingletonBosqueNonefrombool0int0singletonBosqueNone x -> BosqueSome x
| _ -> BosqueNone

type union__int0singletonBosqueNone: Type -> Type ->Type =
| Injectintfromint0singletonBosqueNone: x : int -> union__int0singletonBosqueNone int singletonBosqueNone
| InjectsingletonBosqueNonefromint0singletonBosqueNone: x : singletonBosqueNone -> union__int0singletonBosqueNone int singletonBosqueNone

val projectintfromint0singletonBosqueNone : (union__int0singletonBosqueNone int singletonBosqueNone) -> bosqueOption int
let projectintfromint0singletonBosqueNone x = match x with
| Injectintfromint0singletonBosqueNone x -> BosqueSome x
| _ -> BosqueNone

val projectsingletonBosqueNonefromint0singletonBosqueNone : (union__int0singletonBosqueNone int singletonBosqueNone) -> bosqueOption singletonBosqueNone
let projectsingletonBosqueNonefromint0singletonBosqueNone x = match x with
| InjectsingletonBosqueNonefromint0singletonBosqueNone x -> BosqueSome x
| _ -> BosqueNone

type tuple__2 (t_1 : Type) (t_2 : Type) =
| Mktuple__2: _1:t_1 -> _2:t_2 -> tuple__2 t_1 t_2 

type tuple__16 (t_1 : Type) (t_2 : Type) (t_3 : Type) (t_4 : Type) (t_5 : Type) (t_6 : Type) (t_7 : Type) (t_8 : Type) (t_9 : Type) (t_10 : Type) (t_11 : Type) (t_12 : Type) (t_13 : Type) (t_14 : Type) (t_15 : Type) (t_16 : Type) =
| Mktuple__16: _1:t_1 -> _2:t_2 -> _3:t_3 -> _4:t_4 -> _5:t_5 -> _6:t_6 -> _7:t_7 -> _8:t_8 -> _9:t_9 -> _10:t_10 -> _11:t_11 -> _12:t_12 -> _13:t_13 -> _14:t_14 -> _15:t_15 -> _16:t_16 -> tuple__16 t_1 t_2 t_3 t_4 t_5 t_6 t_7 t_8 t_9 t_10 t_11 t_12 t_13 t_14 t_15 t_16 

type record__f_g (t_1 : Type) (t_2 : Type) =
| Mkrecord__f_g: f:t_1 -> g:t_2 -> record__f_g t_1 t_2 

val nSMain__identityUnion : (union__bool0int0singletonBosqueNone bool int singletonBosqueNone) -> Tot (union__bool0int0singletonBosqueNone bool int singletonBosqueNone)
let nSMain__identityUnion x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__max : (union__int0singletonBosqueNone int singletonBosqueNone) -> int -> Tot int
let nSMain__max x y = 
    let __tmp_0 = true in 
        if (op_Equality __tmp_0 true) then 
            let __ir_ret___2 = y in 
                let __ir_ret___3 = __ir_ret___2 in 
                    let _return_ = __ir_ret___3 in 
                        _return_
        else 
            let __tmp_4 = (op_GreaterThanOrEqual x y) in 
                if (op_Equality __tmp_4 true) then 
                    let __ir_ret___1 = x in 
                        let __ir_ret___3 = __ir_ret___1 in 
                            let _return_ = __ir_ret___3 in 
                                _return_
                else 
                    let __ir_ret__ = y in 
                        let __ir_ret___3 = __ir_ret__ in 
                            let _return_ = __ir_ret___3 in 
                                _return_

val nSMain__main : int
let nSMain__main  = 
    let __tmp_0 = (Mktuple__2 10 10) in 
        let x = __tmp_0 in 
            let __tmp_16 = (Mktuple__2 1 1) in 
                let __tmp_3 = (Mktuple__16 1 1 1 1 1 1 1 1 1 1 1 1 __tmp_16 "hello" false true) in 
                    let x2 = __tmp_3 in 
                        let __tmp_22 = (Mkrecord__f_g 1 2) in 
                            let x3 = __tmp_22 in 
                                let __tmp_27 = (Mkrecord__f_g?.f x3) in 
                                    let x4 = __tmp_27 in 
                                        let __tmp_28 = (Mkrecord__f_g 20 10) in 
                                            let x5 = __tmp_28 in 
                                                let __tmp_33 = (Mkrecord__f_g?.f x5) in 
                                                    let x6 = __tmp_33 in 
                                                        let y = 20 in 
                                                            let __tmp_35 = (nSMain__identityUnion y) in 
                                                                let y2 = __tmp_35 in 
                                                                    let __tmp_40 = (Mktuple__2?._1 x) in 
                                                                        let __tmp_37 = (nSMain__max __tmp_40 y) in 
                                                                            let z = __tmp_37 in 
                                                                                let __tmp_42 = (Mktuple__2 x y) in 
                                                                                    let zTuple = __tmp_42 in 
                                                                                        let __ir_ret__ = z in 
                                                                                            let _return_ = __ir_ret__ in 
                                                                                                _return_

