module NSMain__main_main

type tuple__2 (t_1 : Type) (t_2 : Type) =
| Mktuple__2: _1:t_1 -> _2:t_2 -> tuple__2 t_1 t_2 

type tuple__16 (t_1 : Type) (t_2 : Type) (t_3 : Type) (t_4 : Type) (t_5 : Type) (t_6 : Type) (t_7 : Type) (t_8 : Type) (t_9 : Type) (t_10 : Type) (t_11 : Type) (t_12 : Type) (t_13 : Type) (t_14 : Type) (t_15 : Type) (t_16 : Type) =
| Mktuple__16: _1:t_1 -> _2:t_2 -> _3:t_3 -> _4:t_4 -> _5:t_5 -> _6:t_6 -> _7:t_7 -> _8:t_8 -> _9:t_9 -> _10:t_10 -> _11:t_11 -> _12:t_12 -> _13:t_13 -> _14:t_14 -> _15:t_15 -> _16:t_16 -> tuple__16 t_1 t_2 t_3 t_4 t_5 t_6 t_7 t_8 t_9 t_10 t_11 t_12 t_13 t_14 t_15 t_16 

type tuple__3 (t_1 : Type) (t_2 : Type) (t_3 : Type) =
| Mktuple__3: _1:t_1 -> _2:t_2 -> _3:t_3 -> tuple__3 t_1 t_2 t_3 

type record__f_g (t_1 : Type) (t_2 : Type) =
| Mkrecord__f_g: f:t_1 -> g:t_2 -> record__f_g t_1 t_2 

val nSMain__max0 : (tuple__2 int int) -> int -> Tot int
let nSMain__max0 x y = 
    let __tmp_0 = (Mktuple__3 1 2 3) in 
        let z = __tmp_0 in 
            let __tmp_6 = (Mktuple__3?._1 z) in 
                let z_1 = __tmp_6 in 
                    let __tmp_7 = (Mktuple__3 1 2 3) in 
                        let z2 = __tmp_7 in 
                            let __tmp_13 = (Mktuple__3?._2 z2) in 
                                let z2_1 = __tmp_13 in 
                                    let __tmp_17 = (Mktuple__2?._1 x) in 
                                        let __tmp_14 = (op_GreaterThanOrEqual __tmp_17 y) in 
                                            if (op_Equality __tmp_14 true) then 
                                                let __tmp_21 = (Mktuple__2?._1 x) in 
                                                    let _ir_ret__1 = __tmp_21 in 
                                                        let _ir_ret__2 = _ir_ret__1 in 
                                                            let _return_ = _ir_ret__2 in 
                                                                _return_
                                            else 
                                                let _ir_ret_ = y in 
                                                    let _ir_ret__2 = _ir_ret_ in 
                                                        let _return_ = _ir_ret__2 in 
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
                                                            let __tmp_35 = (nSMain__max0 x y) in 
                                                                let z = __tmp_35 in 
                                                                    let __tmp_38 = (Mktuple__2 x y) in 
                                                                        let zTuple = __tmp_38 in 
                                                                            let _ir_ret_ = z in 
                                                                                let _return_ = _ir_ret_ in 
                                                                                    _return_

