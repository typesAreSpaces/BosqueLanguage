module NSMain__main_main

val nSMain__max0 : bool -> bool -> Tot bool
let nSMain__max0 x y = 
    if (op_Equality x true) then 
        let _ir_ret__1 = y in 
            let _ir_ret__2 = _ir_ret__1 in 
                let _return_ = _ir_ret__2 in 
                    _return_
    else 
        let _ir_ret_ = x in 
            let _ir_ret__2 = _ir_ret_ in 
                let _return_ = _ir_ret__2 in 
                    _return_

val nSMain__main : bool
let nSMain__main  = 
    let x = 10 in 
        let y = 20 in 
            let __tmp_2 = (nSMain__max0 true false) in 
                let z = __tmp_2 in 
                    let _ir_ret_ = z in 
                        let _return_ = _ir_ret_ in 
                            _return_

