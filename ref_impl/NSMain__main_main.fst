module NSMain__main_main

let nSMain__max0 x y = 
    let __tmp_0 = (op_GreaterThanOrEqual x y) in 
        if (op_Equality __tmp_0 true) then 
            let _ir_ret__1 = x in 
                let _ir_ret__2 = _ir_ret__1 in 
                    let _return_ = _ir_ret__2 in 
                        _return_
        else 
            let _ir_ret_ = y in 
                let _ir_ret__2 = _ir_ret_ in 
                    let _return_ = _ir_ret__2 in 
                        _return_

let nSMain__main  = 
    let x = 10 in 
        let y = 20 in 
            let __tmp_2 = (nSMain__max0 x y) in 
                let z = __tmp_2 in 
                    let _ir_ret_ = z in 
                        let _return_ = _ir_ret_ in 
                            _return_

