module NSMain__main_main
open BosqueOption

val nSMain__max : (x:bosqueTerm{subtypeOf (BUnionType BIntType BNoneType) (getType x)}) -> (x:bosqueTerm{isInt x}) -> Tot (x:bosqueTerm{isInt x})
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

val nSMain__identityUnion : (bosqueTerm) -> Tot (bosqueTerm)
let nSMain__identityUnion x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__identityTupleOptional : (x:bosqueTerm{isTuple 2 (SCons BIntType (SCons BBoolType SNil))}) -> Tot (x:bosqueTerm{isTuple 2 (SCons BIntType (SCons BBoolType SNil))})
let nSMain__identityTupleOptional x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__main : (x:bosqueTerm{isInt x})
let nSMain__main  = 
    let s = "hello1" in 
        let _LoadConstTypeString = 0 in 
            let s1 = __tmp_1 in 
                let n = none in 
                    let __tmp_3 = (Mktuple__2 10 30) in 
                        let x = __tmp_3 in 
                            let y = 20 in 
                                let _MIRAccessFromIndex = 0 in 
                                    let __tmp_7 = (nSMain__max __tmp_10 y) in 
                                        let z = __tmp_7 in 
                                            let __tmp_25 = (Mktuple__2 1 1) in 
                                                let __tmp_12 = (Mktuple__16 1 1 1 1 1 1 1 1 1 1 1 1 __tmp_25 "hello" false true) in 
                                                    let x2 = __tmp_12 in 
                                                        let __tmp_31 = (Mkrecord__f_g 1 2) in 
                                                            let x3 = __tmp_31 in 
                                                                let _MIRAccessFromProperty = 0 in 
                                                                    let x4 = __tmp_36 in 
                                                                        let __tmp_37 = (Mkrecord__f_g 20 10) in 
                                                                            let x5 = __tmp_37 in 
                                                                                let _MIRAccessFromProperty = 0 in 
                                                                                    let x6 = __tmp_42 in 
                                                                                        let __tmp_43 = (nSMain__identityUnion y) in 
                                                                                            let y2 = __tmp_43 in 
                                                                                                let __tmp_46 = (Mktuple__2 1 true) in 
                                                                                                    let __tmp_45 = (nSMain__identityTupleOptional __tmp_46) in 
                                                                                                        let z2 = __tmp_45 in 
                                                                                                            let __tmp_50 = (Mktuple__1 1) in 
                                                                                                                let __tmp_49 = (nSMain__identityTupleOptional __tmp_50) in 
                                                                                                                    let z3 = __tmp_49 in 
                                                                                                                        let __tmp_52 = (Mktuple__2 x y) in 
                                                                                                                            let zTuple = __tmp_52 in 
                                                                                                                                let __ir_ret__ = z in 
                                                                                                                                    let _return_ = __ir_ret__ in 
                                                                                                                                        _return_

