module NSMain__main_main
open BosqueOption

val nSMain__identityUnion : (x:bosqueTerm{subtypeOf (BUnionType BBoolType (BUnionType BIntType (BUnionType BNoneType (BTypeStringType BAnyType)))) (getType x)}) -> Tot (x:bosqueTerm{subtypeOf (BUnionType BBoolType (BUnionType BIntType (BUnionType BNoneType (BTypeStringType BAnyType)))) (getType x)})
let nSMain__identityUnion x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

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

val nSMain__identityTupleOptional : (x:bosqueTerm{subtypeOf (BUnionType (BTupleType false 3 (SCons BIntType (SCons BBoolType (SCons BIntType SNil)))) (BTupleType true 4 (SCons BIntType (SCons BBoolType (SCons BIntType (SCons BBoolType SNil)))))) (getType x)}) -> Tot (x:bosqueTerm{subtypeOf (BUnionType (BTupleType false 3 (SCons BIntType (SCons BBoolType (SCons BIntType SNil)))) (BTupleType true 4 (SCons BIntType (SCons BBoolType (SCons BIntType (SCons BBoolType SNil)))))) (getType x)})
let nSMain__identityTupleOptional x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__identityOpenTuple : (x:bosqueTerm{isTuple true 1 (SCons (BTypeStringType BAnyType) SNil)}) -> Tot (x:bosqueTerm{isTuple true 1 (SCons (BTypeStringType BAnyType) SNil)})
let nSMain__identityOpenTuple x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__main : (x:bosqueTerm{isInt x})
let nSMain__main  = 
    let string_test = "string_test" in 
        let _LoadConstTypeString = 0 in 
            let player1 = __tmp_1 in 
                let n = none in 
                    let __tmp_3 = (Mktuple__2 10 30) in 
                        let xTuple2 = __tmp_3 in 
                            let __tmp_19 = (Mktuple__2 1 1) in 
                                let __tmp_6 = (Mktuple__16 1 1 1 1 1 1 1 1 1 1 1 1 __tmp_19 "hello" false true) in 
                                    let x2 = __tmp_6 in 
                                        let __tmp_25 = (Mkrecord__f_g 1 2) in 
                                            let xRecord = __tmp_25 in 
                                                let _MIRAccessFromProperty = 0 in 
                                                    let xProjection = __tmp_30 in 
                                                        let __tmp_31 = (Mkrecord__f_g 20 10) in 
                                                            let xRecord2 = __tmp_31 in 
                                                                let _MIRAccessFromProperty = 0 in 
                                                                    let xProjection2 = __tmp_36 in 
                                                                        let y = 20 in 
                                                                            let __tmp_38 = (nSMain__identityUnion y) in 
                                                                                let y2 = __tmp_38 in 
                                                                                    let _MIRAccessFromIndex = 0 in 
                                                                                        let __tmp_40 = (nSMain__max __tmp_43 y) in 
                                                                                            let z = __tmp_40 in 
                                                                                                let __tmp_45 = (nSMain__max z y) in 
                                                                                                    let z_max_func_repeated = __tmp_45 in 
                                                                                                        let __tmp_49 = (Mktuple__3 1 true 2) in 
                                                                                                            let __tmp_48 = (nSMain__identityTupleOptional __tmp_49) in 
                                                                                                                let z2 = __tmp_48 in 
                                                                                                                    let __tmp_54 = (Mktuple__1 "hello") in 
                                                                                                                        let __tmp_53 = (nSMain__identityOpenTuple __tmp_54) in 
                                                                                                                            let z3 = __tmp_53 in 
                                                                                                                                let __tmp_56 = (Mktuple__2 xTuple2 y) in 
                                                                                                                                    let zTuple2 = __tmp_56 in 
                                                                                                                                        let __ir_ret__ = z in 
                                                                                                                                            let _return_ = __ir_ret__ in 
                                                                                                                                                _return_

