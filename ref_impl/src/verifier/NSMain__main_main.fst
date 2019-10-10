module NSMain__main_main
open BosqueTypes

(* Type names *)

let bTypeStringType_BAnyType = (BTypedStringType BAnyType)

let bUnionType_bUnionType_BBoolType_BIntType_BNoneType_bTypeStringType_BAnyType = (BUnionType BBoolType (BUnionType BIntType (BUnionType BNoneType bTypeStringType_BAnyType)))
let bUnionType_bUnionType_BIntType_BNoneType = (BUnionType BIntType BNoneType)
let bUnionType_bUnionType_bTupleType_3BIntType_BBoolType_BIntTypefalse_bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue = (BUnionType bTupleType_3BIntType_BBoolType_BIntTypefalse bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue)
let bUnionType_bUnionType_BBoolType_BNoneType = (BUnionType BBoolType BNoneType)
let bUnionType_bUnionType_BBoolType_BIntType_BNoneType = (BUnionType BBoolType (BUnionType BIntType BNoneType))
let bUnionType_bUnionType_BBoolType_BNoneType_BIntType = (BUnionType BBoolType (BUnionType BNoneType BIntType))



let bTupleType_bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType (SCons BIntType SNil))
let bTupleType_bTupleType_16BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_bTupleType_2BIntType_BIntTypefalse_bTypeStringType_BAnyType_BBoolType_BBoolTypefalse = BTupleType false 16 (SCons BIntType (SCons BIntType (SCons BIntType (SCons BIntType (SCons BIntType (SCons BIntType (SCons BIntType (SCons BIntType (SCons BIntType (SCons BIntType (SCons BIntType (SCons BIntType (SCons bTupleType_2BIntType_BIntTypefalse (SCons bTypeStringType_BAnyType (SCons BBoolType (SCons BBoolType SNil))))))))))))))))
let bTupleType_bTupleType_3BIntType_BBoolType_BIntTypefalse = BTupleType false 3 (SCons BIntType (SCons BBoolType (SCons BIntType SNil)))
let bTupleType_bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue = BTupleType true 4 (SCons BIntType (SCons BBoolType (SCons BIntType (SCons BBoolType SNil))))
let bTupleType_bTupleType_1bTypeStringType_BAnyTypefalse = BTupleType false 1 (SCons bTypeStringType_BAnyType SNil)
let bTupleType_bTupleType_1bTypeStringType_BAnyTypetrue = BTupleType true 1 (SCons bTypeStringType_BAnyType SNil)
let bTupleType_bTupleType_2bTupleType_2BIntType_BIntTypefalse_BIntTypefalse = BTupleType false 2 (SCons bTupleType_2BIntType_BIntTypefalse (SCons BIntType SNil))

(* Concept Declarations *)

(* Entity Declarations *)

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__identityUnion : (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType_bTypeStringType_BAnyType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType_bTypeStringType_BAnyType (getType x)})
let nSMain__identityUnion x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__max : (x:bosqueTerm{subtypeOf bUnionType_BIntType_BNoneType (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf BIntType (getType x)})
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

val nSMain__identityTupleOptional : (x:bosqueTerm{subtypeOf bUnionType_bTupleType_3BIntType_BBoolType_BIntTypefalse_bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bUnionType_bTupleType_3BIntType_BBoolType_BIntTypefalse_bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue (getType x)})
let nSMain__identityTupleOptional x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__identityOpenTuple : (x:bosqueTerm{subtypeOf bTupleType_1bTypeStringType_BAnyTypetrue (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bTupleType_1bTypeStringType_BAnyTypetrue (getType x)})
let nSMain__identityOpenTuple x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__maxx : (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BNoneType (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType (getType x)})
let nSMain__maxx x y = 
    let __tmp_0 = (op_GreaterThan y 0) in 
        if (op_Equality __tmp_0 true) then 
            let __ir_ret___1 = x in 
                let __ir_ret___2 = __ir_ret___1 in 
                    let _return_ = __ir_ret___2 in 
                        _return_
        else 
            let __ir_ret__ = y in 
                let __ir_ret___2 = __ir_ret__ in 
                    let _return_ = __ir_ret___2 in 
                        _return_

val nSMain__main : (x:bosqueTerm{subtypeOf BIntType (getType x)})
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
                                        let y = 20 in 
                                            let __tmp_26 = (nSMain__identityUnion y) in 
                                                let y2 = __tmp_26 in 
                                                    let _MIRAccessFromIndex = 0 in 
                                                        let __tmp_28 = (nSMain__max __tmp_31 y) in 
                                                            let z = __tmp_28 in 
                                                                let __tmp_33 = (nSMain__max z y) in 
                                                                    let z_max_func_repeated = __tmp_33 in 
                                                                        let __tmp_37 = (Mktuple__3 1 true 2) in 
                                                                            let __tmp_36 = (nSMain__identityTupleOptional __tmp_37) in 
                                                                                let z2 = __tmp_36 in 
                                                                                    let __tmp_42 = (Mktuple__1 "hello") in 
                                                                                        let __tmp_41 = (nSMain__identityOpenTuple __tmp_42) in 
                                                                                            let z3 = __tmp_41 in 
                                                                                                let __tmp_44 = (nSMain__maxx false 3) in 
                                                                                                    let z4 = __tmp_44 in 
                                                                                                        let __tmp_47 = (Mktuple__2 xTuple2 y) in 
                                                                                                            let zTuple2 = __tmp_47 in 
                                                                                                                let __ir_ret__ = z in 
                                                                                                                    let _return_ = __ir_ret__ in 
                                                                                                                        _return_

