module NSMain__main_main
open Sequence
open BosqueTypes
open BosqueTerms

(* Type names *)
let bTypedStringType_BAnyType = (BTypedStringType BAnyType)
let bTypedStringType_BNoneType = (BTypedStringType BNoneType)
let bTupleType_2BIntType_BIntTypefalse = BTupleType false 2 (SCons BIntType 1 (SCons BIntType 0 SNil))
let bTupleType_16BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_BIntType_bTupleType_2BIntType_BIntTypefalse_bTypedStringType_BAnyType_BBoolType_BBoolTypefalse = BTupleType false 16 (SCons BIntType 15 (SCons BIntType 14 (SCons BIntType 13 (SCons BIntType 12 (SCons BIntType 11 (SCons BIntType 10 (SCons BIntType 9 (SCons BIntType 8 (SCons BIntType 7 (SCons BIntType 6 (SCons BIntType 5 (SCons BIntType 4 (SCons bTupleType_2BIntType_BIntTypefalse 3 (SCons bTypedStringType_BAnyType 2 (SCons BBoolType 1 (SCons BBoolType 0 SNil))))))))))))))))
let bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BNoneType = (BUnionType BBoolType (BUnionType BIntType (BUnionType BNoneType bTypedStringType_BNoneType)))
let bUnionType_BIntType_BNoneType = (BUnionType BIntType BNoneType)
let bTupleType_3BIntType_BBoolType_BIntTypefalse = BTupleType false 3 (SCons BIntType 2 (SCons BBoolType 1 (SCons BIntType 0 SNil)))
let bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue = BTupleType true 4 (SCons BIntType 3 (SCons BBoolType 2 (SCons BIntType 1 (SCons BBoolType 0 SNil))))
let bUnionType_bTupleType_3BIntType_BBoolType_BIntTypefalse_bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue = (BUnionType bTupleType_3BIntType_BBoolType_BIntTypefalse bTupleType_4BIntType_BBoolType_BIntType_BBoolTypetrue)
let bTupleType_1bTypedStringType_BAnyTypefalse = BTupleType false 1 (SCons bTypedStringType_BAnyType 0 SNil)
let bTupleType_1bTypedStringType_BNoneTypetrue = BTupleType true 1 (SCons bTypedStringType_BNoneType 0 SNil)
let bUnionType_BBoolType_BNoneType = (BUnionType BBoolType BNoneType)
let bUnionType_BBoolType_BIntType_BNoneType = (BUnionType BBoolType (BUnionType BIntType BNoneType))
let bUnionType_BBoolType_BNoneType_BIntType = (BUnionType BBoolType (BUnionType BNoneType BIntType))
let bTupleType_2bTupleType_2BIntType_BIntTypefalse_BIntTypefalse = BTupleType false 2 (SCons bTupleType_2BIntType_BIntTypefalse 1 (SCons BIntType 0 SNil))

(* Concept Declarations *)

(* Entity Declarations *)

(* Constant Declarations *)

(* Function Declarations *)
val nSMain__identityUnion : (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BNoneType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType_bTypedStringType_BNoneType (getType x)})
let nSMain__identityUnion x = 
  let __ir_ret__ = x in 
    let _return_ = __ir_ret__ in 
      _return_

val nSMain__max : (x:bosqueTerm{subtypeOf bUnionType_BIntType_BNoneType (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf BIntType (getType x)})
let nSMain__max x y = 
  let __tmp_0 = (BBool true) in 
    if (op_Equality __tmp_0 (BBool true)) then 
      let __ir_ret___2 = y in 
        let __ir_ret___3 = __ir_ret___2 in 
          let _return_ = __ir_ret___3 in 
            _return_
    else 
      let __tmp_4 = (extractBool (op_greaterOrEq x y)) in 
        if (op_Equality __tmp_4 (BBool true)) then 
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

val nSMain__identityOpenTuple : (x:bosqueTerm{subtypeOf bTupleType_1bTypedStringType_BNoneTypetrue (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bTupleType_1bTypedStringType_BNoneTypetrue (getType x)})
let nSMain__identityOpenTuple x = 
  let __ir_ret__ = x in 
    let _return_ = __ir_ret__ in 
      _return_

val nSMain__maxx : (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BNoneType (getType x)}) -> (x:bosqueTerm{subtypeOf BIntType (getType x)}) -> Tot (x:bosqueTerm{subtypeOf bUnionType_BBoolType_BIntType_BNoneType (getType x)})
let nSMain__maxx x y = 
  let __tmp_0 = (extractBool (op_greater y (BInt 0))) in 
    if (op_Equality __tmp_0 (BBool true)) then 
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
  let string_test = (BTypedString "string_test" BAnyType) in 
    let __tmp_6 = (BnSMain__PlayerMark (BTypedString "o" BAnyType)) in 
      let __tmp_1 = (BnSMain__Artist (BInt 100) (BBool true) (BTypedString "Cornell" BAnyType) (BTypedString "Chris" BAnyType) __tmp_6) in 
        let node = __tmp_1 in 
          let __tmp_8 = (BnSMain__PlayerMark (BTypedString "x" BAnyType)) in 
            let player1 = __tmp_8 in 
              let __tmp_10 = (BInt 0) in 
                let player2 = __tmp_10 in 
                  let __tmp_11 = (BnSMain__Artist (BInt 100) (BBool true) (BTypedString "Pan" BAnyType) (BTypedString "Peter" BAnyType) player1) in 
                    let node1 = __tmp_11 in 
                      let __tmp_17 = (BnSMain__Artist (BInt 100) (BBool true) (BTypedString "Cornell" BAnyType) (BTypedString "Chris" BAnyType) player1) in 
                        let node2 = __tmp_17 in 
                          let n = BNone in 
                            let __tmp_24 = (Mktuple__2 (BInt 10) (BInt 30)) in 
                              let xTuple2 = __tmp_24 in 
                                let __tmp_40 = (Mktuple__2 (BInt 1) (BInt 1)) in 
                                  let __tmp_27 = (Mktuple__16 (BInt 1) (BInt 1) (BInt 1) (BInt 1) (BInt 1) (BInt 1) (BInt 1) (BInt 1) (BInt 1) (BInt 1) (BInt 1) (BInt 1) __tmp_40 (BTypedString "hello" BAnyType) (BBool false) (BBool true)) in 
                                    let x2 = __tmp_27 in 
                                      let y = (BInt 20) in 
                                        let __tmp_47 = (nSMain__identityUnion y) in 
                                          let y2 = __tmp_47 in 
                                            let _MIRAccessFromIndex = (BInt 0) in 
                                              let __tmp_49 = (nSMain__max __tmp_52 y) in 
                                                let z = __tmp_49 in 
                                                  let __tmp_54 = (nSMain__max z y) in 
                                                    let z_max_func_repeated = __tmp_54 in 
                                                      let __tmp_58 = (Mktuple__3 (BInt 1) (BBool true) (BInt 2)) in 
                                                        let __tmp_57 = (nSMain__identityTupleOptional __tmp_58) in 
                                                          let z2 = __tmp_57 in 
                                                            let __tmp_63 = (Mktuple__1 (BTypedString "hello" BAnyType)) in 
                                                              let __tmp_62 = (nSMain__identityOpenTuple __tmp_63) in 
                                                                let z3 = __tmp_62 in 
                                                                  let __tmp_65 = (nSMain__maxx (BBool false) (BInt 3)) in 
                                                                    let z4 = __tmp_65 in 
                                                                      let __tmp_68 = (Mktuple__2 xTuple2 y) in 
                                                                        let zTuple2 = __tmp_68 in 
                                                                          let __ir_ret__ = z in 
                                                                            let _return_ = __ir_ret__ in 
                                                                              _return_

