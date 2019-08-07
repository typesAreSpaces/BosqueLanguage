module NSMain__main_main
open BosqueOption

val nSMain__id : (x:bosqueTerm{isInt x}) -> Tot (x:bosqueTerm{isInt x})
let nSMain__id x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSCore__List__set<T=NSCore__None|NSCore__String<NSMain__PlayerMark>> : (x:bosqueTerm{isInt x}) -> Tot (x:bosqueTerm{isInt x})
let nSCore__List__set<T=NSCore__None|NSCore__String<NSMain__PlayerMark>> x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__Board__markCellWith : (x:bosqueTerm{isNone x}) -> (x:bosqueTerm{isInt x}) -> (x:bosqueTerm{isInt x}) -> (x:bosqueTerm{isString BNoneType x}) -> Tot (x:bosqueTerm{isNone x})
let nSMain__Board__markCellWith this x y mark = 
    let _MIRAccessFromField = 0 in 
        let __tmp_9 = (op_Multiply y 3) in 
            let __tmp_7 = (op_Addition x __tmp_9) in 
                let __tmp_6 = (nSCore__List__set<T=NSCore__None|NSCore__String<NSMain__PlayerMark>> __tmp_5 __tmp_7 mark) in 
                    let _MIRModifyWithFields = 0 in 
                        let __ir_ret__ = __tmp_2 in 
                            let _return_ = __ir_ret__ in 
                                _return_

val nSCore__List__any<T=NSCore__List<[NSCore__Int, NSCore__Int]>>[/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/tictactoe/main.bsq%78%0] : (x:bosqueTerm{isInt x}) -> Tot (x:bosqueTerm{isInt x})
let nSCore__List__any<T=NSCore__List<[NSCore__Int, NSCore__Int]>>[/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/tictactoe/main.bsq%78%0] x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__Board__checkSingleWinner : (x:bosqueTerm{isNone x}) -> (x:bosqueTerm{isString BNoneType x}) -> Tot (x:bosqueTerm{isBool x})
let nSMain__Board__checkSingleWinner this mark = 
    let _MIRAccessConstantValue = 0 in 
        let __tmp_2 = (nSCore__List__any<T=NSCore__List<[NSCore__Int, NSCore__Int]>>[/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/tictactoe/main.bsq%78%0] __tmp_1 mark this) in 
            let __ir_ret__ = __tmp_2 in 
                let _return_ = __ir_ret__ in 
                    _return_

val nSMain__Board__checkForWinner : (x:bosqueTerm{isNone x}) -> Tot (x:bosqueTerm{subtypeOf (BUnionType BNoneType (BTypeStringType BNoneType)) (getType x)})
let nSMain__Board__checkForWinner this = 
    let _MIRAccessConstantValue = 0 in 
        let __tmp_0 = (nSMain__Board__checkSingleWinner this __tmp_2) in 
            if (op_Equality __tmp_0 true) then 
                let _MIRAccessConstantValue = 0 in 
                    let __ir_ret___2 = __tmp_3 in 
                        let __ir_ret___3 = __ir_ret___2 in 
                            let _return_ = __ir_ret___3 in 
                                _return_
            else 
                let _MIRAccessConstantValue = 0 in 
                    let __tmp_4 = (nSMain__Board__checkSingleWinner this __tmp_6) in 
                        if (op_Equality __tmp_4 true) then 
                            let _MIRAccessConstantValue = 0 in 
                                let __ir_ret___1 = __tmp_7 in 
                                    let __ir_ret___3 = __ir_ret___1 in 
                                        let _return_ = __ir_ret___3 in 
                                            _return_
                        else 
                            let __ir_ret__ = none in 
                                let __ir_ret___3 = __ir_ret__ in 
                                    let _return_ = __ir_ret___3 in 
                                        _return_

val nSCore__List__filter<T=[NSCore__Int, NSCore__Int]>[/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/tictactoe/main.bsq%44%0] : (x:bosqueTerm{isInt x}) -> Tot (x:bosqueTerm{isInt x})
let nSCore__List__filter<T=[NSCore__Int, NSCore__Int]>[/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/tictactoe/main.bsq%44%0] x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__Board__getOpenCells : (x:bosqueTerm{isNone x}) -> Tot (x:bosqueTerm{isNone x})
let nSMain__Board__getOpenCells this = 
    let _MIRAccessConstantValue = 0 in 
        let __tmp_2 = (nSCore__List__filter<T=[NSCore__Int, NSCore__Int]>[/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/tictactoe/main.bsq%44%0] __tmp_1 this) in 
            let __ir_ret__ = __tmp_2 in 
                let _return_ = __ir_ret__ in 
                    _return_

val nSCore__List__uniform<T=[NSCore__Int, NSCore__Int]> : (x:bosqueTerm{isInt x}) -> Tot (x:bosqueTerm{isInt x})
let nSCore__List__uniform<T=[NSCore__Int, NSCore__Int]> x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSCore__List__at<T=NSCore__None|NSCore__String<NSMain__PlayerMark>> : (x:bosqueTerm{isInt x}) -> Tot (x:bosqueTerm{isInt x})
let nSCore__List__at<T=NSCore__None|NSCore__String<NSMain__PlayerMark>> x = 
    let __ir_ret__ = x in 
        let _return_ = __ir_ret__ in 
            _return_

val nSMain__Board__getCellContents : (x:bosqueTerm{isNone x}) -> (x:bosqueTerm{isInt x}) -> (x:bosqueTerm{isInt x}) -> Tot (x:bosqueTerm{subtypeOf (BUnionType BNoneType (BTypeStringType BNoneType)) (getType x)})
let nSMain__Board__getCellContents this x y = 
    let _MIRAccessFromField = 0 in 
        let __tmp_6 = (op_Multiply y 3) in 
            let __tmp_4 = (op_Addition x __tmp_6) in 
                let __tmp_3 = (nSCore__List__at<T=NSCore__None|NSCore__String<NSMain__PlayerMark>> __tmp_2 __tmp_4) in 
                    let __ir_ret__ = __tmp_3 in 
                        let _return_ = __ir_ret__ in 
                            _return_

val nSMain__Board__isCellOccupied : (x:bosqueTerm{isNone x}) -> (x:bosqueTerm{isInt x}) -> (x:bosqueTerm{isInt x}) -> Tot (x:bosqueTerm{isBool x})
let nSMain__Board__isCellOccupied this x y = 
    let __tmp_1 = (nSMain__Board__getCellContents this x y) in 
        let _MIRIsTypeOfSome = 0 in 
            let __ir_ret__ = __tmp_0 in 
                let _return_ = __ir_ret__ in 
                    _return_

val nSMain__Game__makeAutoMove : (x:bosqueTerm{isNone x}) -> (x:bosqueTerm{isString BNoneType x}) -> (x:bosqueTerm{isInt x}) -> Tot (x:bosqueTerm{isNone x})
let nSMain__Game__makeAutoMove this mark rnd = 
    let _MIRAccessFromField = 0 in 
        let __tmp_5 = (nSMain__Board__isCellOccupied __tmp_4 1 1) in 
            let __tmp_1 = (op_Negation __tmp_5) in 
                if (op_Equality __tmp_1 true) then 
                    let _MIRAccessFromField = 0 in 
                        let __tmp_11 = (nSMain__Board__markCellWith __tmp_10 1 1 mark) in 
                            let nboard_1 = __tmp_11 in 
                                let nboard_2 = nboard_1 in 
                                    let __tmp_34 = (nSMain__Board__checkForWinner nboard_2) in 
                                        let _MIRModifyWithFields = 0 in 
                                            let __ir_ret__ = __tmp_32 in 
                                                let _return_ = __ir_ret__ in 
                                                    _return_
                else 
                    let _MIRAccessFromField = 0 in 
                        let __tmp_18 = (nSMain__Board__getOpenCells __tmp_17) in 
                            let opts = __tmp_18 in 
                                let __tmp_19 = (nSCore__List__uniform<T=[NSCore__Int, NSCore__Int]> opts rnd) in 
                                    let tup = __tmp_19 in 
                                        let _MIRAccessFromField = 0 in 
                                            let _MIRAccessFromIndex = 0 in 
                                                let _MIRAccessFromIndex = 0 in 
                                                    let __tmp_25 = (nSMain__Board__markCellWith __tmp_24 __tmp_28 __tmp_29 mark) in 
                                                        let nboard = __tmp_25 in 
                                                            let nboard_2 = nboard in 
                                                                let __tmp_34 = (nSMain__Board__checkForWinner nboard_2) in 
                                                                    let _MIRModifyWithFields = 0 in 
                                                                        let __ir_ret__ = __tmp_32 in 
                                                                            let _return_ = __ir_ret__ in 
                                                                                _return_

val nSMain__Game__makeExplicitMove : (x:bosqueTerm{isNone x}) -> (x:bosqueTerm{isInt x}) -> (x:bosqueTerm{isInt x}) -> (x:bosqueTerm{isString BNoneType x}) -> Tot (x:bosqueTerm{isNone x})
let nSMain__Game__makeExplicitMove this x y mark = 
    let _MIRAccessFromField = 0 in 
        let __tmp_3 = (nSMain__Board__markCellWith __tmp_2 x y mark) in 
            let nboard = __tmp_3 in 
                let __tmp_11 = (nSMain__Board__checkForWinner nboard) in 
                    let _MIRModifyWithFields = 0 in 
                        let __ir_ret__ = __tmp_9 in 
                            let _return_ = __ir_ret__ in 
                                _return_

val nSMain__main : (x:bosqueTerm{isNone x})
let nSMain__main  = 
    let __tmp_0 = (nSMain__id 1) in 
        let x = __tmp_0 in 
            let _LoadFieldDefaultValue = 0 in 
                let _LoadFieldDefaultValue = 0 in 
                    let _ConstructorPrimary = 0 in 
                        let game = __tmp_2 in 
                            let _MIRAccessConstantValue = 0 in 
                                let __tmp_5 = (nSMain__Game__makeAutoMove game __tmp_7 0) in 
                                    let game_1 = __tmp_5 in 
                                        let _MIRAccessConstantValue = 0 in 
                                            let __tmp_9 = (nSMain__Game__makeAutoMove game_1 __tmp_11 1) in 
                                                let game_2 = __tmp_9 in 
                                                    let _MIRAccessConstantValue = 0 in 
                                                        let __tmp_13 = (nSMain__Game__makeAutoMove game_2 __tmp_15 2) in 
                                                            let game_3 = __tmp_13 in 
                                                                let _MIRAccessConstantValue = 0 in 
                                                                    let __tmp_17 = (nSMain__Game__makeExplicitMove game_3 2 0 __tmp_21) in 
                                                                        let game_4 = __tmp_17 in 
                                                                            let _MIRAccessConstantValue = 0 in 
                                                                                let __tmp_22 = (nSMain__Game__makeExplicitMove game_4 2 1 __tmp_26) in 
                                                                                    let game_5 = __tmp_22 in 
                                                                                        let __ir_ret__ = game_5 in 
                                                                                            let _return_ = __ir_ret__ in 
                                                                                                _return_

