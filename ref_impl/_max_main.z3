(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model true)

(declare-sort Term)
(declare-datatypes () ((BType BInt BBool BString)))

(declare-fun HasType (Term BType) Bool)
(declare-fun UnboxInt (Term) Int)
(declare-fun UnboxBool (Term) Bool)
(declare-fun UnboxString (Term) String)

(declare-fun NSMain__max_@tmp_0 () Term)
(declare-fun NSMain__max_x () Term)
(declare-fun NSMain__max_y () Term)
(declare-fun MIRJumpCondFormula () Term)
(declare-fun NSMain__max__ir_ret_$1 () Term)
(declare-fun MIRJumpFormula () Term)
(declare-fun NSMain__max__ir_ret_$2 () Term)
(declare-fun NSMain__max__ir_ret_ () Term)
(declare-fun NSMain__max__return_ () Term)

(assert (= (UnboxBool NSMain__max_@tmp_0) (>= (UnboxInt NSMain__max_x) (UnboxInt NSMain__max_y))))
(assert (=> (UnboxBool NSMain__max_@tmp_0) (and (and (= (UnboxInt NSMain__max__ir_ret_$1) (UnboxInt NSMain__max_x)) (UnboxBool MIRJumpFormula)) (and (and (=> (or (UnboxBool NSMain__max_@tmp_0) (not (UnboxBool NSMain__max_@tmp_0))) (= (UnboxInt NSMain__max__ir_ret_$2) (UnboxInt NSMain__max__ir_ret_$1))) (= (UnboxInt NSMain__max__ir_ret_$2) (UnboxInt NSMain__max__ir_ret_))) (= (UnboxInt NSMain__max__ir_ret_$2) (UnboxInt NSMain__max__return_))))))
(assert (=> (not (UnboxBool NSMain__max_@tmp_0)) (and (and (= (UnboxInt NSMain__max__ir_ret_) (UnboxInt NSMain__max_y)) (UnboxBool MIRJumpFormula)) (and (and (=> (or (UnboxBool NSMain__max_@tmp_0) (not (UnboxBool NSMain__max_@tmp_0))) (= (UnboxInt NSMain__max__ir_ret_$2) (UnboxInt NSMain__max__ir_ret_$1))) (= (UnboxInt NSMain__max__ir_ret_$2) (UnboxInt NSMain__max__ir_ret_))) (= (UnboxInt NSMain__max__ir_ret_$2) (UnboxInt NSMain__max__return_))))))
(check-sat)
