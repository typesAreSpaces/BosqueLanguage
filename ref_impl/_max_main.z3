(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model true)

(declare-sort Term)
(declare-datatypes () ((BType BInt BBool BString)))

(declare-fun HasType (Term BType) Bool)
(declare-fun UnboxInt (Term) Int)
(declare-fun UnboxBool (Term) Bool)
(declare-fun UnboxString (Term) String)

(declare-fun NSMain__max_@tmp_0 () Bool)
(declare-fun NSMain__max_x () Int)
(declare-fun NSMain__max_y () Int)
(declare-fun MIRJumpCondFormula () Bool)
(declare-fun NSMain__max__ir_ret_$1 () Int)
(declare-fun MIRJumpFormula () Bool)
(declare-fun NSMain__max__ir_ret_$2 () Int)
(declare-fun NSMain__max__ir_ret_ () Int)
(declare-fun NSMain__max__return_ () Int)

(assert (= NSMain__max_@tmp_0 (>= NSMain__max_x NSMain__max_y)))
(assert MIRJumpCondFormula)
(assert (=> NSMain__max_@tmp_0 (and (and (= NSMain__max__ir_ret_$1 NSMain__max_x) MIRJumpFormula) (and (and (=> (or (= NSMain__max_@tmp_0 true) (not (= NSMain__max_@tmp_0 true))) (= NSMain__max__ir_ret_$2 NSMain__max__ir_ret_$1)) (= NSMain__max__ir_ret_$2 NSMain__max__ir_ret_)) (= NSMain__max__ir_ret_$2 NSMain__max__return_)))))
(assert (=> (not NSMain__max_@tmp_0) (and (and (= NSMain__max__ir_ret_ NSMain__max_y) MIRJumpFormula) (and (and (=> (or (= NSMain__max_@tmp_0 true) (not (= NSMain__max_@tmp_0 true))) (= NSMain__max__ir_ret_$2 NSMain__max__ir_ret_$1)) (= NSMain__max__ir_ret_$2 NSMain__max__ir_ret_)) (= NSMain__max__ir_ret_$2 NSMain__max__return_)))))
(check-sat)
