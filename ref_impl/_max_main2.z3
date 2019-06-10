(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model true)

(declare-sort Term)
(declare-datatypes () ((BType BInt BBool BString)))

(declare-fun HasType (Term) BType)
(declare-fun BoxInt (Int) Term)
(declare-fun UnboxInt (Term) Int)
(declare-fun BoxBool (Bool) Term)
(declare-fun UnboxBool (Term) Bool)
(declare-fun BoxString (String) Term)
(declare-fun UnboxString (Term) String)

(assert (forall ((@x Int)) (! (= (UnboxInt (BoxInt @x)) @x) :pattern ((BoxInt @x)))))
(assert (forall ((@x Bool)) (! (= (UnboxBool (BoxBool @x)) @x) :pattern ((BoxBool @x)))))
(assert (forall ((@x String)) (! (= (UnboxString (BoxString @x)) @x) :pattern ((BoxString @x)))))

(declare-fun NSMain__max_z () Term)
(declare-fun NSMain__max_@tmp_1 () Term)
(declare-fun MIRJumpCondFormula () Term)
(declare-fun NSMain__max__ir_ret_$2 () Term)
(declare-fun NSMain__max_y () Term)
(declare-fun MIRJumpFormula () Term)
(declare-fun NSMain__max__ir_ret_$3 () Term)
(declare-fun NSMain__max_@tmp_5 () Term)
(declare-fun NSMain__max__ir_ret_$1 () Term)
(declare-fun NSMain__max__ir_ret_ () Term)
(declare-fun NSMain__max__return_ () Term)

(assert (and (and (and (and true (= NSMain__max_z (BoxInt 3))) (= NSMain__max_@tmp_1 (BoxBool (>= (UnboxInt NSMain__max_z) 0)))) (UnboxBool MIRJumpCondFormula)) (and (=> (UnboxBool NSMain__max_@tmp_1) (and (and (= NSMain__max__ir_ret_$2 (BoxInt (UnboxInt NSMain__max_y))) (UnboxBool MIRJumpFormula)) (and (and (and (=> (or (= NSMain__max_@tmp_1 (BoxBool true)) (not (= NSMain__max_@tmp_1 (BoxBool true)))) (= NSMain__max__ir_ret_$3 NSMain__max__ir_ret_$2)) (=> (or (= NSMain__max_@tmp_5 (BoxBool true)) (not (= NSMain__max_@tmp_5 (BoxBool true)))) (= NSMain__max__ir_ret_$3 NSMain__max__ir_ret_$1))) (= NSMain__max__ir_ret_$3 NSMain__max__ir_ret_)) (= NSMain__max__return_ (BoxInt (UnboxInt NSMain__max__ir_ret_$3)))))) (=> (not (UnboxBool NSMain__max_@tmp_1)) (and (and (= NSMain__max_@tmp_5 (BoxBool (>= (UnboxInt NSMain__max_y) 0))) (UnboxBool MIRJumpCondFormula)) (and (=> (UnboxBool NSMain__max_@tmp_5) (and (and (= NSMain__max__ir_ret_$1 (BoxInt (UnboxInt NSMain__max_y))) (UnboxBool MIRJumpFormula)) (and (and (and (=> (or (= NSMain__max_@tmp_1 (BoxBool true)) (not (= NSMain__max_@tmp_1 (BoxBool true)))) (= NSMain__max__ir_ret_$3 NSMain__max__ir_ret_$2)) (=> (or (= NSMain__max_@tmp_5 (BoxBool true)) (not (= NSMain__max_@tmp_5 (BoxBool true)))) (= NSMain__max__ir_ret_$3 NSMain__max__ir_ret_$1))) (= NSMain__max__ir_ret_$3 NSMain__max__ir_ret_)) (= NSMain__max__return_ (BoxInt (UnboxInt NSMain__max__ir_ret_$3)))))) (=> (not (UnboxBool NSMain__max_@tmp_5)) (and (and (= NSMain__max__ir_ret_ (BoxInt (UnboxInt NSMain__max_y))) (UnboxBool MIRJumpFormula)) (and (and (and (=> (or (= NSMain__max_@tmp_1 (BoxBool true)) (not (= NSMain__max_@tmp_1 (BoxBool true)))) (= NSMain__max__ir_ret_$3 NSMain__max__ir_ret_$2)) (=> (or (= NSMain__max_@tmp_5 (BoxBool true)) (not (= NSMain__max_@tmp_5 (BoxBool true)))) (= NSMain__max__ir_ret_$3 NSMain__max__ir_ret_$1))) (= NSMain__max__ir_ret_$3 NSMain__max__ir_ret_)) (= NSMain__max__return_ (BoxInt (UnboxInt NSMain__max__ir_ret_$3))))))))))))
(check-sat)
