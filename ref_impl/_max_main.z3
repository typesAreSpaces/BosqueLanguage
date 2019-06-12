(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model true)

(declare-sort Term)
(declare-datatypes () ((BType BInt BBool BString BAny BSome BNone)))

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

(declare-fun NSMain__max_x () Term)
(declare-fun NSMain__max_y () Term)
(declare-fun NSMain__max_@tmp_0 () Term)
(declare-fun MIRJumpCondFormula () Term)
(declare-fun NSMain__max__ir_ret_$1 () Term)
(declare-fun MIRJumpFormula () Term)
(declare-fun NSMain__max__ir_ret_$2 () Term)
(declare-fun NSMain__max__ir_ret_ () Term)
(declare-fun NSMain__max__return_ () Term)

(assert (=> (and (= (HasType NSMain__max_x) BInt) (= (HasType NSMain__max_y) BInt)) (= NSMain__max_@tmp_0 (BoxBool (>= (UnboxInt NSMain__max_x) (UnboxInt NSMain__max_y))))))
(assert (=> (and (= (HasType NSMain__max_x) BString) (= (HasType NSMain__max_y) BString)) (= NSMain__max_@tmp_0 (BoxBool (>= (UnboxString NSMain__max_x) (UnboxString NSMain__max_y))))))
(assert (UnboxBool MIRJumpCondFormula))
(assert (=> (= NSMain__max_@tmp_0 (BoxBool true)) (and (and (= NSMain__max__ir_ret_$1 (BoxInt (UnboxInt NSMain__max_x))) (UnboxBool MIRJumpFormula)) (and (and (=> (= NSMain__max_@tmp_0 (BoxBool true)) (= NSMain__max__ir_ret_$2 NSMain__max__ir_ret_$1)) (=> (not (= NSMain__max_@tmp_0 (BoxBool true))) (= NSMain__max__ir_ret_$2 NSMain__max__ir_ret_))) (= NSMain__max__return_ (BoxInt (UnboxInt NSMain__max__ir_ret_$2)))))))
(assert (=> (not (= NSMain__max_@tmp_0 (BoxBool true))) (and (and (= NSMain__max__ir_ret_ (BoxInt (UnboxInt NSMain__max_y))) (UnboxBool MIRJumpFormula)) (and (and (=> (= NSMain__max_@tmp_0 (BoxBool true)) (= NSMain__max__ir_ret_$2 NSMain__max__ir_ret_$1)) (=> (not (= NSMain__max_@tmp_0 (BoxBool true))) (= NSMain__max__ir_ret_$2 NSMain__max__ir_ret_))) (= NSMain__max__return_ (BoxInt (UnboxInt NSMain__max__ir_ret_$2)))))))
(check-sat)
