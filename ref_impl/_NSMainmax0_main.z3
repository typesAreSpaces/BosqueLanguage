(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model true)

(declare-sort Term)
(declare-datatypes () ((BType BInt BBool BString BAny BSome BNone BTuple BRecord)))
(declare-sort None)
(declare-sort RecordProperty)

(declare-fun HasType (Term) BType)
(declare-fun BoxInt (Int) Term)
(declare-fun UnboxInt (Term) Int)
(declare-fun BoxBool (Bool) Term)
(declare-fun UnboxBool (Term) Bool)
(declare-fun BoxString (String) Term)
(declare-fun UnboxString (Term) String)
(declare-fun TupleElement (Term Int) Term)
(declare-fun TupleLength (Term) Int)
(declare-fun RecordElement (Term RecordProperty) Term)
(declare-fun RecordLength (Term) Int)
(declare-fun BoxNone (None) Term)
(declare-fun UnboxNone (Term) None)

(define-fun head ((s String)) String (str.at s 0))
(define-fun tail ((s String)) String (str.substr s 1 (- (str.len s) 1)))
(declare-fun firstChar (String) (_ BitVec 8))
(assert (forall ((s String)) (! (or (= (seq.unit (firstChar s)) (seq.at s 0)) (= (as seq.empty String)  (seq.at s 0))) :pattern (firstChar s) :pattern (seq.at s 0))))
(declare-fun <_string (String String) Bool)
(assert (forall ((x String) (y String)) (! (= (<_string x y) (ite (= (head x) (head y)) (<_string (tail x) (tail y)) (bvult (firstChar x) (firstChar y)))) :pattern ((<_string x y)))))
(define-fun <=_string ((x String) (y String)) Bool (or (<_string x y) (= x y)))
(define-fun >_string ((x String) (y String)) Bool (not (<=_string x y)))
(define-fun >=_string ((x String) (y String)) Bool (not (<_string x y)))

(assert (forall ((@x Int)) (! (= (UnboxInt (BoxInt @x)) @x) :pattern ((BoxInt @x)))))
(assert (forall ((@x Bool)) (! (= (UnboxBool (BoxBool @x)) @x) :pattern ((BoxBool @x)))))
(assert (forall ((@x String)) (! (= (UnboxString (BoxString @x)) @x) :pattern ((BoxString @x)))))
(assert (forall ((@x None)) (! (= (UnboxNone (BoxNone @x)) @x) :pattern ((BoxNone @x)))))

(declare-fun @NSMain__max0_x () Term)
(declare-fun @NSMain__max0_y () Term)
(declare-fun @NSMain__max0_@tmp_0 () Term)
(declare-fun MIRJumpCondFormula () Term)
(declare-fun @NSMain__max0__ir_ret_$1 () Term)
(declare-fun MIRJumpFormula () Term)
(declare-fun @NSMain__max0__ir_ret_$2 () Term)
(declare-fun @NSMain__max0__ir_ret_ () Term)
(declare-fun @NSMain__max0__return_ () Term)

(assert (= (HasType @NSMain__max0_x) BInt))
(assert (= (HasType @NSMain__max0_y) BInt))
(assert (= (HasType @NSMain__max0_@tmp_0) BBool))
(assert (= (HasType @NSMain__max0__ir_ret_) BInt))
(assert (= (HasType @NSMain__max0__ir_ret_$1) BInt))
(assert (= (HasType @NSMain__max0__ir_ret_$2) BInt))
(assert (= (HasType @NSMain__max0__return_) BInt))

(assert (=> (and (= (HasType @NSMain__max0_x) BInt) (= (HasType @NSMain__max0_y) BInt)) (and (= @NSMain__max0_@tmp_0 (BoxBool (>= (UnboxInt @NSMain__max0_x) (UnboxInt @NSMain__max0_y)))) (= (HasType @NSMain__max0_@tmp_0) BBool))))
(assert (=> (and (= (HasType @NSMain__max0_x) BString) (= (HasType @NSMain__max0_y) BString)) (and (= @NSMain__max0_@tmp_0 (BoxBool (>=_string (UnboxString @NSMain__max0_x) (UnboxString @NSMain__max0_y)))) (= (HasType @NSMain__max0_@tmp_0) BBool))))

(assert (UnboxBool MIRJumpCondFormula))

(assert (=> (= @NSMain__max0_@tmp_0 (BoxBool true))
	(and (and
		(= @NSMain__max0__ir_ret_$1 (BoxInt (UnboxInt @NSMain__max0_x)))
		(UnboxBool MIRJumpFormula)
	     )
	     (and
		(and
			(=>
				(= @NSMain__max0_@tmp_0 (BoxBool true))
				(= @NSMain__max0__ir_ret_$2 @NSMain__max0__ir_ret_$1)
			)
			(=>
				(not (= @NSMain__max0_@tmp_0 (BoxBool true)))
				(= @NSMain__max0__ir_ret_$2 @NSMain__max0__ir_ret_))
			) (= @NSMain__max0__return_ (BoxInt (UnboxInt @NSMain__max0__ir_ret_$2)))))))

(assert (=> (not (= @NSMain__max0_@tmp_0 (BoxBool true))) (and (and (= @NSMain__max0__ir_ret_ (BoxInt (UnboxInt @NSMain__max0_y))) (UnboxBool MIRJumpFormula)) (and (and (=> (= @NSMain__max0_@tmp_0 (BoxBool true)) (= @NSMain__max0__ir_ret_$2 @NSMain__max0__ir_ret_$1)) (=> (not (= @NSMain__max0_@tmp_0 (BoxBool true))) (= @NSMain__max0__ir_ret_$2 @NSMain__max0__ir_ret_))) (= @NSMain__max0__return_ (BoxInt (UnboxInt @NSMain__max0__ir_ret_$2)))))))
(check-sat)
