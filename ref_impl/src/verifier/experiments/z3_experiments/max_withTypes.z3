(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-sort Term)
(declare-datatypes () ((BType BInt BBool)))

(declare-fun HasType (Term BType) Bool)
(declare-fun BoxInt (Int) Term)
(declare-fun UnboxInt (Term) Int)

(assert
 (forall ((@x Term))
	 (! (implies
	     (HasType @x BInt)
	     (= (BoxInt (UnboxInt @x)) @x))
	    :pattern ((UnboxInt @x))
	    )
	 )
 )

(declare-fun op_>= (Term Term) Bool)
(assert (forall ((@x Term) (@y Term)) (! (implies (and (HasType @x BInt) (HasType @y BInt)) (= (op_>= @x @y) (>= (UnboxInt @x) (UnboxInt @y)))) :pattern (op_>= @x @y))))

;;-------------------------------------------
;; Example

(declare-const x Term)
(declare-const y Term)

(define-fun maxTerm ((@x Term) (@y Term)) Term (ite (op_>= @x @y) @x @y))

(assert (HasType x BInt))
(assert (HasType y BInt))

(define-const example Bool (op_>= (maxTerm x y) x))

(assert (not example))
;;(assert (not example))

(check-sat)
;;-------------------------------------------
