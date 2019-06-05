(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-sort Term)
(declare-datatypes () ((BType BInt BBool)))

(declare-fun HasType (Term BType) Bool)
(declare-fun BoxInt (Int) Term)
(declare-fun UnboxInt (Term) Int)

;; (declare-fun op_>= (Term Term) Bool)
;; (assert (forall ((@x Term) (@y Term)) (! (implies (and (HasType @x BInt) (HasType @y BInt)) (= (op_>= @x @y) (>= (UnboxInt @x) (UnboxInt @y)))) :pattern (op_>= @x @y))))
(define-fun op_>= ((@x Term) (@y Term)) Bool (implies (and (HasType @x BInt) (HasType @y BInt)) (>= (UnboxInt @x) (UnboxInt @y))))

;;-------------------------------------------
;; Example

;; (assert
;;  (forall ((@x Term))
;; 	 (! (= (UnboxInt (BoxInt @x)) @x)
;; 	    :pattern ((BoxInt @x))
;; 	    )
;; 	 )
;;  )

(declare-const x Term)
(declare-const x_int Int)
(assert (= (UnboxInt x) x_int))
(assert (= (BoxInt x_int) x))
;;(assert (= (UnboxInt (BoxInt x_int)) x_int))

(declare-const y Term)
(declare-const y_int Int)
(assert (= (UnboxInt y) y_int))
(assert (= (BoxInt y_int) y))
;;(declare-const y_int Int)
;;(assert (= (UnboxInt (BoxInt y_int)) y_int))

(define-fun maxTerm ((@x Term) (@y Term)) Term (ite (op_>= @x @y) @x @y))

(assert (HasType x BBool))
(assert (HasType y BInt))

(define-const flag Bool true)
(define-const example Bool (ite flag (op_>= (maxTerm x y) x) (not (op_>= (maxTerm x y) x))))

(assert example)

(check-sat)
(get-model)
;;-------------------------------------------
