(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model true)

(declare-sort Term)

(declare-datatypes () ((BType BInt BBool)))

;; All elements of type BType are different

(declare-fun HasType (Term BType) Bool)
(declare-fun BoxInt (Int) Term)
(declare-fun UnboxInt (Term) Int)

(assert
 (forall ((@x Term))
	 (! (= (BoxInt (UnboxInt @x)) @x)
	    :pattern ((UnboxInt @x))
	    )
	 )
 )

;; (assert (= (UnboxInt (BoxInt 14)) 14))
;; (assert (= (UnboxInt (BoxInt 11)) 11))

;;-------------------------------------------
;; Example

(declare-const x Term)
(declare-const y Term)

(assert (HasType x BInt))
(assert (HasType y BInt))

(assert (= x (BoxInt 14)))
(assert (= y (BoxInt 11)))

(define-const example Bool
  (= (UnboxInt x) (UnboxInt y))
  )

(assert example)
;;(assert (not example))

(check-sat)
;;-------------------------------------------
