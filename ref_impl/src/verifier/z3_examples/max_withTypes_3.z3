(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model true)

(declare-sort Term)
(declare-datatypes () ((BType BInt BBool BString)))

(declare-fun HasType (Term BType) Bool)
(declare-fun BoxInt (Int) Term)
(declare-fun UnboxInt (Term) Int)
(declare-fun BoxBool (Bool) Term)
(declare-fun UnboxBool (Term) Bool)
(declare-fun BoxString (String) Term)
(declare-fun UnboxString (Term) String)

(assert (forall ((@x Int)) (! (= (UnboxInt (BoxInt @x)) @x) :pattern ((BoxInt @x)))))
(assert (forall ((@x Int)) (! (= (UnboxBool (BoxBool @x)) @x) :pattern ((BoxBool @x)))))
(assert (forall ((@x Int)) (! (= (UnboxString (BoxString @x)) @x) :pattern ((BoxString @x)))))

(define-fun op_> ((@x Term) (@y Term)) Term (BoxBool (> (UnboxInt @x) (UnboxInt @y))))
(define-fun op_< ((@x Term) (@y Term)) Term (BoxBool (< (UnboxInt @x) (UnboxInt @y))))
(define-fun op_>= ((@x Term) (@y Term)) Term (BoxBool (>= (UnboxInt @x) (UnboxInt @y))))
(define-fun op_<= ((@x Term) (@y Term)) Term (BoxBool (<= (UnboxInt @x) (UnboxInt @y))))

;;-------------------------------------------
;; Example

(declare-const x Term)
(declare-const y Term)

(define-fun maxTerm ((@x Term) (@y Term)) Term (ite (UnboxBool (op_> @x @y)) @x @y))

(define-const flag Bool true)
(define-const example Bool
  (ite flag
       (UnboxBool (op_>= (maxTerm x y) x))
       (not (UnboxBool (op_>= (maxTerm x y) x)))
       )
  )

(assert example)

(check-sat)
;;-------------------------------------------
