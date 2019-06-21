(push)
(declare-const temp Int)
(define-fun f ((x Int)) Bool (and (= temp x)))
(assert (f 1))
(assert (f 2))
(check-sat)
(pop)

;; ------------------------------------------------------

(declare-fun f (Int Int) Bool)

(push)
(declare-const temp Int)
;; (assert (forall ((x Int) (y Int))
;; 				(! (iff
;; 					(f x y)
;; 					(and (= temp x) (>= temp y))
;; 					) :pattern ((f x y)))
;; 				))
(assert (forall ((x Int) (y Int))
				(! (iff
					(f x y)
					(>= x y)
					) :pattern ((f x y)))
				))
(pop)
;; The forall assertion is no longer valid here!
(assert (f 1 2))
;;(assert (f 2 2))
(check-sat)
(get-model)
