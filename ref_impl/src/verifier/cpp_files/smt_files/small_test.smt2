(declare-fun x () Int)
(declare-fun f (Int) Int)

(assert (< (f 0) (- 1)))
(assert (forall ((x Int)) (! (>= (f x) 0) :pattern ((f x)))))

(check-sat)

