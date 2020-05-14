(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation

(declare-fun x () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int Int) Int)

(assert (< (f 0) (- 1)))
(assert (forall ((x Int) (y Int)) (! (and (>= (f x) 0) (= (h x y) (+ (g y) (g x)))) :pattern ((f x) (h x y) (g y) (g x)))))
(assert (forall ((x Int)) (! (forall ((y Int)) (! (and (>= (f x) 0) (= (h x y) (+ (g y) (g x)))) :pattern ((h x y) (g y)))) :pattern ((f x) (g x)))))

(check-sat)

