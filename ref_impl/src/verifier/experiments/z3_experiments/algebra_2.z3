(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(define-const conjecture Bool
(= (* (+ a b c) (+ a b c)) (+ (* a a) (* 2 a b) (* 2 a c) (* b b) (* 2 b c) (* c c)) )
)

(assert (not conjecture))

(check-sat)