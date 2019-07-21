(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)

(define-const conjecture Bool
(= (* (+ a b c d e) (+ a b c d e)) (+ (* a a) (* 2 a b) (* 2 a c) (* 2 a d) (* 2 a e) (* b b) (* 2 b c) (* 2 b d) (* 2 b e) (* c c) (* 2 c d) (* 2 c e) (* d d) (* 2 d e) (* e e)) )
)

(assert (not conjecture))

(check-sat)