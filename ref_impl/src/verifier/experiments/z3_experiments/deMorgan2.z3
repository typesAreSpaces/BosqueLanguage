(declare-const a Bool)
(declare-const b Bool)
(define-fun demorgan ((x Bool) (y Bool)) Bool
    (= (and x y) (not (or (not x) (not y)))))
(assert (not (demorgan a b)))
(check-sat)