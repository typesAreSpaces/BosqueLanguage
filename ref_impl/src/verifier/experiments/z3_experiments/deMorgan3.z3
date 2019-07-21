(declare-const a Bool)
(define-fun demorgan () Bool
    (= (and a b) (not (or (not a) (not b)))))
(declare-const b Bool)
(assert (not demorgan))
(check-sat)