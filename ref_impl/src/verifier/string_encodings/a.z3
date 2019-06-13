(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model true)

(define-fun charToInt ((s String)) Int
(ite (= s "a") 0
(ite (= s "b") 1
(ite (= s "c") 2
(ite (= s "d") 3
(ite (= s "e") 4
(ite (= s "f") 5
(ite (= s "g") 6
(ite (= s "h") 7
(ite (= s "i") 8
(ite (= s "j") 9
(ite (= s "k") 10
(ite (= s "l") 11
(ite (= s "m") 12
(ite (= s "n") 13
(ite (= s "o") 14
(ite (= s "p") 15
(ite (= s "q") 16
(ite (= s "r") 17
(ite (= s "s") 18
(ite (= s "t") 19
(ite (= s "u") 20
(ite (= s "v") 21
(ite (= s "w") 22
(ite (= s "x") 23
(ite (= s "y") 24
(ite (= s "z") 25 -1)))))))))))))))))))))))))))

(define-fun head ((s String)) String (str.at s 0))
(define-fun tail ((s String)) String (str.substr s 1 (- (str.len s) 1)))

(declare-fun <_string (String String) Bool)
(assert (forall ((@x String) (@y String))
	(=
		(<_string @x @y)
		(ite (= (charToInt (head @x)) (charToInt (head @y)))
		     (<_string (tail @x) (tail @y))
		     (< (charToInt (head @x)) (charToInt (head @y))))
	)
))

;; Examples

(define-const a String "jose")
(define-const b String "narda")
(define-const c String "dad")
(define-const d String "mom")


(assert (not (<_string c d)))

(check-sat)
