(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model true)

(define-fun head ((s String)) String (str.at s 0))
(define-fun tail ((s String)) String (str.substr s 1 (- (str.len s) 1)))
(declare-fun firstChar (String) (_ BitVec 8))
(assert (forall ((s String))
		(!
		 (or (= (seq.unit (firstChar s)) (seq.at s 0))
		     (= (as seq.empty String)  (seq.at s 0)))
		 :pattern (firstChar s)
	       	 :pattern (seq.at s 0))
		))

(declare-fun <_string (String String) Bool)
(assert (forall ((x String) (y String))
		(! (= (<_string x y)
		      (ite (= (head x) (head y))
			   (<_string (tail x) (tail y))
			   (bvult (firstChar x) (firstChar y))))
		   :pattern ((<_string x y)))
		))

;; Examples

(define-const a String "jose")
(define-const b String "narda")
(define-const c String "dad")
(define-const d String "mom")

(assert (not (<_string b a)))

(check-sat)
