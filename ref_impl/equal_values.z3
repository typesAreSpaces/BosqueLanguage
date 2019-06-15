(set-option :smt.auto-config false) ; disable automatic self configuration
(set-option :smt.mbqi false) ; disable model-based quantifier instantiation
(set-option :model true)

(declare-sort Term)
(declare-datatypes () ((BType BInt BBool BString BAny BSome BNone)))
(declare-sort Any)
(declare-sort Some)
(declare-sort None)

(declare-fun HasType (Term) BType)
(declare-fun BoxInt (Int) Term)
(declare-fun UnboxInt (Term) Int)
(declare-fun BoxBool (Bool) Term)
(declare-fun UnboxBool (Term) Bool)
(declare-fun BoxString (String) Term)
(declare-fun UnboxString (Term) String)
(declare-fun BoxAny (Any) Term)
(declare-fun UnboxAny (Term) Any)
(declare-fun BoxSome (Some) Term)
(declare-fun UnboxSome (Term) Some)
(declare-fun BoxNone (None) Term)
(declare-fun UnboxNone (Term) None)

(define-fun head ((s String)) String (str.at s 0))
(define-fun tail ((s String)) String (str.substr s 1 (- (str.len s) 1)))
(declare-fun firstChar (String) (_ BitVec 8))
(assert (forall ((s String)) (! (or (= (seq.unit (firstChar s)) (seq.at s 0)) (= (as seq.empty String)  (seq.at s 0))) :pattern (firstChar s) :pattern (seq.at s 0))))
(declare-fun <_string (String String) Bool)
(assert (forall ((x String) (y String)) (! (= (<_string x y) (ite (= (head x) (head y)) (<_string (tail x) (tail y)) (bvult (firstChar x) (firstChar y)))) :pattern ((<_string x y)))))
(define-fun <=_string ((x String) (y String)) Bool (or (<_string x y) (= x y)))
(define-fun >_string ((x String) (y String)) Bool (not (<=_string x y)))
(define-fun >=_string ((x String) (y String)) Bool (not (<_string x y)))
(assert (forall ((@x Int)) (! (= (UnboxInt (BoxInt @x)) @x) :pattern ((BoxInt @x)))))
(assert (forall ((@x Bool)) (! (= (UnboxBool (BoxBool @x)) @x) :pattern ((BoxBool @x)))))
(assert (forall ((@x String)) (! (= (UnboxString (BoxString @x)) @x) :pattern ((BoxString @x)))))

(declare-fun x () Term)
(declare-fun y () Term)

(assert (or (= (HasType x) BInt) (= (HasType x) BNone)))
(assert (or (= (HasType y) BInt) (= (HasType y) BNone)))

(assert (= x y))
(assert (not (= (HasType x) (HasType y))))


(check-sat)
