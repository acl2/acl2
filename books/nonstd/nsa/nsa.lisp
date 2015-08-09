(in-package "ACL2")

; cert_param: (uses-acl2r)

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;;; Added for compatibility with old NSA books
(defmacro standard-numberp (x)
  `(and (acl2-numberp ,x)
	(standardp ,x)))

(deftheory nsa-theory
  '(i-small i-large i-close))

;;; You would think this macro was included with ACL2!  I don't know
;;; how I lived without it!

(defmacro enable-disable (enable-list disable-list)
  (list 'union-theories
	(cons 'disable disable-list)
	`(quote ,enable-list)))

;;; These axioms from axioms.lisp are dangerous as :rewrite rules, so
;;; we disabled them there.  Here, we re-enable them, but only as
;;; :forward-chaining rules, so that only type reasoning is used to
;;; check the hypothesis.  That should give us the best of both worlds
;;; when small/limited are disabled below.

(defthm small-are-limited-forward
  (implies (i-small x)
	   (i-limited x))
  :hints (("Goal" :in-theory (enable small-are-limited)))
  :rule-classes (:forward-chaining))

(defthm standards-are-limited-forward
  (implies (and (standardp x)
		(acl2-numberp x))
	   (i-limited x))
  :hints (("Goal" :in-theory (enable standards-are-limited)))
  :rule-classes (:forward-chaining))

;;; The key theorem we want is that all rationals with abs(numerator)
;;; and denominator <= 10000 (really some fixed number) are standard.
;;; This automatically implies all integers with magnitude <= 10000
;;; are standard.  Moreover, all complex numbers with realpart and
;;; imagpart in this range will be standard, too.
;;;
;;; In addition, we get that

(defthm standard-numberp-rationalp
  (implies (and (rationalp x)
		(standard-numberp (numerator x))
		(standard-numberp (denominator x)))
	   (standard-numberp x))
  :hints (("Goal" :use (:instance standardp-times
				  (x (/ (denominator x)))
				  (y (numerator x)))
	   :in-theory (disable standardp-times)))
  :rule-classes nil)

(defthm standard-numberp-rationalp-with-syntaxp
  (implies (and (syntaxp (and (consp x) (eq (car x) 'quote)))
		(rationalp x)
		(standard-numberp (numerator x))
		(standard-numberp (denominator x)))
	   (standard-numberp x))
  :hints (("Goal"
	   :use ((:instance standard-numberp-rationalp)))))

(defthm standardp-complex-2
  (implies (and (complexp x)
		(standard-numberp (realpart x))
		(standard-numberp (imagpart x)))
	   (standard-numberp x))
  :hints (("Goal" :use ((:instance standardp-complex
				   (x (realpart x))
				   (y (imagpart x))))
	   :in-theory (disable standardp-complex)))
  :rule-classes nil)

(defthm standardp-complex-2-with-syntaxp
  (implies (and (syntaxp (and (consp x) (eq (car x) 'quote)))
		(complexp x)
		(standard-numberp (realpart x))
		(standard-numberp (imagpart x)))
	   (standard-numberp x))
  :hints (("Goal" :use ((:instance standardp-complex-2)))))

(local
 (defthm rem-mod-integers-up-to-100
   (implies (and (integerp x) (< 0 x) (<= x 100))
	    (let ((a (truncate x 10))
		  (b (rem x 10)))
	      (and (integerp a) (<= 0 a) (<= a 10)
		   (integerp b) (<= 0 b) (< b 10)
		   (equal (+ (* a 10) b) x))))
   :hints (("Goal"
	    :use ((:instance remainder-theorem-1 (y 10))
		  (:instance remainder-theorem-2 (y 10)))
	    :in-theory (disable remainder-theorem-1
				remainder-theorem-2
				truncate
				rem))
	   ("Subgoal 2''"
	    :use ((:instance truncate-lower-bound (x x) (y 10)))
	    :in-theory (disable truncate truncate-lower-bound)))))

(local
 (defthm standard-numberp-naturals-to-10
   (implies (and (integerp x) (<= 0 x) (<= x 10))
	    (standard-numberp x))
   :hints (("Goal"
	    :cases ((= x 0) (= x 1) (= x 2) (= x 3) (= x 4) (= x 5)
		    (= x 6) (= x 7) (= x 8) (= x 9) (= x 10))))))

(local
 (defthm standard-numberp-naturals-to-100
   (implies (and (integerp x) (<= 0 x) (<= x 100))
	    (standard-numberp x))
   :hints (("Goal"
	    :cases ((= 0 x) (< 0 x)))
	   ("Subgoal 1"
	    :use ((:instance rem-mod-integers-up-to-100)
		  (:instance standardp-plus
			     (x (* (truncate x 10) 10))
			     (y (rem x 10)))
		  (:instance standardp-times
			     (x (truncate x 10))
			     (y 10))
		  (:instance standard-numberp-naturals-to-10
			     (x (truncate x 10)))
		  (:instance standard-numberp-naturals-to-10
			     (x (rem x 10))))
	    :in-theory (disable rem-mod-integers-up-to-100
				standardp-plus
				standardp-times
				standard-numberp-naturals-to-10
				truncate rem)))))

(local
 (defthm rem-mod-integers-up-to-10000
   (implies (and (integerp x) (< 0 x) (<= x 10000))
	    (let ((a (truncate x 100))
		  (b (rem x 100)))
	      (and (integerp a) (<= 0 a) (<= a 100)
		   (integerp b) (<= 0 b) (< b 100)
		   (equal (+ (* a 100) b) x))))
   :hints (("Goal"
	    :use ((:instance remainder-theorem-1 (y 100))
		  (:instance remainder-theorem-2 (y 100)))
	    :in-theory (disable remainder-theorem-1
				remainder-theorem-2
				truncate
				rem))
	   ("Subgoal 2''"
	    :use ((:instance truncate-lower-bound (x x) (y 100)))
	    :in-theory (disable truncate truncate-lower-bound)))))

(local
 (defthm standard-numberp-naturals-to-10000
   (implies (and (integerp x) (<= 0 x) (<= x 10000))
	    (standard-numberp x))
   :hints (("Goal"
	    :cases ((= 0 x) (< 0 x)))
	   ("Subgoal 1"
	    :use ((:instance rem-mod-integers-up-to-10000)
		  (:instance standardp-plus
			     (x (* (truncate x 100) 100))
			     (y (rem x 100)))
		  (:instance standardp-times
			     (x (truncate x 100))
			     (y 100))
		  (:instance standard-numberp-naturals-to-100
			     (x (truncate x 100)))
		  (:instance standard-numberp-naturals-to-100
			     (x (rem x 100))))
	    :in-theory (disable rem-mod-integers-up-to-10000
				standardp-plus
				standardp-times
				standard-numberp-naturals-to-100
				truncate rem)))))

(local
 (defthm rem-mod-integers-up-to-100000000
   (implies (and (integerp x) (< 0 x) (<= x 100000000))
	    (let ((a (truncate x 10000))
		  (b (rem x 10000)))
	      (and (integerp a) (<= 0 a) (<= a 10000)
		   (integerp b) (<= 0 b) (< b 10000)
		   (equal (+ (* a 10000) b) x))))
   :hints (("Goal"
	    :use ((:instance remainder-theorem-1 (y 10000))
		  (:instance remainder-theorem-2 (y 10000)))
	    :in-theory (disable remainder-theorem-1
				remainder-theorem-2
				truncate
				rem))
	   ("Subgoal 2''"
	    :use ((:instance truncate-lower-bound (x x) (y 10000)))
	    :in-theory (disable truncate truncate-lower-bound)))))

(local
 (defthm standard-numberp-naturals-to-100000000
   (implies (and (integerp x) (<= 0 x) (<= x 100000000))
	    (standard-numberp x))
   :hints (("Goal"
	    :cases ((= 0 x) (< 0 x)))
	   ("Subgoal 1"
	    :use ((:instance rem-mod-integers-up-to-100000000)
		  (:instance standardp-plus
			     (x (* (truncate x 10000) 10000))
			     (y (rem x 10000)))
		  (:instance standardp-times
			     (x (truncate x 10000))
			     (y 10000))
		  (:instance standard-numberp-naturals-to-10000
			     (x (truncate x 10000)))
		  (:instance standard-numberp-naturals-to-10000
			     (x (rem x 10000))))
	    :in-theory (disable rem-mod-integers-up-to-100000000
				standardp-plus
				standardp-times
				standard-numberp-naturals-to-10000
				truncate rem)))))

(defthm standard-numberp-integers-to-100000000
  (implies (and (integerp x) (<= -100000000 x) (<= x 100000000))
	   (standard-numberp x))
  :hints (("Goal"
	   :cases ((<= 0 x)))
	  ("Subgoal 2'"
	   :use (:instance standard-numberp-naturals-to-100000000 (x (- x)))))
  :rule-classes nil)

(defthm standard-numberp-rationals-num-demom-100000000
  (implies (and (rationalp x)
		(<= -100000000 (numerator x))
		(<= (numerator x) 100000000)
		(<= (denominator x) 100000000))
	   (standard-numberp x))
  :hints (("Goal"
	   :use ((:instance standard-numberp-rationalp)
		 (:instance standard-numberp-integers-to-100000000
			    (x (numerator x)))
		 (:instance standard-numberp-integers-to-100000000
			    (x (denominator x))))))
  :rule-classes nil)

(defthm standard-numberp-rationals-num-demom-100000000-with-syntaxp
  (implies (and (syntaxp (and (consp x) (eq (car x) 'quote)))
		(rationalp x)
		(<= -100000000 (numerator x))
		(<= (numerator x) 100000000)
		(<= (denominator x) 100000000))
	   (standard-numberp x))
  :hints (("Goal"
	   :by (:instance standard-numberp-rationals-num-demom-100000000))))

;;; Now, we have some theorems about standard-part.  We are careful
;;; here to not assume too much about i-large numbers.  In particular,
;;; we limit our discussion to i-limited numbers.

(defthm standard-part-of-complex-2
  (implies (complexp x)
	   (equal (standard-part x)
		  (complex (standard-part (realpart x))
			   (standard-part (imagpart x)))))
  :hints (("Goal" :use ((:instance standard-part-of-complex
				   (x (realpart x))
				   (y (imagpart x))))
	   :in-theory (disable standard-part-of-complex)))
  :rule-classes nil)

(defthm standard-part-is-idempotent
    (implies (acl2-numberp x)
	     (equal (standard-part (standard-part x))
		    (standard-part x)))
  :hints (("Goal" :cases ((complexp x) (realp x)))
	  ("Subgoal 2" :use ((:instance standard-part-of-complex-2)))))

(defthm standard-part-<-2
  (implies (and (realp x)
		(realp y)
		(< (standard-part x) (standard-part y)))
	   (< x y))
  :hints (("Goal" :by (:instance standard-part-<=)))
  :rule-classes nil)

(defthm standard-part-squeeze
  (implies (and (realp x) (realp y) (realp z)
		(<= x y) (<= y z)
		(= (standard-part x) (standard-part z)))
	   (equal (standard-part y) (standard-part x)))
  :hints (("Goal" :use ((:instance standard-part-<=)
			(:instance standard-part-<= (x y) (y z)))
	   :in-theory (disable standard-part-<=)))
  :rule-classes nil)

;;; We will build a theory for i-small, i-limited, and i-large.

(defthm standard-small-is-zero
  (implies (and (standard-numberp x)
		(i-small x))
	   (equal x 0))
  :rule-classes nil)

;;; Next, we build up a theory about i-small, and how it interacts
;;; with the arithmetic operators.

(defthm i-small-plus
  (implies (and (i-small x) (i-small y))
	   (i-small (+ x y))))

(defthm i-small-uminus
  (equal (i-small (- x))
	 (i-small (fix x))))

(defthm small*limited->small
  (implies (and (i-small x)
		(i-limited y))
	   (i-small (* x y)))
  :hints (("Goal" :in-theory (enable small-are-limited))))

(defthm limited*small->small
  (implies (and (i-limited x)
		(i-small y))
	   (i-small (* x y)))
  :hints (("Goal" :in-theory (enable small-are-limited))))

(defthm i-small-udivide
  (implies (and (i-small x)
		(not (equal x 0)))
	   (i-large (/ x))))

;;; Next, we build up a similar theory about i-limited.  We just need
;;; the results about arithmetic operators for now.  We will use the
;;; fact (axiom) that each i-limited number can be written as the sum
;;; of a standard and i-close number.

(defthm limited-standard-part
  (implies (i-limited x)
	   (i-limited (standard-part x))))

(defun non-standard-part (x)
  (- x (standard-part x)))

(defthm i-small-non-standard-part
  (implies (i-limited x)
	   (i-small (non-standard-part x))))

(local
 (defthm i-limited-plus-lemma
   (implies (and (standard-numberp x)
		 (i-small x-eps)
		 (standard-numberp y)
		 (i-small y-eps))
	   (i-limited (+ x x-eps y y-eps)))
   :hints (("Goal"
	    :use ((:instance standard+small->i-limited
			     (x (+ x y))
			     (eps (+ x-eps y-eps))))
	    :in-theory (disable standard+small->i-limited)))))

(defthm i-limited-plus
  (implies (and (i-limited x)
		(i-limited y))
	   (i-limited (+ x y)))
  :hints (("Goal"
	   :use ((:instance i-limited-plus-lemma
			    (x (standard-part x))
			    (x-eps (non-standard-part x))
			    (y (standard-part y))
			    (y-eps (non-standard-part y))))
	   :in-theory (disable i-limited-plus-lemma))))

(local
 (defthm i-limited-times-lemma
   (implies (and (standard-numberp x)
		 (i-small x-eps)
		 (standard-numberp y)
		 (i-small y-eps))
	    (i-limited (* (+ x x-eps) (+ y y-eps))))
   :hints (("Goal"
	    :use ((:instance standard+small->i-limited
			     (x (* x y))
			     (eps (+ (* x y-eps)
				     (* y x-eps)
				     (* x-eps y-eps)))))
	    :in-theory (enable-disable (standards-are-limited)
				       (standard+small->i-limited
					i-small))))))

(defthm i-limited-times
  (implies (and (i-limited x)
		(i-limited y))
	   (i-limited (* x y)))
  :hints (("Goal"
	   :use ((:instance i-limited-times-lemma
			    (x (standard-part x))
			    (x-eps (non-standard-part x))
			    (y (standard-part y))
			    (y-eps (non-standard-part y))))
	   :in-theory (disable i-limited-times-lemma))))

(defthm i-limited-udivide
  (implies (and (i-limited x)
		(not (i-small x)))
	   (i-limited (/ x))))

;;; Next, we can build a theory about i-large numbers.  It would be
;;; nice to be able to say something about i-large-plus, but this is
;;; not possible.  Consider "x + -x", for example.

(defthm limited+large->large
  (implies (and (i-limited x)
		(i-large y))
	   (i-large (+ x y)))
  :hints (("Goal"
	   :cases ((i-limited (+ x y))))
	  ("Subgoal 1"
	   :use ((:instance i-limited-plus (x (+ x y)) (y (- x))))
	   :in-theory (disable i-limited-plus))))

(defthm large+limited->large
  (implies (and (i-large x)
		(i-limited y))
	   (i-large (+ x y)))
  :hints (("Goal"
	   :use ((:instance limited+large->large (x y) (y x)))
	   :in-theory (disable limited+large->large i-large))))

(defthm i-large-uminus
  (equal (i-large (- x))
	 (i-large x)))

(defthm limited*large->large
  (implies (and (acl2-numberp x)
		(not (i-small x))
		(i-large y))
	   (i-large (* x y)))
  :hints (("Goal" :in-theory (enable small-are-limited))))

(defthm large*limited->large
  (implies (and (i-large x)
		(acl2-numberp y)
		(not (i-small y)))
	   (i-large (* x y)))
  :hints (("Goal" :in-theory (enable small-are-limited))))

(defthm i-large-udivide
  (implies (i-large x)
	   (i-small (/ x))))

;;; Now, we consider some theorems about i-close.

(defthm i-close-reflexive
  (implies (acl2-numberp x)
	   (i-close x x)))

(defthm i-close-symmetric
   (implies (i-close x y)
	    (i-close y x))
   :hints (("Goal''"
	    :use ((:theorem (equal (+ (- x) y) (- (+ x (- y))))))
	    :in-theory (disable DISTRIBUTIVITY-OF-MINUS-OVER-+))))

(defthm i-close-transitive
  (implies (and (i-close x y)
		(i-close y z))
	   (i-close x z))
  :hints (("Goal"
	   :use ((:instance standard-part-of-plus
			    (x (- x y))
			    (y (- y z))))
	   :in-theory (disable standard-part-of-plus
			       i-close-reflexive
			       i-close-symmetric))))

(defthm i-close-to-small-sum
    (implies (and (acl2-numberp x)
		  (standardp x)
		  (i-small eps))
	     (i-close x (+ x eps))))

(defthm i-close-small
  (implies (and (i-small x)
		(i-close x y))
	   (i-small y))
  :hints (("Goal"
	   :use ((:instance i-small-plus (x (- x y)) (y (- x))))
	   :in-theory (disable i-small-plus))))

(defthm i-close-small-2
  (implies (and (i-small y)
		(i-close x y))
	   (i-small x))
  :hints (("Goal"
	   :use ((:instance i-close-small (x y) (y x))
		 (:instance i-small-uminus (x (- x y))))
	   :in-theory (disable i-close-small i-small i-small-uminus))))

(defthm i-close-limited
  (implies (and (i-limited x)
		(i-close x y))
	   (i-limited y))
  :hints (("Goal"
	   :use ((:instance i-limited-plus (x (- x y)) (y (- x))))
	   :in-theory (disable i-large i-small i-limited-plus
                               ;; change for v2-6:
                               limited+large->large))))

(defthm i-close-limited-2
  (implies (and (i-limited y)
		(i-close x y))
	   (i-limited x))
  :hints (("Goal"
	   :use ((:instance i-close-limited (x y) (y x)))
	   :in-theory (disable i-close-limited i-close i-large))))

(defthm i-close-large
  (implies (and (i-large x)
		(i-close x y))
	   (i-large y))
  :hints (("Goal"
	   :use ((:instance limited+large->large (x (- x y)) (y (- x))))
	   :in-theory (disable i-large limited+large->large))))

(defthm i-close-large-2
  (implies (and (i-large y)
		(i-close x y))
	   (i-large x))
  :hints (("Goal"
	   :use ((:instance i-close-large (x y) (y x)))
	   :in-theory (disable i-close-large i-close i-large))))

(defthm close-x-y->same-standard-part
    (implies (and (i-close x y)
		  (i-limited x))
	     (equal (equal (standard-part x) (standard-part y))
		    t))
  :hints (("Goal"
	   :use ((:instance i-close-limited))
	   :in-theory (enable-disable (i-close i-small)
				      (i-close-limited)))))

(defthm standard-part-close
  (implies (i-limited x)
	   (i-close (standard-part x) x))
  :hints (("Goal"
	   :use ((:instance i-small-non-standard-part))
	   :in-theory (enable-disable (i-close i-small)
				      (i-small-non-standard-part)))))


;;; Now, we consider the special theory of i-small, i-limited, and
;;; i-large, when dealing with real numbers.  In particular, we want
;;; to formalize the intuition that i-small < i-limited < i-large.

(local
 (defthm small-<-non-small-lemma
   (implies (and (i-small x)
		 (realp x)
		 (<= 0 x)
		 (not (i-small y))
		 (realp y)
		 (<= 0 y))
	    (< x y))
   :hints (("Goal"
	    :use ((:instance standard-part-<-2))))))

(defthm small-<-non-small
  (implies (and (i-small x)
		(realp x)
		(not (i-small y))
		(realp y))
	   (< (abs x) (abs y)))
  :hints (("Goal"
	   :use ((:instance small-<-non-small-lemma
			    (x (abs x))
			    (y (abs y))))
	   :in-theory (disable small-<-non-small-lemma))))

(local
 (defthm small-if-<-small-lemma
   (implies (and (i-small x)
		 (realp x)
		 (realp y)
		 (<= 0 y)
		 (<= y x))
	    (i-small y))
   :hints (("Goal"
	    :use ((:instance standard-part-squeeze
			     (x 0)
			     (y y)
			     (z x)))
	    :in-theory (disable small-<-non-small-lemma
				small-<-non-small)))))

(defthm small-if-<-small
  (implies (and (i-small x)
		(realp x)
		(realp y)
		(<= (abs y) (abs x)))
	   (i-small y))
  :hints (("Goal"
	   :use ((:instance small-if-<-small-lemma
			    (x (abs x))
			    (y (abs y))))
	   :in-theory '(abs fix i-small-uminus))))

(local
 (defthm large->-non-large-lemma
   (implies (and (i-large x)
		 (realp x)
		 (<= 0 x)
		 (not (i-large y))
		 (realp y)
		 (<= 0 y))
	    (> x y))
   :hints (("Goal"
	    :use ((:instance standard-part-<-2
			     (x (/ x))
			     (y (/ y))))
	    :in-theory (disable small-<-non-small-lemma)))))

(defthm large->-non-large
   (implies (and (i-large x)
		 (realp x)
		 (not (i-large y))
		 (realp y))
	    (> (abs x) (abs y)))
  :hints (("Goal"
	   :use ((:instance large->-non-large-lemma
			    (x (abs x))
			    (y (abs y))))
	   :in-theory '(abs fix i-large-uminus))))

(local
 (defthm large-if->-large-lemma
   (implies (and (i-large x)
		 (realp x)
		 (realp y)
		 (<= 0 x)
		 (<= x y))
	    (i-large y))
   :hints (("Goal"
	    :use ((:instance large->-non-large-lemma))
	    :in-theory (disable i-large
				standards-are-limited
				i-close-large i-close-large-2
				i-close-limited i-close-limited-2
				large->-non-large-lemma)))))

(defthm large-if->-large
  (implies (and (i-large x)
		(realp x)
		(realp y)
		(<= (abs x) (abs y)))
	   (i-large y))
   :hints (("Goal"
	    :use ((:instance large-if->-large-lemma
			     (x (abs x))
			     (y (abs y))))
	    :in-theory '(abs fix i-large-uminus))))

(defthm limited-squeeze
    (implies (and (realp a) (realp b) (realp x)
		  (<= a x) (<= x b)
		  (i-limited a) (i-limited b))
	     (i-limited x))
  :hints (("Goal"
	   :use ((:instance large-if->-large
			    (x x)
			    (y a))
		 (:instance large-if->-large
			    (x x)
			    (y b)))
	   :in-theory (enable-disable (abs) (large-if->-large)))))

(in-theory (disable nsa-theory))

;;; Now we tackle the theory of non-standard complex number

;;; The first theorem simply states how to take the inverse of a
;;; complex number.

(encapsulate
 ()

 ;; A most useful lemma allows as to rewrite a complex number in the
 ;; form a + bi where a and b are real.

 (local
  (defthm lemma-1
    (implies (and (realp r) (realp s))
	     (equal (complex r s)
		    (+ r (* #c(0 1) s))))
    :hints (("Goal" :by (:instance complex-definition (x r) (y s))))))

 ;; With that algebraic trick, we can now consider the product of a
 ;; complex number and its conjugate.  The result is the square of the
 ;; length of the complex vector, of course.  We prove a slightly more
 ;; powerful lemma here, as we also multiply both sides of the
 ;; equation by an arbitrary number.

 (local
  (defthm lemma-2
   (implies (and (realp r) (realp s) (acl2-numberp x))
	    (equal (* (complex r s)
		      (complex r (- s))
		      x)
		   (* (+ (* r r) (* s s))
		      x)))))

 ;; We now establish that if you multiply a complex number by its
 ;; conjugate divided by the square of the number's length, you get
 ;; 1.  I.e., this establishes what the inverse of a complex number
 ;; is, but only indirectly.

 (local
  (defthm lemma-3
   (implies (and (realp r) (realp s) (or (not (= r 0)) (not (= s 0))))
	    (equal (* (complex r s)
		      (/ (complex r (- s))
			 (+ (* r r) (* s s))))
		   1))
   :hints (("Goal" :in-theory (disable lemma-1)))))

 ;; We now restate the theorem so that the inverse is found directly.

 (local
  (defthm lemma-4
   (implies (and (realp r) (realp s) (or (not (= r 0)) (not (= s 0))))
	    (equal (/ (complex r s))
		   (/ (complex r (- s))
		      (+ (* r r) (* s s)))))
   :hints (("Goal"
	    :use ((:instance equal-/
			     (x (complex r s))
			     (y (/ (complex r (- s))
				   (+ (* r r) (* s s))))))
	    :in-theory (disable lemma-1 lemma-2 equal-/)))))

 ;; Now, we want to move the quotient up into the complex number
 ;; itself.  So, we show how divisions by real numbers affect complex
 ;; numbers.

 (local
  (defthm lemma-5
    (implies (and (realp r) (realp s) (realp x))
	     (equal (complex (/ r x) (/ s x))
		    (/ (complex r s) x)))))

 ;; This gives us a new restatement of the theorem.

 (local
  (defthm lemma-6
    (implies (and (realp r) (realp s) (or (not (= r 0)) (not (= s 0))))
	     (equal (/ (complex r s))
		    (complex (/ r (+ (* r r) (* s s)))
			     (/ (- s) (+ (* r r) (* s s))))))
    :hints (("Goal"
	     :use ((:instance lemma-5
			      (r r)
			      (s (- s))
			      (x (+ (* r r) (* s s)))))
	     :in-theory (disable lemma-1 lemma-5)))))

 ;; The only thing left is to consider complex numbers that are also
 ;; real numbers.  There is no real problem, even for the case when
 ;; the number is zero (because in ACL2 1/0 == 0).

 (defthm /-complex
   (implies (and (realp r) (realp s))
	    (equal (/ (complex r s))
		   (complex (/ r (+ (* r r) (* s s)))
			    (/ (- s) (+ (* r r) (* s s))))))
   :hints (("Goal"
	    :cases ((or (not (= r 0)) (not (= s 0))))
	    :in-theory (disable lemma-1 lemma-2 lemma-3 lemma-4))))

 )

;;; This is a very useful rewriting of complex inverses, when the
;;; number involved is not explicitly written as (complex a b).

(defthm /-complex-2
  (implies (complexp x)
	   (equal (/ x)
		  (let ((r (realpart x))
			(s (imagpart x)))
		    (complex (/ r (+ (* r r) (* s s)))
			     (/ (- s) (+ (* r r) (* s s)))))))
  :hints (("Goal" :in-theory (disable equal-/))))
(in-theory (disable /-complex-2))


;;; Now we can begin the development of non-standard analysis with
;;; complex numbers.  First of all, we get a clean characterization of
;;; when a complex number is small.

(defthm complex-small
  (implies (complexp x)
	   (equal (i-small x)
		  (and (i-small (realpart x))
		       (i-small (imagpart x)))))
  :hints (("Goal" :in-theory (enable i-small))))

;;; We want to establish a similar rule about when a complex number is
;;; limited or large.

(encapsulate
 ()

 (local
  (in-theory (disable limited-squeeze)))

 ;; First, we show that if a real number is infinitesimal its square
 ;; is also infinitesimal.  We restrict our attention to
 ;; infinitesimals of the form 1/x, because those are the terms that
 ;; will be popping up next.

 (local
  (defthm lemma-1
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0))
     (equal (standard-part (/ (* r r))) 0))
    :hints (("Goal"
	     :cases ((not (i-limited (/ r)))))
	    ("Subgoal 2"
	     :in-theory (enable i-large)
	     )
	    ("Subgoal 1"
	     :use ((:instance small-are-limited (x (/ r))))
	     :in-theory (enable-disable (i-small)
					(small-are-limited))))))

 ;; Next is an important and trivial lemma.  I don't know why the
 ;; linear rewriting rules don't take care of this.  In any case, for
 ;; positive r and s, 1/(r+s) is less than 1/r...duh.

 (local
  (defthm lemma-2
    (implies
     (and (realp r)
	  (< 0 r)
	  (realp s)
	  (<= 0 s))
     (<= (/ (+ r s))
	 (/ r)))))

 ;; So now we see that if 1/r is a positive infinitesimal, so is
 ;; 1/r^2, and therefore so is 1/(r^2+s^2) for any real s!

 (local
  (defthm lemma-3
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0)
	  (< 0 r)
	  (realp s))
     (equal (standard-part (/ (+ (* r r) (* s s)))) 0))
    :hints (("goal"
	     :use ((:instance lemma-1)
		   (:instance standard-part-<=
			      (x 0)
			      (y (/ (+ (* r r) (* s s)))))
		   (:instance standard-part-<=
			      (x (/ (+ (* r r) (* s s))))
			      (y (/ (* r r)))))
	     :in-theory '(nonnegative-product lemma-2)))))

 ;; Of course, the theorem above also holds for negative infinitesimal
 ;; 1/r.

 (local
  (defthm lemma-4
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0)
	  (< r 0)
	  (realp s))
     (equal (standard-part (/ (+ (* r r) (* s s)))) 0))
    :hints (("goal"
	     :use ((:instance lemma-3 (r (- r))))
	     :in-theory (disable lemma-3)))))

 ;; So, the theorem holds for any non-zero infinitesimal 1/r.

 (local
  (defthm lemma-5
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0)
	  (not (equal r 0))
	  (realp s))
     (equal (standard-part (/ (+ (* r r) (* s s)))) 0))
    :hints (("goal"
	     :cases ((< 0 r) (< r 0))))))

 ;; When 1/s is not infinetsimal, we can multiply both sides of the
 ;; equation above by s, and the result still holds.

 (local
  (defthm lemma-7
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0)
	  (not (equal r 0))
	  (realp s)
	  (not (equal (standard-part (/ s)) 0)))
     (equal (standard-part (* s (/ (+ (* r r) (* s s))))) 0))
    :hints (("Goal"
	     :use ((:instance limited*small->small
			      (x s)
			      (y (/ (+ (* r r) (* s s))))))
	     :in-theory (enable-disable (i-small i-large)
					(limited*small->small))))))

 ;; The same holds when 1/r is not infinitesimal, so we can multiply
 ;; both sides by r.  We consider the cases when x is positive and
 ;; negative separately.  First for positive r....

 (local
  (defthm lemma-9
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0)
	  (< 0 r)
	  (realp s))
     (equal (standard-part (* r (/ (+ (* r r) (* s s))))) 0))
    :hints (("goal"
	     :use ((:instance standard-part-<=
			      (x 0)
			      (y (* r (/ (+ (* r r) (* s s))))))
		   (:instance standard-part-<=
			      (x (* r (/ (+ (* r r) (* s s)))))
			      (y (/ r))))))))

 ;; ...then for negative r...

 (local
  (defthm lemma-10
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0)
	  (< r 0)
	  (realp s))
     (equal (standard-part (* r (/ (+ (* r r) (* s s))))) 0))
    :hints (("goal"
	     :use ((:instance standard-part-<=
			      (x (* r (/ (+ (* r r) (* s s)))))
			      (y 0))
		   (:instance standard-part-<=
			      (x (/ r))
			      (y (* r (/ (+ (* r r) (* s s)))))))))))

 ;; ... and then we combine the proofs for all possible r.

 (local
  (defthm lemma-11
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0)
	  (realp s))
     (equal (standard-part (* r (/ (+ (* r r) (* s s))))) 0))
    :hints (("goal"
	     :cases ((< 0 r) (< r 0))))))

 ;; In summary, we have that if 1/r is infinitesimal, so is r/(r^2+s^2).

 (local
  (defthm lemma-12
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0)
	  (realp s))
     (equal (standard-part (* r (/ (+ (* s s) (* r r))))) 0))))

 ;; And, we have that if 1/r is infinitesimal, so is s/(r^2+s^2).

 (local
  (defthm lemma-13
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0)
	  (not (equal r 0))
	  (realp s))
     (equal (standard-part (* s (/ (+ (* r r) (* s s))))) 0))
    :hints (("goal"
	     :cases ((equal (standard-part (/ s)) 0))))))

 ;; We prove the case for s^2+r^2 as well as r^2+s^2

 (local
  (defthm lemma-14
    (implies
     (and (realp r)
	  (equal (standard-part (/ r)) 0)
	  (not (equal r 0))
	  (realp s))
     (equal (standard-part (* s (/ (+ (* s s) (* r r))))) 0))))

 ;; And so we get the first main theorem.  If either r or s is large,
 ;; so is a+bi.

 (defthm complex-large-1
   (implies (complexp x)
	    (implies (or (i-large (realpart x))
			 (i-large (imagpart x)))
		     (i-large x)))
   :hints (("Goal"
	    :in-theory (enable i-small i-large))))

 ;; Likewise, if a+bi is limited, both a and b must be limited.

 (defthm complex-limited-2
   (implies (and (complexp x)
		 (i-limited x))
	    (and (i-limited (realpart x))
		 (i-limited (imagpart x))))
   :rule-classes nil)
 )

;;; Simple theorems say that the standard-part of i is i, and the standard part
;;; of -i is -i.  But we do not need to prove these; in fact ACL2 "computes"
;;; with standard-part when forming the relevant terms!

;;; Moreover, i is limited and not small.

(defthm limited-not-small-i
  (and (not (i-large #c(0 1)))
       (not (i-small #c(0 1))))
  :hints (("Goal" :in-theory (enable i-small))))

;;; Now we can prove different versions of the main theorems, namely
;;; that when a and b are limited, so is a+bi.

(defthm complex-limited-1
  (implies (and (complexp x)
		(i-limited (realpart x))
		(i-limited (imagpart x)))
	   (i-limited x))
  :hints (("Goal"
	   :in-theory (disable i-large))
	  ("Subgoal 1"
	   :use ((:instance complex-definition
			    (x r)
			    (y s))
		 (:instance i-limited-plus
			    (x r)
			    (y (* #c( 0 1) s)))
		 (:instance i-limited-times
			    (x #c( 0 1))
			    (y s)))
	   :in-theory (disable i-large i-limited-plus
			       i-limited-times)))
  :rule-classes nil)

;;; And finally, if a+bi is large, one of a or b must be large.

(defthm complex-large-2
  (implies (complexp x)
	   (implies (i-large x)
		    (or (i-large (realpart x))
			(i-large (imagpart x)))))
   :hints (("Goal"
	    :use ((:instance complex-limited-1)
		  (:instance small-are-limited)
		  (:instance small-are-limited (x (realpart x)))
		  (:instance small-are-limited (x (imagpart x))))
	    :in-theory nil))
   :rule-classes nil)


