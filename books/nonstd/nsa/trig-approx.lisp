;; This book develops an epsilon approximation scheme for the sine and cosine
;; functions.

(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))
(local (include-book "arithmetic/abs" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(include-book "trig")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; First, we prove that the Taylor approximation to sine and cosine is
;; valid.  One of these (cosine) is actually proved in trig.lisp.

(encapsulate
 ()

 ;; The lemma taylorish-sin-valid inexplicably proves the result only
 ;; for when counter equals 0.  Unfortunately, the Taylor series of
 ;; sin(x) starts with counter equal to 1!  So, we figure out here how
 ;; to step counter by one.

 (local
  (defthm lemma-1
    (implies (and (integerp counter)
		  (nat-even-p counter)
		  (<= 0 counter)
		  (integerp nterms))
	     (equal (sumlist (taylorish-sin-list nterms counter sign x))
		    (sumlist (taylorish-sin-list (1- nterms) (1+ counter)
						 sign x))))
    :hints (("Goal" :do-not-induct t
	     :expand ((taylorish-sin-list nterms counter sign x))))))

 ;; Now, it's easy to prove that the Taylor approximation for sin(x)
 ;; gives the right results -- but notice we go up to N-1 not N below!

 (defthm taylor-sin-valid
   (implies (standard-numberp x)
	    (equal (acl2-sine x)
		   (standard-part (sumlist (taylor-sincos-list
					    (1- (i-large-integer)) 1 1
					    x)))))
   :hints (("Goal"
	    :in-theory (enable taylorish-sin-valid)))))

;; That the taylor approximation works for cos(x) was proved earlier.

(defthm taylor-cos-valid
  (implies (standard-numberp x)
	   (equal (acl2-cosine x)
		  (standard-part (sumlist (taylor-sincos-list
					   (i-large-integer) 0 1
					   x)))))
  :hints (("Goal"
	   :in-theory (enable taylorish-cos-valid))))

;; Now, we will be splitting up taylor-sincos-list's into a limited
;; part and a (non-infinitesimal) small part, based on the epsilon
;; precision argument.  We want to claim that both parts of the split
;; are limited.  For the first part, we need to show that if nterms is
;; limited, then so is the sumlist of taylor-sincos-list upto nterms.
;; For the second, we'll need the fact that taylor-sincos-list is an
;; alternating sequence "after a while".

;; The first part is easy:  taylor-sincos is limited up for limited
;; arguments.  (The standard-numberp on sign is because sign is
;; changed during the recursion, even though it's not part of the
;; measure, so it doesn't go down!)

(defthm limited-taylor-sincos-list
  (implies (and (i-limited nterms)
		(i-limited counter)
		(standard-numberp sign)
		(i-limited x))
	   (i-limited (sumlist (taylor-sincos-list nterms counter sign x)))))

;; For the second part, we need to show that taylor-sincos-list
;; satisfies the alternating sequence property.  There are two
;; properties.  First, it must alternate in sign.  Second, it must
;; including successively decreasing terms.  The first property was
;; proved in trig.lisp:

(defthm alternating-sequence-1-p-taylor-sincos
  (implies (and (realp sign)
		(realp x))
	   (alternating-sequence-1-p (taylor-sincos-list nterms
							 counter
							 sign
							 x))))

;; For the second property, we need to pick a value of counter that is
;; far enough out on the sequence that 1/counter! dwarfs x^counter.
;; Picking counter >= x satisfies that property.

(defun taylor-sin-term (sign counter x)
  (* sign
     (expt x counter)
     (/ (factorial counter))))

;; One silly thing is that alternating series need to be treated
;; especially when they are composed entirely of zeros.  Here, we
;; prove that a Taylor term for sine (or cosine) is zero only when x
;; is zero.

(defthm taylor-sin-term-non-zero
  (implies (and (realp x)    (not (equal x 0))
		(realp sign) (not (equal sign 0)))
	   (equal (equal (taylor-sin-term sign counter x) 0)
		  nil)))

;; So now, we can talk about the absolute value of a Taylor term.  The
;; sign (of the sign) is irrelevant.

(defthm abs-taylor-sin-term-sign
  (equal (abs (taylor-sin-term (- sign) counter x))
	 (abs (taylor-sin-term sign counter x)))
  :hints (("Goal" :in-theory (enable abs))))

;; From this, we should be able to prove that subsequent terms in the
;; Taylor approximation become smaller.

(encapsulate
 ()

 ;; First, we need some silly algebra.

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (< 0 x)
		  (realp c)
		  (< x c))
	     (< (* x (/ c)) 1))))

 ;; More algebra!

 (local
  (defthm lemma-2
    (implies (and (realp x)
		  (< 0 x)
		  (realp c)
		  (< x c))
	     (< (* x (/ (+ 1 c))) 1))
    :hints (("Goal"
	     :use ((:instance lemma-1 (c (+ 1 c))))
	     :in-theory (disable lemma-1)))))

 ;; And even more algebra!

 (local
  (defthm lemma-3
    (implies (and (realp x)
		  (< 0 x)
		  (realp c)
		  (< x c)
		  (realp e)
		  (< 0 e))
	     (< (* x (/ (+ 1 c)) e) e))))

 ;; Now, we have that successive terms decrease in magnitude, but only
 ;; if we know that counter is positive.

 (local
  (defthm abs-taylor-counter+1-<-counter-lemma
    (implies (and (realp x)          (not (equal x 0))
		  (realp sign)       (not (equal sign 0))
		  (integerp counter) (<= 0 counter)
		  (< (abs x) counter))
	     (< (abs (taylor-sin-term sign (+ 1 counter) x))
		(abs (taylor-sin-term sign counter x))))))

 ;; Of course, we *should* know that counter is positive, since it's
 ;; at least |x| !

 (local
  (defthm lemma-4
    (implies (and (realp x)
		  (integerp counter)
		  (< (abs x) counter))
	     (<= 0 counter))
    :hints (("Goal"
	     :in-theory (enable abs)))))

 ;; And so, we get that successive terms decrease.

 (defthm abs-taylor-counter+1-<-counter
   (implies (and (realp x)          (not (equal x 0))
		 (realp sign)       (not (equal sign 0))
		 (integerp counter)
		 (< (abs x) counter))
	    (< (abs (taylor-sin-term sign (+ 1 counter) x))
	       (abs (taylor-sin-term sign counter x))))
   :hints (("Goal"
	    :cases ((<= 0 counter)))
	   ("Subgoal 2"
	    :use ((:instance lemma-4))
	    :in-theory nil)))
 )

;; From which its obvious that the sequence two terms at a time is
;; also decreasing....duh.

(defthm abs-taylor-counter+2-<-counter
  (implies (and (realp x)          (not (equal x 0))
		(realp sign)       (not (equal sign 0))
		(integerp counter)
		(< (abs x) counter))
	   (< (abs (taylor-sin-term sign (+ 2 counter) x))
	      (abs (taylor-sin-term sign counter x))))
  :hints (("Goal"
	   :use ((:instance abs-taylor-counter+1-<-counter)
		 (:instance abs-taylor-counter+1-<-counter
			    (counter (+ 1 counter))))
	   :in-theory (disable abs-taylor-counter+1-<-counter
			       taylor-sin-term))))

;; Now here's an obvious rule.  A Taylor-sin-term of sin(0) or cos(0)
;; is equal to 0 (except for the 0^0 term :-)

(defthm taylor-sin-term-x=0
  (implies (and (integerp counter)
		(not (equal counter 0)))
	   (equal (taylor-sin-term sign counter 0)
		  0)))

;; If the sign is zero, then the Taylor term is zero -- of course,
;; that should never happen.

(defthm taylor-sin-term-sign=0
  (equal (taylor-sin-term 0 counter x)
	 0))

;; Now here is an alternate definition of the taylor-sincos-list.
;; This one uses taylor-sin-term instead of computing the value right
;; there in the recursion.  That way, we can disable the first term
;; and reason about it separately.

(defthm taylor-sincos-list-alternate-definition
  (equal (taylor-sincos-list nterms counter sign x)
	 (if (or (zp nterms)
		 (not (integerp counter))
		 (< counter 0))
	     nil
	   (cons (taylor-sin-term sign counter x)
		 (taylor-sincos-list (nfix (- nterms 2))
				     (+ counter 2)
				     (- sign)
				     x))))
  :rule-classes :definition)

(in-theory (disable taylor-sin-term))
(in-theory (disable (:definition taylor-sincos-list)))

;; And speaking of which, the first term of a Taylor list is just
;; taylor-sin-term

(defthm car-taylor-sincos-list-3
  (implies (taylor-sincos-list nterms counter sign x)
	   (equal (car (taylor-sincos-list nterms counter sign x))
		  (taylor-sin-term sign counter x)))
  :hints (("Goal"
	   :use ((:instance (:definition
			     taylor-sincos-list-alternate-definition)))
	   :in-theory (disable taylor-sincos-list-alternate-definition
			       car-taylor-sincos-list
			       car-taylor-sincos-list-2))))

;; So now, for non-zero values of x, we get that the Taylor list
;; satisfies the second alternating property, i.e., successive terms
;; decrease.

(defthm alternating-sequence-2-p-taylor-sincos-x-<>-0
  (implies (and (realp x)
		(not (equal x 0))
		(realp sign)
		(not (equal sign 0))
		(integerp counter)
		(< (abs x) counter))
	   (alternating-sequence-2-p (taylor-sincos-list nterms
							 counter
							 sign
							 x)))
  :hints (("Goal"
	   :induct (taylor-sincos-list nterms counter sign x))))

;; Same thing holds when x=0 but sign isn't, since all the terms are
;; zero.  We probably don't need sign!=0 hypothesis!

(defthm alternating-sequence-2-p-taylor-sincos-x-=-0
  (implies (and (realp x)
		(equal x 0)
		(realp sign)
		(not (equal sign 0))
		(integerp counter)
		(< (abs x) counter))
	   (alternating-sequence-2-p (taylor-sincos-list nterms
							 counter
							 sign
							 x)))
  :hints (("Goal"
	   :induct (taylor-sincos-list nterms counter sign x))))

;; Ditto when sign is zero.

(defthm alternating-sequence-2-p-taylor-sincos-sign-=-0
  (implies (and (realp x)
		(realp sign)
		(equal sign 0)
		(integerp counter)
		(< (abs x) counter))
	   (alternating-sequence-2-p (taylor-sincos-list nterms
							 counter
							 sign
							 x)))
  :hints (("Goal"
	   :induct (taylor-sincos-list nterms counter sign x))))

;; And therefore, taylor-sincos-list satisfies the second alternating
;; sequence property.

(defthm alternating-sequence-2-p-taylor-sincos
  (implies (and (realp x)
		(realp sign)
		(integerp counter)
		(< (abs x) counter))
	   (alternating-sequence-2-p (taylor-sincos-list nterms
							 counter
							 sign
							 x)))
  :hints (("Goal"
	   :use ((:instance alternating-sequence-2-p-taylor-sincos-x-<>-0)
		 (:instance alternating-sequence-2-p-taylor-sincos-x-=-0)
		 (:instance alternating-sequence-2-p-taylor-sincos-sign-=-0))
	   :in-theory nil)))

;; What that means is that taylor-sincos-list is an alternating sequence.

(defthm alternating-sequence-p-taylor-sincos
  (implies (and (realp x)
		(realp sign)
		(integerp counter)
		(< (abs x) counter))
	   (alternating-sequence-2-p (taylor-sincos-list nterms
							 counter
							 sign
							 x))))

;; This rule is just needed by ACL2 occasionally to know when
;; taylor-sincos-list is non-nil.

(defthm not-nilp-taylor-sincos-list
  (implies (and (integerp nterms)
		(< 0 nterms)
		(integerp counter)
		(<= 0 counter))
	   (taylor-sincos-list nterms counter sign x))
  :hints (("Goal" :in-theory (enable taylor-sincos-list))))

;; So now, we want to prove that the sum of the alternating series
;; part is no bigger than its first element.

(encapsulate
 ()

 ;; Here's a simple lemma that lets us know counter is positive when
 ;; |x| < counter.

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (integerp counter)
		  (< (abs x) counter))
	     (<= 0 counter))
    :hints (("Goal"
	     :in-theory (enable abs)))))

 ;; Now, as long as we have a valid Taylor sum list, we can conclude
 ;; that its bounded above by its first element.

 (defthm sumlist-taylor-sincos-list-bound-lemma
   (implies (and (realp x)
		 (realp sign)
		 (integerp counter)
		 (< (abs x) counter)
		 (integerp nterms)
		 (< 0 nterms))
	    (<= (abs (sumlist (taylor-sincos-list nterms counter sign x)))
		(abs (taylor-sin-term sign counter x))))
   :hints (("Goal"
	    :use ((:instance sumlist-alternating-sequence
			     (x (taylor-sincos-list nterms counter sign x))))
	    :in-theory (disable sumlist-alternating-sequence))
	   ("Goal'''"
	    :use ((:instance lemma-1)
		  (:instance not-nilp-taylor-sincos-list)
		  (:instance car-taylor-sincos-list-3))
	    :in-theory nil)))
 )

;; But even better, we can get rid of some of the hypothesis, like any
;; requirements on the number of terms -- because when the list is
;; non-existent, its sumlist is zero.

(defthm sumlist-taylor-sincos-list-bound
  (implies (and (realp x)
		(realp sign)
		(integerp counter)
		(< (abs x) counter))
	   (<= (abs (sumlist (taylor-sincos-list nterms counter sign x)))
	       (abs (taylor-sin-term sign counter x))))
  :hints (("Goal"
	   :cases ((and (integerp nterms) (< 0 nterms))))))

;; So, now what is the absolute value of a Taylor sin term.  We only
;; care about values when sign is 1 or -1.  Also, we would like a nice
;; recurrence relation not depending on expt.  This does the trick:

(defun abs-taylor-sin-term (counter x)
  (if (zp counter)
      1
    (* (abs x) (/ counter)
       (abs-taylor-sin-term (1- counter) x))))

;; But first we have to prove that....

(encapsulate
 ()

 ;; We don't like recursing according to expt, so we enable n-expt
 ;; which has an easier recursion scheme.

 (local (in-theory (enable n-expt-expt)))

 ;; We observe that n-expt is always real for real values of x.

 (local
  (defthm realp-n-expt
    (implies (realp x)
	     (realp (n-expt x n)))))

 ;; Now, we see that abs-taylor-sin-term really is the absolute value
 ;; of the Taylor sin term, but only when sign is 1 or -1.

 (defthm abs-taylor-sin-term-works
   (implies (and (realp x)
		 (integerp counter)
		 (<= 0 counter)
		 (or (= sign 1) (= sign -1)))
	    (equal (abs (taylor-sin-term sign counter x))
		   (abs-taylor-sin-term counter x)))
   :hints (("Goal"
	    :induct (abs-taylor-sin-term counter x))
	   ("Subgoal *1/2.2''"
	    :expand ((taylor-sin-term 1 counter x)
		     (taylor-sin-term 1 (+ -1 counter) x)))
	   ("Subgoal *1/2.2'''"
	    :expand ((factorial counter)))
	   ("Subgoal *1/2.1'''"
	    :expand ((taylor-sin-term 1 counter x)
		     (taylor-sin-term 1 (+ -1 counter) x)))
	   ("Subgoal *1/2.1'4'"
	    :expand ((factorial counter)))
	   ("Subgoal *1/1.2"
	    :expand ((taylor-sin-term 1 0 x)))
	   ("Subgoal *1/1.1"
	    :expand ((taylor-sin-term 1 0 x)))
	   ))
 )

;; Since abs-taylor-sin-term is an upper bound on the sumlist of the
;; remainder of a Taylor series -- i.e., on the error term -- we want
;; to make it as small as possible.  To do this, we use the same trick
;; as above.  Split abs-taylor-sin-term into two components.  The
;; first is bounded by some constant M, and the second can be made
;; smaller than e/M for any value of e.  The product of these two
;; (equal to abs-taylor-sin-term) is thus less than an arbitrary e.

;; Here is the definition of the "low-order" terms.  This is the part
;; that comes up to some bound M.

(defun abs-taylor-sin-term-low (counter m x)
  (if (zp counter)
      1
    (if (< m counter)
	(abs-taylor-sin-term-low (1- counter) m x)
      (* (abs x) (/ counter)
	 (abs-taylor-sin-term-low (1- counter) m x)))))

;; And here are the "higher-order" terms, which we should be able to
;; make smaller than e/M.

(defun abs-taylor-sin-term-high (counter m x)
  (if (zp counter)
      1
    (if (< m counter)
	(* (abs x) (/ counter)
	 (abs-taylor-sin-term-high (1- counter) m x))
      (abs-taylor-sin-term-high (1- counter) m x))))

;; But first, we have to prove that abs-taylor-sin-term is given by
;; the product of the "low" part and the "high" part.

(defthm abs-taylor-sin-term-high-low
  (equal (abs-taylor-sin-term counter x)
	 (* (abs-taylor-sin-term-low counter m x)
	    (abs-taylor-sin-term-high counter m x))))

;; Now, the high part keeps multiplying by x/counter where counter
;; gets bigger and bigger.  We come up with an upper bound for it by
;; multiplying each time by x/m where "m" is the constant where we
;; split the taylor-sin-term, so it must be less than counter.

(defun abs-taylor-sin-term-high-2 (counter m x)
  (if (zp counter)
      1
    (if (< m counter)
	(* (abs x) (/ m)
	 (abs-taylor-sin-term-high-2 (1- counter) m x))
      (abs-taylor-sin-term-high-2 (1- counter) m x))))

;; Obviously these terms are real.

(defthm realp-abs-taylor-sin-term-high
  (implies (and (realp counter)
		(realp x))
	   (realp (abs-taylor-sin-term-high counter m x)))
  :rule-classes (:rewrite :type-prescription :generalize))

;; And so are these.

(defthm realp-abs-taylor-sin-term-high-2
  (implies (and (realp m)
		(realp x))
	   (realp (abs-taylor-sin-term-high-2 counter m x)))
  :rule-classes (:rewrite :type-prescription :generalize))

;; And they're non-negative!

(defthm abs-taylor-sin-term-high->=-0
  (implies (and (realp counter)
		(<= 0 counter)
		(realp x))
	   (<= 0 (abs-taylor-sin-term-high counter m x)))
  :rule-classes (:rewrite :type-prescription :generalize))

;; And so are these!

(defthm abs-taylor-sin-term-high-2->=-0
  (implies (and (realp m)
		(<= 0 m)
		(realp x))
	   (<= 0 (abs-taylor-sin-term-high-2 counter m x)))
  :rule-classes (:rewrite :type-prescription :generalize))

;; OK, now we want to prove that our original "high" estimate is at
;; least equal to our "high-2" estimate (where we divide by m instead
;; of counter each time).

(encapsulate
 ()

 ;; First, we need a simple cancellation rule.

 (local
  (defthm lemma-1
    (implies (and (realp x1) (realp x2)
		  (realp a) (<= 0 a)
		  (realp z1) (realp z2))
	     (equal (< (* x1 a z1) (* x2 a z2))
		    (if (equal a 0)
			nil
		      (< (* x1 z1) (* x2 z2)))))
    :hints (("Subgoal 1"
	     :use ((:instance <-*-left-cancel
			      (z a)
			      (x (* x1 z1))
			      (y (* x2 z2))))
	     :in-theory (disable <-*-left-cancel)))))

 ;; And here's a simple composition rule for <=.

 (local
  (defthm lemma-2
    (implies (and (realp x1) (realp x2) (<= 0 x1) (<= x1 x2)
		  (realp y1) (realp y2) (<= 0 y1) (< y1 y2))
	     (<= (* x1 y1) (* x2 y2)))))

 ;; From these, it follows that high-2 is an upper bound on the
 ;; high-order terms.

 (defthm abs-taylor-sin-term-high-<=-2
   (implies (and (realp counter) (<= 0 counter)
		 (realp m)       (< 0 m)
		 (realp x))
	    (<= (abs-taylor-sin-term-high counter m x)
		(abs-taylor-sin-term-high-2 counter m x))))
 )

;; Aha!  Since we keep multiplying by the same value on high-2, we
;; realize that high-w is nothing more than a call to expt.

(defthm abs-taylor-sin-term-high-2->n-expt
  (implies (and (integerp counter)
		(integerp m)
		(<= 0 m)
		(<= m counter))
	   (equal (abs-taylor-sin-term-high-2 counter m x)
		  (n-expt (/ (abs x) m)
			  (- counter m)))))

;; Now, we know that we can choose m above so that the call to
;; expt(x/m k) approaches zero.  For example, pick m so that x/m < 1/2
;; and we can make expt(x/m k) as small as possible by simply picking
;; larger values of k.  But we want to use the lemma
;; guess-num-iters-aux-is-a-good-guess which has a conclusion more
;; like y > 2^k.  So, what we want is to prove that if y>2^k, 1/y is
;; less than 1/2^k.

(encapsulate
 ()

 ;; First, we snow that 1/2-to-the-n is the same as expt(1/2 n).  This
 ;; just reflects that we didn't know about expt when we wrote the
 ;; code for guess-num-iters (but hey, sqrt was our first ACL2
 ;; project!)

 (local
  (defthm lemma-1
    (implies (and (integerp n)
		  (<= 0 n)
		  (realp x)
		  (< 0 x))
	     (equal (/ (2-to-the-n n)) (n-expt 1/2 n)))))

 ;; And here is a simple cancellation rule, 1/x < y => 1/y < x

 (local
  (defthm lemma-2
    (implies (and (realp x)
		  (< 0 x)
		  (realp y)
		  (< 0 y)
		  (< (/ x) y))
	     (< (/ y) x))
    :hints (("Goal"
	     :use ((:instance <-unary-/-positive-left)
		   (:instance <-unary-/-positive-left (x y) (y x)))
	     :in-theory (disable <-unary-/-positive-left)))))

 ;; And so, as long as 1/x < 2^n, 1/2^n < x.

 (defthm 2-to-the-n->expt-2-n
   (implies (and (integerp n)
		 (<= 0 n)
		 (realp x)
		 (< 0 x)
		 (< (/ x) (2-to-the-n n)))
	    (< (n-expt 1/2 n) x))
   :hints (("Goal"
	    :use ((:instance lemma-2
			     (y (2-to-the-n n))))
	    :in-theory (disable lemma-2))))
 )

;; So now, if we have a given value of eps and m, here are the number
;; of times we have to iterate before 1/2^n < eps

(defun new-guess-num-iters (eps m)
  (guess-num-iters-aux (next-integer (/ eps)) m))

;; Now, the guess we come up with is at least equal to m, since we
;; just keep increasing to m.

(defthm new-guess-num-iters-bound
  (implies (integerp m)
	   (< m (new-guess-num-iters eps m))))

;; And, we always come up with a positive number of iters.

(defthm new-guess-num-iters-bound-type-prescription
  (and (integerp (new-guess-num-iters eps m))
       (< 0 (new-guess-num-iters eps m))))

;; Unsurprisingly, this choice of num-iters works again!  I.e., 1/2^n
;; really is less than epsilon.

(defthm guess-num-iters-works-again
  (implies (and (realp eps)
		(< 0 eps)
		(integerp m)
		(< 0 m))
	   (< (n-expt 1/2 (new-guess-num-iters eps m))
	      eps))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance 2-to-the-n->expt-2-n
			    (x eps)
			    (n (guess-num-iters-aux
				(next-integer (/ eps)) m)))
		 (:instance guess-num-iters-aux-is-a-good-guess
			    (x (next-integer (/ eps)))
			    (num-iters m)))
	   :in-theory (disable 2-to-the-n->expt-2-n
			       guess-num-iters-aux-is-a-good-guess
			       <-unary-/-positive-left))))

(in-theory (disable new-guess-num-iters))

;; Now, we need some simple theorems about n-expt, since we've
;; converted all references to expt into n-expt.  The first obvious
;; fact is that it's real.

(defthm realp-n-expt
  (implies (realp x)
	   (realp (n-expt x n)))
  :rule-classes (:rewrite :type-prescription :generalize))

;; It's also non-negative for non-negative arguments.

(defthm n-expt->=-0
  (implies (and (realp x)
		(<= 0 x))
	   (<= 0 (n-expt x n)))
  :rule-classes (:rewrite :type-prescription :generalize))

;; Another useful fact is that x<=y means x^n <= y^n

(defthm n-expt-monotonic
  (implies (and (realp x) (<= 0 x)
		(realp y) (<= x y))
	   (<= (n-expt x n) (n-expt y n))))

;; So now, if we choose a number f <= 1/2 to start with, we fine that
;; our choice of num-iters is good enough so that f^num_iters < eps.

(defthm guess-num-iters-really-works
  (implies (and (realp eps)  (< 0 eps)
		(integerp m) (< 0 m)
		(realp f)    (<= 0 f)  (<= f 1/2))
	   (< (n-expt f (new-guess-num-iters eps m))
	      eps))
  :hints (("Goal"
	   :use ((:instance guess-num-iters-works-again)
		 (:instance n-expt-monotonic
			    (x f)
			    (y 1/2)
			    (n (new-guess-num-iters eps m))))
	   :in-theory nil)))

;; So that means we can come up with an arbitrarily small upper bound
;; for the high-2 function.

(defthm abs-taylor-sin-term-high-2-upper-bound
  (implies (and (integerp m)
		(< 0 m)
		(equal counter (+ m (new-guess-num-iters eps m)))
		(realp x)
		(<= (/ (abs x) m) 1/2)
		(realp eps) (< 0 eps))
	   (< (abs-taylor-sin-term-high-2 counter m x)
	      eps)))

;; And of course, since high < high-2, that means we have an
;; arbitrarily good upper bound for the high portion.

(defthm abs-taylor-sin-term-high-upper-bound
  (implies (and (integerp m)
		(< 0 m)
		(equal counter (+ m (new-guess-num-iters eps m)))
		(realp x)
		(<= (/ (abs x) m) 1/2)
		(realp eps) (< 0 eps))
	   (< (abs-taylor-sin-term-high counter m x)
	      eps))
  :hints (("Goal"
	   :use ((:instance abs-taylor-sin-term-high-<=-2)
		 (:instance abs-taylor-sin-term-high-2-upper-bound))
	   :in-theory (disable abs-taylor-sin-term-high-<=-2
			       abs-taylor-sin-term-high-2-upper-bound
			       guess-num-iters-really-works))))

;; Now, for really large values of m, it doesn't really matter
;; whether I go up to counter iters or m terms in computing the
;; low-order terms -- the upper ones are all zero.

(defthm abs-taylor-sin-term-low-counter-m-m-x
  (implies (and (integerp counter)
		(integerp m)
		(<= 0 m)
		(< m counter))
	   (equal (abs-taylor-sin-term-low counter m x)
		  (abs-taylor-sin-term-low m m x))))

;; So that gives us a different version of the split for
;; taylor-sin-term, where the low terms go all the way up to m.

(defthm abs-taylor-sin-term-high-low-better
  (implies (and (integerp counter)
		(integerp m)
		(<= 0 m)
		(< m counter))
	   (equal (abs-taylor-sin-term counter x)
		  (* (abs-taylor-sin-term-low m m x)
		     (abs-taylor-sin-term-high counter m x)))))

(in-theory (disable abs-taylor-sin-term-high-low))

;; Now, here are some simple lemmas about the low and high order
;; terms, namely they're real and non-negative.

(defthm realp-abs-taylor-sin-term-low
  (implies (realp x)
	   (and (realp (abs-taylor-sin-term-low c m x))
		(<= 0 (abs-taylor-sin-term-low c m x))))
  :rule-classes (:rewrite :type-prescription :generalize))

;; Ditto....

(defthm realp-abs-taylor-sin-term-high-3
  (implies (realp x)
	   (and (realp (abs-taylor-sin-term-high c m x))
		(<= 0 (abs-taylor-sin-term-high c m x))))
  :rule-classes (:rewrite :type-prescription :generalize))

;; So now, we can pick the right n so that the nth term of the Taylor
;; approximation to x is < eps.  Notice that we make sure the value we
;; return is even, because the Taylor expansion takes every other term
;; from the sequence.

(defun n-for-taylor-sin-term (x eps)
  (let* ((m (next-integer (* 2 (abs x))))
	 (eps1 (/ eps (1+ (abs-taylor-sin-term-low m m x))))
	 (counter (+ m (new-guess-num-iters eps1 m))))
    (if (evenp counter)
	counter
      (1+ counter))))

;; And now, we need to prove the above claim.  First, we need some
;; lemmas.

(encapsulate
 ()

 ;; Here's something obvious to start with.  If x is real, then the
 ;; ceiling of 2*|x| is never negative.

 (local
  (defthm lemma-1
    (implies (realp x)
	     (equal (< (next-integer (* 2 (abs x))) 0) nil))
    :hints (("Goal"
	     :use ((:instance x-<-next-integer
			      (x (* 2 (abs x))))
		   (:instance (:theorem
			       (implies (realp x)
					(<= 0 (* 2 (abs x)))))))
	     :in-theory (disable x-<-next-integer))
	    ("Subgoal 1"
	     :in-theory (enable abs)))))

 ;; Better yet, we actually know it's positive, because of the ceiling
 ;; part.

 (local
  (defthm lemma-2
    (implies (realp x)
	     (< 0 (next-integer (* 2 (abs x)))))
    :hints (("Goal"
	     :use ((:instance x-<-next-integer
			      (x (* 2 (abs x))))
		   (:instance (:theorem
			       (implies (realp x)
					(<= 0 (* 2 (abs x)))))))
	     :in-theory (disable x-<-next-integer))
	    ("Subgoal 1"
	     :in-theory (enable abs)))))

 ;; Now, if m = ceiling(2*|x|), it follows that |x|/m < 1/2.

 (local
  (defthm lemma-3
    (implies (and (realp x)
		  (equal m (next-integer (* 2 (abs x)))))
	     (and (< 0 m)
		  (not (< 1/2 (* (/ m) (abs x))))))))

 ;; So now, we find that if we pick our value of m and counter
 ;; carefully, the nth taylor-sin-term is less than epsilon.

 (local
  (defthm abs-taylor-sin-term-upper-bound-lemma
    (implies (and (realp x)
		  (realp eps) (< 0 eps)
		  (equal m (next-integer (* 2 (abs x))))
		  (equal eps1 (/ eps (1+ (abs-taylor-sin-term-low m m x))))
		  (equal counter (+ m (new-guess-num-iters eps1 m))))
	     (< (abs-taylor-sin-term counter x)
		eps))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance abs-taylor-sin-term-high-low-better)
		   (:instance abs-taylor-sin-term-high-upper-bound
			      (eps eps1)))
	     :in-theory (disable abs-taylor-sin-term-high-low-better
				 abs-taylor-sin-term-high-upper-bound)))))

 ;; Silly theorem, |x| < c => c is never negative.

 (local
  (defthm lemma-4
    (implies (and (realp x)
		  (integerp counter)
		  (< (abs x) counter))
	     (equal (< counter 0) nil))
    :hints (("Goal" :in-theory (enable abs)))))

 ;; Actually, more than that, c is never zero either, so if c is an
 ;; integer, it's at least 1.

 (local
  (defthm lemma-5
    (implies (and (realp x)
		  (integerp counter)
		  (< (abs x) counter))
	     (equal (< (+ 1 counter) 0) nil))
    :hints (("Goal" :use ((:instance lemma-4))
	     :in-theory (disable lemma-4)))))

 ;; Now here is how you resolve the taylor-sin-term of sin(0) or
 ;; cos(0).  It's always zero, except for the first term of cosine.

 (local
  (defthm lemma-6
    (implies (equal x 0)
	     (equal (abs-taylor-sin-term c x)
		    (if (zp c) 1 0)))))

 ;; Remember that we pick the final n as being always even.  If the
 ;; first pick is odd, we add one to it.  So now, since we know that
 ;; the first pick gives a small enough taylor-sin-term, we look at
 ;; the taylor-sin-term when we add 1 to the counter.  For starters,
 ;; it's obvious that taylor-sin-term just gets smaller, right?

 (local
  (defthm lemma-7
   (implies (and (realp x)
		 (integerp counter)
		 (< (abs x) counter))
	    (<= (abs-taylor-sin-term (+ 1 counter) x)
		(abs-taylor-sin-term counter x)))
   :hints (("Goal" :do-not-induct t
	    :cases ((= x 0)))
	   ("Subgoal 2"
	    :use ((:instance abs-taylor-counter+1-<-counter (sign 1))
		  (:instance abs-taylor-sin-term-works (sign 1))
		  (:instance abs-taylor-sin-term-works
			     (sign 1)
			     (counter (+ 1 counter)))
		  (:instance lemma-4)
		  (:instance lemma-5))
	    :in-theory (disable abs-taylor-sin-term
				abs-taylor-sin-term-works
				abs-taylor-counter+1-<-counter
				lemma-4
				lemma-5
                                ;; Added by Matt K. for v3-4:
                                abs-taylor-sin-term-high-low-better))
	   ("Subgoal 1"
	    :use ((:instance lemma-5))
	    :in-theory (disable lemma-5)))))

 ;; So, let's define our method for picking the value of num-iters,
 ;; before we bother with making it even.

 (local
  (defun n-for-taylor-sin-term-raw (x eps)
    (let* ((m (next-integer (* 2 (abs x))))
	   (eps1 (/ eps (1+ (abs-taylor-sin-term-low m m x))))
	   (counter (+ m (new-guess-num-iters eps1 m))))
      counter)))

 ;; We know that choice of num-iters is good enough to make
 ;; taylor-sin-term small enough for us.

 (local
  (defthm abs-taylor-sin-term-upper-bound-lemma-2
    (implies (and (realp x)
		  (realp eps) (< 0 eps))
	     (< (abs-taylor-sin-term (n-for-taylor-sin-term-raw x eps) x)
		eps))
    :hints (("Goal"
	     :expand ((n-for-taylor-sin-term-raw x eps)))
	    ("Goal'"
	     :use ((:instance abs-taylor-sin-term-upper-bound-lemma))
	     :in-theory (disable abs-taylor-sin-term-upper-bound-lemma)))))

 ;; And here's the kick.  The actual value of num-iters we pick is
 ;; either the one above or 1 plus that value.

 (local
  (defthm raw-is-useful
    (or (equal (n-for-taylor-sin-term x eps)
	       (n-for-taylor-sin-term-raw x eps))
	(equal (n-for-taylor-sin-term x eps)
	       (+ 1 (n-for-taylor-sin-term-raw x eps))))
    :rule-classes nil))

 (local (in-theory (disable n-for-taylor-sin-term-raw)))

 ;; Of course, the value of n we pick is always a positive integer.

 (defthm n-for-taylor-sin-term-type-prescription
   (implies (and (realp x)
		 (realp eps)
		 (< 0 eps))
	    (and (integerp (n-for-taylor-sin-term x eps))
		 (< 0 (n-for-taylor-sin-term x eps))))
   :hints (("Goal"
	    :use ((:instance new-guess-num-iters-bound-type-prescription
			     (eps eps1))
		  (:instance lemma-2))
	    :in-theory (disable
				new-guess-num-iters-bound-type-prescription
				lemma-2)))
   :rule-classes (:rewrite :type-prescription :generalize))

 ;; Now, the value of n we pick is at least 2*|x| -- this is because
 ;; we start looking at values of n from that number, and we always
 ;; look for a bigger value.

 (local
  (defthm lemma-1.1
    (< (next-integer (* 2 (abs x)))
       (n-for-taylor-sin-term x eps))
    :hints (("Goal"
	     :use ((:instance new-guess-num-iters-bound-type-prescription
			      (eps eps1)))
	     :in-theory (disable new-guess-num-iters-bound-type-prescription)))))

 ;; Here's a dumb lemma: |x| <= 2|x|....

 (local
  (defthm lemma-1.2
    (<= (abs x) (* 2 (abs x)))
    :hints (("Goal" :in-theory (enable abs)))))

 ;; and so |x| < ceil(2|x|)

 (local
  (defthm lemma-1.3
    (implies (realp x)
	     (< (abs x)
		(next-integer (* 2 (abs x)))))
    :hints (("Goal"
	     :use ((:instance lemma-1.2)
		   (:instance x-<-next-integer
			      (x (* 2 (abs x)))))
	     :in-theory (disable lemma-1.2
				 x-<-next-integer)))))

 ;; Which means that the value of num-iters we end up with is at least
 ;; equal to |x|.

 (defthm abs-x-<-n-for-taylor-sin-term
   (implies (realp x)
	    (< (abs x) (n-for-taylor-sin-term x eps)))
   :hints (("Goal"
	    :use ((:instance lemma-1.1)
		  (:instance lemma-1.3))
	    :in-theory (disable lemma-1.1
				lemma-1.3
				n-for-taylor-sin-term))))

 ;; This is true even before we bother adding 1 to the odd values of
 ;; num-iters.

 (local
  (defthm abs-x-<-n-for-taylor-sin-term-raw
    (implies (realp x)
	     (< (abs x) (n-for-taylor-sin-term-raw x eps)))
    :hints (("Goal"
	     :use ((:instance lemma-1.1)
		   (:instance lemma-1.3)
		   (:instance raw-is-useful))
	     :in-theory (disable lemma-1.1
				 lemma-1.3
				 n-for-taylor-sin-term
				 n-for-taylor-sin-term-raw)))))

 ;; OK, so finally, the nth term in the Taylor series turns out to be
 ;; less than the arbitrary epsilon.

 (defthm abs-taylor-sin-term-upper-bound
    (implies (and (realp x)
		  (realp eps) (< 0 eps))
	     (< (abs-taylor-sin-term (n-for-taylor-sin-term x eps) x)
		eps))
    :hints (("Goal"
	     :use ((:instance raw-is-useful))
	     :in-theory (disable n-for-taylor-sin-term))
	    ("Subgoal 2"
	     :use ((:instance abs-taylor-sin-term-upper-bound-lemma-2))
	     :in-theory (disable abs-taylor-sin-term-upper-bound-lemma-2))
	    ("Subgoal 1"
	     :use ((:instance abs-taylor-sin-term-upper-bound-lemma-2)
		   (:instance lemma-7
			      (counter (n-for-taylor-sin-term-raw x eps))))
	     :in-theory (disable abs-taylor-sin-term-upper-bound-lemma-2
				 n-for-taylor-sin-term
				 abs-taylor-sin-term
				 lemma-7))))

 ;; This is just for an induction hint:

 (local
  (defun natural-induction (n)
    (if (zp n)
	1
      (+ n (natural-induction (1- n))))))

 ;; If n is odd, then n-1 is even.

 (local
  (defthm lemma-8
    (implies (and (integerp n)
		  (<= 0 n)
		  (not (evenp n)))
	     (evenp (- n 1)))
    :hints (("Goal" :induct (natural-induction n)))))

 ;; If n is odd, then n+1 is even.

 (local
  (defthm lemma-9
    (implies (and (integerp n)
		  (<= 0 n)
		  (not (evenp n)))
	     (evenp (+ 1 n)))
    :hints (("Goal" :use ((:instance lemma-8)
			  (:instance (:theorem
				      (implies (evenp n)
					       (evenp (+ n 2))))
				     (n (- n 1))))
	     :in-theory (disable lemma-8)))))

 ;; Here is a different definition of n-for-taylor-sin-term that just
 ;; leaves open the detail of forcing num-iters to be even.

 (local
  (defun n-for-taylor-sin-term-alt (x eps)
    (if (evenp (n-for-taylor-sin-term-raw x eps))
	(n-for-taylor-sin-term-raw x eps)
      (1+ (n-for-taylor-sin-term-raw x eps)))))

 ;; The definition is the same as the previous one!

 (local
  (defthm alt-works
    (equal (n-for-taylor-sin-term x eps)
	   (n-for-taylor-sin-term-alt x eps))
    :hints (("Goal" :in-theory (enable n-for-taylor-sin-term-raw)))))

 ;; And so it returns a positive integer....

 (local
  (defthm raw-type-prescription
   (implies (and (realp x)
		 (realp eps)
		 (< 0 eps))
	    (and (integerp (n-for-taylor-sin-term-raw x eps))
		 (< 0 (n-for-taylor-sin-term-raw x eps))))
   :hints (("Goal"
	    :use ((:instance new-guess-num-iters-bound-type-prescription
			     (eps eps1))
		  (:instance lemma-2))
	    :in-theory (enable-disable
			(n-for-taylor-sin-term-raw)
			(new-guess-num-iters-bound-type-prescription
			 lemma-2))))
   :rule-classes (:rewrite :type-prescription :generalize)))

 ;; Actually, it returns an *even* positive integer.

 (defthm evenp-n-for-taylor-sin-term
   (implies (and (realp x)
		 (realp eps)
		 (< 0 eps))
	    (evenp (n-for-taylor-sin-term x eps)))
   :hints (("Goal"
	    :use ((:instance lemma-9
			     (n (n-for-taylor-sin-term-raw x eps))))
	    :in-theory (disable lemma-9
				n-for-taylor-sin-term))))
 )

(in-theory (disable n-for-taylor-sin-term))
(in-theory (disable (n-for-taylor-sin-term)))

;; So now, without a doubt the value of num-iters we pick is good
;; enough to make taylor-sin-term small enough -- this is the same as
;; the previous theorem with |taylor-sin-term| instead of
;; abs-taylor-sin-term.

(defthm taylor-sin-term-upper-bound
  (implies (and (realp x)
		(realp eps) (< 0 eps)
		(or (= sign 1) (= sign -1)))
	   (< (abs (taylor-sin-term sign (n-for-taylor-sin-term x eps) x))
	      eps)))

;; Since we sometimes end up with 1+counter, we show that this still
;; works even when counter is 1+num_iters

(encapsulate
 ()

 ;; First, some simple rules.  abs-taylor-sin-term is real....

 (local
  (defthm lemma-1
    (implies (realp x)
	     (realp (abs-taylor-sin-term n x)))
    :rule-classes (:rewrite :type-prescription)))

 ;; ...and it's non-negative.

 (local
  (defthm lemma-2
    (implies (realp x)
	     (<= 0 (abs-taylor-sin-term n x)))
    :rule-classes (:rewrite :type-prescription)))

 ;; And here is a simple cancellation rule:

 (local
  (defthm lemma-3
    (implies (and (realp x)
		  (realp y)
		  (realp z)
		  (<= 0 z)
		  (< 0 y)
		  (< x y))
	     (<= (* x (/ y) z) z))
    :hints (("Goal"
	     :cases ((= z 0)))
	    ("Subgoal 2"
	     :use ((:instance <-*-right-cancel
			      (x (* x (/ y)))
			      (y 1)
			      (z z)))))))

 ;; And of course, the (n+1)st term of the Taylor sequence is at most
 ;; equal to the nth term -- and we already know the nth term is small
 ;; enough, so........

 (local
  (defthm lemma-4
    (implies (and (realp x)
		  (realp eps) (< 0 eps)
		  (or (= sign 1) (= sign -1)))
	     (<= (abs (taylor-sin-term sign (1+ (n-for-taylor-sin-term x eps)) x))
		 (abs (taylor-sin-term sign (n-for-taylor-sin-term x eps) x))))
    :hints (("Goal"
	     :in-theory (disable abs-taylor-sin-term-high-low-better))
	    ("Subgoal 2"
	     :use ((:instance abs-x-<-n-for-taylor-sin-term)
		   (:instance lemma-3
			      (x (abs x))
			      (y (+ 1 (n-for-taylor-sin-term x eps)))
			      (z (abs-taylor-sin-term
				  (n-for-taylor-sin-term x eps)
				  x))))
	     :in-theory (disable abs-x-<-n-for-taylor-sin-term))
	    ("Subgoal 1"
	     :use ((:instance abs-x-<-n-for-taylor-sin-term)
		   (:instance lemma-3
			      (x (abs x))
			      (y (+ 1 (n-for-taylor-sin-term x eps)))
			      (z (abs-taylor-sin-term
				  (n-for-taylor-sin-term x eps)
				  x))))
	     :in-theory (disable abs-x-<-n-for-taylor-sin-term)))))

 ;; ... the (n+1)st term must be small enough!

 (defthm taylor-sin-term-upper-bound-2
   (implies (and (realp x)
		 (realp eps) (< 0 eps)
		 (or (= sign 1) (= sign -1)))
	    (< (abs (taylor-sin-term sign
				     (1+ (n-for-taylor-sin-term x eps))
				     x))
	       eps))
   :hints (("Goal"
	    :use ((:instance lemma-4)
		  (:instance taylor-sin-term-upper-bound))
	    :in-theory nil)))
 )

;; So now, the sumlist of all the terms after the nth one is less than
;; epsilon.  We found a bound for our error term!

(defthm sumlist-taylor-sincos-bound-lemma
  (implies (and (realp x)
		(realp eps) (< 0 eps)
		(or (= sign 1) (= sign -1)))
	   (< (abs (sumlist
		    (taylor-sincos-list nterms
					(n-for-taylor-sin-term x eps)
					sign
					x)))
	      eps))
  :hints (("Goal"
	   :use ((:instance taylor-sin-term-upper-bound)
		 (:instance sumlist-taylor-sincos-list-bound
			    (counter (n-for-taylor-sin-term x eps)))
		 (:instance abs-x-<-n-for-taylor-sin-term)
		 (:instance (:type-prescription n-for-taylor-sin-term)))
	   :in-theory nil)))

;; Of course, the sumlist of all the terms after the (n+1)st term is
;; also bounded.....duh....

(defthm sumlist-taylor-sincos-bound-lemma-2
  (implies (and (realp x)
		(realp eps) (< 0 eps)
		(or (= sign 1) (= sign -1)))
	   (< (abs (sumlist
		    (taylor-sincos-list nterms
					(1+ (n-for-taylor-sin-term x eps))
					sign
					x)))
	      eps))
  :hints (("Goal"
	   :use ((:instance taylor-sin-term-upper-bound-2)
		 (:instance sumlist-taylor-sincos-list-bound
			    (counter (1+ (n-for-taylor-sin-term x eps))))
		 (:instance abs-x-<-n-for-taylor-sin-term)
		 (:instance (:type-prescription n-for-taylor-sin-term)))
	   :in-theory nil)))

;; Now here's an important fact.  The num-iters we pick will be
;; limited when we give it standard arguments.

(defthm limited-guess-num-iters-aux
  (implies (and (integerp range) (standard-numberp range)
		(integerp m) (standard-numberp m))
	   (i-limited (guess-num-iters-aux range m))))

;; This holds for new-guess-num-iters also.

(defthm limited-new-guess-num-iters
  (implies (and (integerp m) (standard-numberp m)
		(realp eps) (< 0 eps) (standard-numberp eps))
	   (i-limited (new-guess-num-iters eps m)))
  :hints (("Goal" :do-not-induct t
	   :expand ((new-guess-num-iters eps m))
	   :in-theory (enable standards-are-limited
			      limited-integers-are-standard))))

;; We want that to be true for n-for-taylor-sincos as well.

(encapsulate
 nil

 ;; To start with, the ceiling of 2|x| is limited for a limited x.

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (i-limited x))
	     (i-limited (next-integer (* 2 (abs x)))))
    :hints (("Goal"
	     :in-theory (enable abs)))))

 ;; And here's a neat lemma!  (x+y) is limited precisely when y is
 ;; limited, if I already know that x is limited.  This is much better
 ;; than the regular limited-plus rule!

 (local
  (defthm lemma-2
    (implies (and (i-limited x)
		  (acl2-numberp y))
	     (equal (i-large (+ x y))
		    (i-large y)))
    :hints (("Goal"
	     :cases ((i-limited y)))
	    ("Subgoal 2"
	     :use ((:instance limited+large->large))
	     :in-theory (disable limited+large->large)))))

 ;; Now, abs(x) is standard when x is standard.

 (local
  (defthm standard-numberp-abs
      (implies (acl2-numberp x)
	       (equal (standardp (abs x))
		      (standardp x)))
    :hints (("Goal" :in-theory (enable abs)))))

 ;; Which means that for standard values, the taylor-sin-term-low part
 ;; is standard.  This is important, because this is the "M" value
 ;; that we'll use to find a "high" product less than eps/M -- we want
 ;; eps/M to be limited, so M and eps must not be small!

 (local
  (defthm standardp-abs-taylor-sin-term-low
    (implies (and (standard-numberp c)
		  (standard-numberp m)
		  (standard-numberp x))
	     (standard-numberp (abs-taylor-sin-term-low c m x)))
    :hints (("Subgoal *1/5'5'"
	     :use ((:instance standardp-times
			      (x (/ c))
			      (y (* (abs x) atstlw)))
		   (:instance standardp-times
			      (x (abs x))
			      (y atstlw)))
	     :in-theory (disable standardp-times)))))


 ;; And that means that the value of num-ters we come up with is limited.

 (defthm limited-n-for-taylor-sin-term
   (implies (and (realp x) (standard-numberp x)
		 (realp eps) (< 0 eps) (standard-numberp eps))
	    (i-limited (n-for-taylor-sin-term x eps)))
   :hints (("Goal" :do-not-induct t
	    :expand ((n-for-taylor-sin-term x eps))
	    :in-theory (enable limited-integers-are-standard))))
 )

;; Now here's a rule that tells us how to split up a Taylor expansion
;; into a limited prefix and some suffix.

(defthm taylor-sincos-list-split-limited-non-limited
  (implies (and (integerp nterms1)
		(<= 0 nterms1)
		(i-limited nterms1)
		(evenp nterms1)
		(integerp nterms2)
		(<= 0 nterms2)
		(i-large nterms2)
		(integerp counter)
		(<= 0 counter)
		(integerp sign))
	   (equal (taylor-sincos-list nterms2 counter sign x)
		  (append (taylor-sincos-list nterms1 counter sign x)
			  (taylor-sincos-list (- nterms2
						 nterms1)
					      (+ counter nterms1)
					      (if (evenp (/ nterms1 2))
						  sign
						(- sign))
					      x))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance taylor-sincos-list-split
			    (n1 nterms1)
			    (n2 (- nterms2 nterms1))))
	   :in-theory (disable taylor-sincos-list-split))
	  ("Goal''"
	   :use ((:instance large->-non-large
			    (x nterms2)
			    (y nterms1)))
	   :in-theory (disable large->-non-large))))

;; And here is that same theorem specialized for the value of
;; num-iters that we pick -- notice we already know num-iters is
;; limited.

(defthm taylor-sincos-list-split-for-n-for-taylor-sin-term
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(i-large nterms)
		(integerp counter)
		(<= 0 counter)
		(integerp sign)
		(realp x) (standard-numberp x)
		(realp eps) (< 0 eps) (standard-numberp eps)
		(equal n (n-for-taylor-sin-term x eps)))
	   (equal (taylor-sincos-list nterms counter sign x)
		  (append (taylor-sincos-list n counter sign x)
			  (taylor-sincos-list (- nterms n)
					      (+ counter n)
					      (if (evenp (/ n 2))
						  sign
						(- sign))
					      x))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance taylor-sincos-list-split-limited-non-limited
			    (nterms1 n)
			    (nterms2 nterms)))
	   :in-theory (disable evenp
			       taylor-sincos-list-split-limited-non-limited))))

;; Same theorem, but when counter starts at 0 -- so we get the entire
;; Taylor series.

(defthm sumlist-taylor-sincos-list-split
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(i-large nterms)
		(realp x) (standard-numberp x)
		(realp eps) (< 0 eps) (standard-numberp eps)
		(equal n (n-for-taylor-sin-term x eps)))
	   (equal (sumlist (taylor-sincos-list nterms 0 1 x))
		  (+ (sumlist (taylor-sincos-list n 0 1 x))
		     (sumlist (taylor-sincos-list (- nterms n)
						  n
						  (if (evenp (/ n 2))
						      1
						    -1)
						  x)))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance taylor-sincos-list-split-for-n-for-taylor-sin-term
			    (counter 0)
			    (sign 1)))
	   :in-theory (disable evenp
			       taylor-sincos-list-split-for-n-for-taylor-sin-term))))

;; Of course, counter starts at 1 for sin(x)....sigh....

(defthm sumlist-taylor-sincos-list-split-2
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(i-large nterms)
		(realp x) (standard-numberp x)
		(realp eps) (< 0 eps) (standard-numberp eps)
		(equal n (n-for-taylor-sin-term x eps)))
	   (equal (sumlist (taylor-sincos-list nterms 1 1 x))
		  (+ (sumlist (taylor-sincos-list n 1 1 x))
		     (sumlist (taylor-sincos-list (- nterms n)
						  (1+ n)
						  (if (evenp (/ n 2))
						      1
						    -1)
						  x)))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance taylor-sincos-list-split-for-n-for-taylor-sin-term
			    (counter 1)
			    (sign 1)))
	   :in-theory (disable evenp
			       taylor-sincos-list-split-for-n-for-taylor-sin-term))))

;; Quick fact: the first part of the split above is limited.

(defthm limited-taylor-sincos-list-n-for-taylor-sin-term
  (implies (and (realp x)
		(realp eps) (< 0 eps) (< eps 1)
		(or (= sign 1) (= sign -1))
		(equal n (n-for-taylor-sin-term x eps)))
	   (i-limited (sumlist (taylor-sincos-list nterms n sign x))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance large-if->-large
			    (x (sumlist (taylor-sincos-list nterms n sign x)))
			    (y 1))
		 (:instance sumlist-taylor-sincos-bound-lemma))
	   :in-theory (disable large-if->-large
			       sumlist-taylor-sincos-bound-lemma))))

;; Same goes for when counter starts with 1....sigh....

(defthm limited-taylor-sincos-list-n-for-taylor-sin-term-2
  (implies (and (realp x)
		(realp eps) (< 0 eps) (< eps 1)
		(or (= sign 1) (= sign -1))
		(equal n (1+ (n-for-taylor-sin-term x eps))))
	   (i-limited (sumlist (taylor-sincos-list nterms n sign x))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance large-if->-large
			    (x (sumlist (taylor-sincos-list nterms n sign x)))
			    (y 1))
		 (:instance sumlist-taylor-sincos-bound-lemma-2))
	   :in-theory (disable large-if->-large
			       sumlist-taylor-sincos-bound-lemma))))

;; Next, we do the same split, but this time we take standard-parts of
;; both sides.  Notice that the standard-part of the sum on the right
;; side of the equation splits into a sum of two standard-parts, since
;; both terms are known to be limited. Moreover, the first term is
;; known to be standard, so we don't need the standard-part!

(defthm standard-part-sumlist-taylor-sincos-list-split
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(i-large nterms)
		(realp x) (standard-numberp x)
		(realp eps) (< 0 eps) (< eps 1)
		(standard-numberp eps)
		(equal n (n-for-taylor-sin-term x eps)))
	   (equal (standard-part
                   (sumlist (taylor-sincos-list nterms
						0
						1
						x)))
		  (+ (sumlist (taylor-sincos-list n 0 1 x))
		     (standard-part
		      (sumlist
		       (taylor-sincos-list (- nterms n)
					   n
					   (if (evenp (/ n 2))
					       1
					     -1)
					   x))))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance sumlist-taylor-sincos-list-split)
		 (:instance standard-part-of-plus
			    (x (sumlist (taylor-sincos-list n 0 1 x)))
			    (y (sumlist
				(taylor-sincos-list (- nterms n)
						    n
						    (if (evenp (/ n 2))
							1
						      -1)
						    x)))))
	   :in-theory (enable-disable (limited-integers-are-standard)
				      (evenp
				       sumlist-taylor-sincos-list-split
				       standard-part-of-plus)))))

;; Same as above, but starting with counter equal to 1.

(defthm standard-part-sumlist-taylor-sincos-list-split-2
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(i-large nterms)
		(realp x) (standard-numberp x)
		(realp eps) (< 0 eps) (< eps 1) (standard-numberp eps)
		(equal n (n-for-taylor-sin-term x eps)))
	   (equal (standard-part (sumlist (taylor-sincos-list nterms 1 1 x)))
		  (+ (sumlist (taylor-sincos-list n 1 1 x))
		     (standard-part
		      (sumlist (taylor-sincos-list (- nterms n)
						   (1+ n)
						   (if (evenp (/ n 2))
						       1
						     -1)
						   x))))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance sumlist-taylor-sincos-list-split-2)
		 (:instance standard-part-of-plus
			    (x (sumlist (taylor-sincos-list n 1 1 x)))
			    (y (sumlist
				(taylor-sincos-list (- nterms n)
						    (1+ n)
						    (if (evenp (/ n 2))
							1
						      -1)
						    x)))))
	   :in-theory (enable-disable (limited-integers-are-standard)
				      (evenp
				       sumlist-taylor-sincos-list-split
				       standard-part-of-plus)))))

;; The error term we ended up with looks like standard-part(XXX) so we
;; want to know when standard-part(XXX) < eps.  It turns out that we
;; can make standard-part(XXX) <= eps (but not strict <) when |XXX|<eps:

(encapsulate
 ()

 ;; First, a quickie.  If x <= 0 and standard-part(x) >= 0, then
 ;; standard-part(x) must be exactly 0.

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (<= x 0)
		  (<= 0 (standard-part x)))
	     (= (standard-part x) 0))
    :hints (("Goal"
	     :use ((:instance standard-part-<= (y 0)))
	     :in-theory (disable standard-part-<=)))
    :rule-classes nil))

 ;; Likewise when x >= 0 and standard-part(x) <= 0.

 (local
  (defthm lemma-2
    (implies (and (realp x)
		  (<= 0 x)
		  (<= (standard-part x) 0))
	     (= (standard-part x) 0))
    :hints (("Goal"
	     :use ((:instance standard-part-<= (x 0) (y x)))
	     :in-theory (disable standard-part-<=)))
    :rule-classes nil))

 ;; And here is a big lemma that if |x|<e then |std-pt(x)| <= e.

 (local
  (defthm lemma-3
    (implies (and (realp x)
		  (realp e)
		  (< (abs x) e)
		  (standard-numberp e))
	     (<= (abs (standard-part x)) e))
    :hints (("Goal"
	     :in-theory (enable abs))
	    ("Subgoal 3"
	     :use ((:instance standard-part-<=
			      (x (- x))
			      (y e)))
	     :in-theory (disable standard-part-<=))
	    ("Subgoal 1"
	     :use ((:instance standard-part-<=
			      (x x)
			      (y e)))
	     :in-theory (disable standard-part-<=)))))

 ;; So now we apply that lemma to our actual error term.

 (defthm standard-part-sumlist-taylor-sincos-bound
   (implies (and (realp x)
		 (realp eps) (< 0 eps) (standard-numberp eps)
		 (or (= sign 1) (= sign -1)))
	    (<= (abs
		 (standard-part
		  (sumlist
		   (taylor-sincos-list nterms
				       (n-for-taylor-sin-term x eps)
				       sign
				       x))))
		eps))
   :hints (("Goal"
	    :use ((:instance lemma-3
			     (e eps)
			     (x (sumlist
				 (taylor-sincos-list
				  nterms
				  (n-for-taylor-sin-term x eps)
				  sign
				  x)))))
	    :in-theory (disable lemma-3))))

 ;; And we do that even for the 1+counter case....

 (defthm standard-part-sumlist-taylor-sincos-bound-2
   (implies (and (realp x)
		 (realp eps) (< 0 eps) (standard-numberp eps)
		 (or (= sign 1) (= sign -1)))
	    (<= (abs
		 (standard-part
		  (sumlist
		   (taylor-sincos-list nterms
				       (+ 1 (n-for-taylor-sin-term x eps))
				       sign
				       x))))
		eps))
   :hints (("Goal"
	    :use ((:instance lemma-3
			     (e eps)
			     (x (sumlist
				 (taylor-sincos-list
				  nterms
				  (+ 1 (n-for-taylor-sin-term x eps))
				  sign
				  x)))))
	    :in-theory (disable lemma-3))))
 )

;; Foots!  We ended up with abs(error) <= eps, and we'd really rather
;; have a strict inequality.  So, we just divide our starting epsilon
;; by 2 -- old analyst's trick.  For technical reasons, we also need
;; our choice of epsilon to be less than 1, so we make sure of that
;; here.

(defun epsilon-for-sincos (eps)
  (let* ((eps1 (/ eps 2))
	 (eps2 (if (< eps1 1) eps1 1/2)))
    eps2))

;; Now here are some properties of the massaged epsilon:

(defthm epsilon-for-sincos-type-prescription
  (implies (and (realp eps)
		(< 0 eps)
		(standard-numberp eps))
	   (and (realp (epsilon-for-sincos eps))
		(< 0 (epsilon-for-sincos eps))
		(< (epsilon-for-sincos eps) 1)
		(< (epsilon-for-sincos eps) eps)
		(standard-numberp (epsilon-for-sincos eps)))))

(in-theory (disable epsilon-for-sincos))

;; So now, we can define the actual computation of num-iters.  It's as
;; before, but using the massaged value of epsilon.

(defun n-for-sincos (x eps)
  (n-for-taylor-sin-term x (epsilon-for-sincos eps)))

;; With this num-iters, we can define an approximation to sin(x)....

(defun sine-approx (x eps)
  (sumlist
   (taylor-sincos-list (n-for-sincos x eps)
		       1
		       1
		       x)))

;; ...and an approximation to cos(x).

(defun cosine-approx (x eps)
  (sumlist
   (taylor-sincos-list (n-for-sincos x eps)
		       0
		       1
		       x)))

;; And now we prove these approximations really are epsilon
;; approximation schemes!

(encapsulate
 ()

 ;; First a simple cancellation rule involving abs.

 (local
  (defthm lemma-1
    (implies (and (equal x (+ y z))
		  (< (abs z) e))
	     (< (abs (- x y)) e))
    :hints (("Goal" :in-theory (enable abs)))))

 ;; Now, we simply show we have a bound on the error term.

 (local
  (defthm standard-part-sumlist-taylor-sincos-epsilon-for-sincos
   (implies (and (realp x)
		 (realp eps) (< 0 eps) (standard-numberp eps)
		 (or (= sign 1) (= sign -1)))
	    (< (abs
		 (standard-part
		  (sumlist
		   (taylor-sincos-list
		    nterms
		    (n-for-taylor-sin-term x (epsilon-for-sincos eps))
		    sign
		    x))))
		eps))
   :hints (("Goal"

	    :use ((:instance standard-part-sumlist-taylor-sincos-bound
			     (eps (epsilon-for-sincos eps)))
		  (:instance epsilon-for-sincos-type-prescription))
	    :in-theory (disable standard-part-sumlist-taylor-sincos-bound
				epsilon-for-sincos-type-prescription)))))

 ;; And this is true even for the 1+counter case....

 (local
  (defthm standard-part-sumlist-taylor-sincos-epsilon-for-sincos-2
   (implies (and (realp x)
		 (realp eps) (< 0 eps) (standard-numberp eps)
		 (or (= sign 1) (= sign -1)))
	    (< (abs
		 (standard-part
		  (sumlist
		   (taylor-sincos-list
		    nterms
		    (+ 1 (n-for-taylor-sin-term x (epsilon-for-sincos eps)))
		    sign
		    x))))
		eps))
   :hints (("Goal"

	    :use ((:instance standard-part-sumlist-taylor-sincos-bound-2
			     (eps (epsilon-for-sincos eps)))
		  (:instance epsilon-for-sincos-type-prescription))
	    :in-theory (disable standard-part-sumlist-taylor-sincos-bound-2
				epsilon-for-sincos-type-prescription)))))

 ;; That means we can prove sine-approx is a good approximation...

 (defthm-std sine-approx-valid
   (implies (and (realp x)
		 (realp eps) (< 0 eps))
	    (< (abs (- (acl2-sine x)
		       (sine-approx x eps)))
	       eps))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance taylor-sin-valid)
		  (:instance standard-part-sumlist-taylor-sincos-list-split-2
			     (nterms (- (i-large-integer) 1))
			     (eps (epsilon-for-sincos eps))
			     (n (n-for-taylor-sin-term x (epsilon-for-sincos eps)))))
	    :in-theory (disable evenp
				taylor-sin-valid
				taylor-sincos-list-split-for-n-for-taylor-sin-term
				sumlist-taylor-sincos-list-split-2
				standard-part-sumlist-taylor-sincos-list-split-2))))

 ;; And so is cosine-approx!

 (defthm-std cosine-approx-valid
   (implies (and (realp x)
		 (realp eps) (< 0 eps))
	    (< (abs (- (acl2-cosine x)
		       (cosine-approx x eps)))
	       eps))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance taylor-cos-valid)
		  (:instance standard-part-sumlist-taylor-sincos-list-split
			     (nterms (i-large-integer))
			     (eps (epsilon-for-sincos eps))
			     (n (n-for-taylor-sin-term x (epsilon-for-sincos eps)))))
	    :in-theory (disable evenp
				taylor-cos-valid
				taylor-sincos-list-split-for-n-for-taylor-sin-term
				sumlist-taylor-sincos-list-split
				standard-part-sumlist-taylor-sincos-list-split))))
 )

