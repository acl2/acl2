;; This book develops some important theorems from trigonometry.  It
;; includes the definition of the trigonometric functions, and it
;; proves their key properties.

(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))
(local (include-book "arithmetic/abs" :dir :system))
(local (include-book "arithmetic/top" :dir :system))

(include-book "exp")
(include-book "exp-sum")
(include-book "exp-continuous")
(include-book "continuity")
(include-book "alternating-series")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;; First, we define the sine function.  sine(x) = (e^{ix}-e^{-ix})/2i.

(defun acl2-sine (x)
  (/ (- (acl2-exp (* #c(0 1) x))
	(acl2-exp (* #c(0 -1) x)))
     #c(0 2)))
(in-theory (disable (acl2-sine)))

;; Similarly, cosine(x) is defined as (e^{ix}+e^{-ix})/2.

(defun acl2-cosine (x)
  (/ (+ (acl2-exp (* #c(0 1) x))
	(acl2-exp (* #c(0 -1) x)))
     2))
(in-theory (disable (acl2-cosine)))

;; From this definition, it follows that sin(x+y)=sin(x)cos(y)+cos(x)sin(y)

(defthm sine-of-sums
  (equal (acl2-sine (+ x y))
	 (+ (* (acl2-sine x) (acl2-cosine y))
	    (* (acl2-cosine x) (acl2-sine y))))
  :hints (("Goal'"
	   :use ((:theorem (equal (+ (- (* #c(0 1/4) (acl2-exp (* #c(0 1) x))
					   (acl2-exp (* #c(0 1) y))))
				     (- (* #c(0 1/4) (acl2-exp (* #c(0 1) x))
					   (acl2-exp (* #c(0 1) y)))))
				  (- (* 2 #c(0 1/4) (acl2-exp (* #c(0 1) x))
					(acl2-exp (* #c(0 1) y))))))))))


;; Similarly, it follows that cos(x+y)=cos(x)cos(y)-sin(x)sin(y)

(defthm cosine-of-sums
  (equal (acl2-cosine (+ x y))
	 (- (* (acl2-cosine x) (acl2-cosine y))
	    (* (acl2-sine x) (acl2-sine y)))))

;; Now, we want to show that sin**2+cos**2=1.

(encapsulate
 ()

 ;; First, a non-trivial Taylor approximation of e^0 is equal to 1

 (local
  (defthm taylor-exp-list-0
    (equal (sumlist (taylor-exp-list nterms counter 0))
	   (if (or (zp nterms)
		   (not (equal counter 0)))
	       0
	     1))))

 ;; That means e^0=1, since 0 is standard.

 (defthm exp-0
   (equal (acl2-exp 0) 1))

 ;; Now, x*e^y*e^{-y} = x.

 (local
  (defthm lemma-1
    (implies (acl2-numberp y)
	     (equal (+ (* x (acl2-exp y) (acl2-exp (- y)))) (fix x)))
    :hints (("Goal"
	     :use ((:instance exp-sum (x y) (y (- y))))
	     :in-theory (disable exp-sum)))))



 ;; From that, simple algebra shows that sin**2+cos**2 = 1.

 (defthm sin**2+cos**2
   (equal (+ (* (acl2-sine x) (acl2-sine x))
	     (* (acl2-cosine x) (acl2-cosine x)))
	  1)
   :hints (("Goal'"
	    :use ((:instance lemma-1 (x 1/4) (y (* #C(0 1) X))))
	    :in-theory (disable lemma-1))))
 )

;; We define the following recursive function to recognize the even
;; numbers.

(defun nat-even-p (n)
  (if (zp n)
      t
    (not (nat-even-p (1- n)))))

;; Using that, we define a *complete* Taylor expansion for sine(x).
;; We say "complete", because it includes the "0" terms in the
;; sequence.  I.e., 0+x+0-x^3/3!+0+x^5/5!+...

(defun taylorish-sin-list (nterms counter sign x)
  (if (or (zp nterms)
	  (not (integerp counter))
	  (< counter 0))
      nil
    (if (nat-even-p counter)
	(cons 0 (taylorish-sin-list (1- nterms)
				    (1+ counter)
				    sign
				    x))
      (cons (* sign
	       (expt x counter)
	       (/ (factorial counter)))
	    (taylorish-sin-list (1- nterms)
				(1+ counter)
				(- sign)
				x)))))

;; Similarly, we define the complete Taylor expansion for cosine(x).

(defun taylorish-cos-list (nterms counter sign x)
  (if (or (zp nterms)
	  (not (integerp counter))
	  (< counter 0))
      nil
    (if (nat-even-p counter)
	(cons (* sign
		 (expt x counter)
		 (/ (factorial counter)))
	      (taylorish-cos-list (1- nterms) (1+ counter) sign x))
      (cons 0 (taylorish-cos-list (1- nterms) (1+ counter) (- sign) x)))))

;; Clearly, the complete Taylor expansion for sine(x) is a list of
;; real numbers.

(defthm real-listp-taylorish-sin-list
  (implies (and (realp x)
		(realp sign))
	   (real-listp (taylorish-sin-list nterms counter sign x)))
  :rule-classes (:rewrite :type-prescription))

;; And so its sum is a reaal number.

(defthm realp-taylorish-sin
  (implies (realp x)
	   (realp (sumlist (taylorish-sin-list nterms counter 1 x))))
  :rule-classes (:rewrite :type-prescription))

;; Likewise, the Taylor expansion of cosine is a list of real numbers.

(defthm real-listp-taylorish-cos-list
  (implies (and (realp x)
		(realp sign))
	   (real-listp (taylorish-cos-list nterms counter sign x)))
  :rule-classes (:rewrite :type-prescription))

;; And so its sum is real.

(defthm realp-taylorish-cos
  (implies (realp x)
	   (realp (sumlist (taylorish-cos-list nterms counter 1 x))))
  :rule-classes (:rewrite :type-prescription))

;; So now, we define the sign-of function, which alternates signs, but
;; only after every other element.  I.e., 1, 1, -1, -1, 1, 1, ...

(defun sign-of (counter)
  (if (zp counter)
      1
    (if (nat-even-p counter)
	(- (sign-of (1- counter)))
      (sign-of (1- counter)))))

;; Here is a simple rule to simplify sign-of(1+x).

(defthm sign-of-1+counter
  (implies (and (integerp counter)
		(<= 0 counter))
	   (equal (sign-of (+ 1 counter))
		  (if (nat-even-p counter)
		      (sign-of counter)
		    (- (sign-of counter))))))

;; A simple theorem.  (x*y)^n = x^n * y^n.

(defthm expt-x*y^n
  (equal (expt (* x y) n)
	 (* (expt x n) (expt y n))))

;; More importantly, (-x*y)^n = (-x)^n * y^n.

(defthm expt---x^n
  (equal (expt (- (* x y)) n)
	 (* (expt (- x) n) (expt y n))))

;; And so, (-i*x)^n = (-i)^n * x^n.

(defthm expt---i^n
  (equal (expt #c(0 -1) n)
	 (* (expt -1 n) (expt #c(0 1) n))))

;; Notice, -1^n = 1 if n is even and -1 if n is odd.

(defthm expt---1^n
  (implies (and (integerp n)
		(<= 0 n))
	   (equal (expt -1 n)
		  (if (nat-even-p n) 1 -1))))

;; Now, we show that the Taylor approximations we got for sine and
;; cosine agree with our definition of sine and cosine.

(encapsulate
 ()

 ;; First, we find an expression for -i^n.

 (local
  (defthm lemma-1
    (implies (and (integerp counter)
		  (<= 0 counter))
	     (equal (expt #c(0 1) counter)
		    (if (nat-even-p counter)
			(sign-of counter)
		      (* #c(0 1) (sign-of counter)))))
    :hints (("Goal"
	     :induct (expt #c(0 1) counter))
	    ("Subgoal *1/3.1"
	     :expand ((sign-of counter))
	     :in-theory (disable sign-of expt)))))

 ;; This is an important lemma.  The Taylor expansion of sine can be
 ;; computed by subtracting the Taylor expansion of e^ix and e^-ix.

 (local
  (defthm taylorish-sin-valid-lemma
    (equal
     (sumlist (taylorish-sin-list nterms counter (sign-of counter) x))
     (+ (- (* #c(0 1/2)
	      (sumlist (taylor-exp-list nterms
					counter (* #c(0 1) x)))))
	(* #c(0 1/2)
	   (sumlist (taylor-exp-list nterms
				     counter (- (* #c(0 1) x)))))))))

 ;; In particular, this holds starting at the first element of the
 ;; sequences.

 (local
  (defthm taylorish-sin-valid-lemma-useful
    (equal
     (sumlist (taylorish-sin-list nterms 0 1 x))
     (+ (- (* #c(0 1/2)
	      (sumlist (taylor-exp-list nterms
					0 (* #c(0 1) x)))))
	(* #c(0 1/2)
	   (sumlist (taylor-exp-list nterms
				     0 (- (* #c(0 1) x)))))))
    :hints (("Goal"
	     :use ((:instance taylorish-sin-valid-lemma (counter 0)))
	     :in-theory (disable taylorish-sin-valid-lemma)))))

 ;; It follows, therefore, that when x is standard, sine(x) is the
 ;; same as the standard-part of the Taylor approximation.

 (defthm taylorish-sin-valid
   (implies (standard-numberp x)
	    (equal (acl2-sine x)
		   (standard-part
		    (sumlist
		     (taylorish-sin-list
		      (i-large-integer)
		      0
		      1
		      x))))))

 ;; Now, we repeat the argument for cosine(x).  First, the sum of e^ix
 ;; and e^-ix gives something close to cosine(x).

 (local
  (defthm taylorish-cos-valid-lemma
    (equal
     (sumlist (taylorish-cos-list nterms counter (sign-of counter) x))
     (+ (* 1/2
	   (sumlist (taylor-exp-list nterms
				     counter (* #c(0 1) x))))
	(* 1/2
	   (sumlist (taylor-exp-list nterms
				     counter (- (* #c(0 1) x)))))))))

 ;; In particular, this holds true starting at the first element.

 (local
  (defthm taylorish-cos-valid-lemma-useful
    (equal
     (sumlist (taylorish-cos-list nterms 0 1 x))
     (+ (* 1/2
	   (sumlist (taylor-exp-list nterms
				     0 (* #c(0 1) x))))
	(* 1/2
	   (sumlist (taylor-exp-list nterms
				     0 (- (* #c(0 1) x)))))))
    :hints (("Goal"
	     :use ((:instance taylorish-cos-valid-lemma (counter 0)))
	     :in-theory (disable taylorish-cos-valid-lemma)))))

 ;; And so the Taylor approximation to cosine is a good approximation.

 (defthm taylorish-cos-valid
   (implies (standard-numberp x)
	    (equal (acl2-cosine x)
		   (standard-part (sumlist (taylorish-cos-list (i-large-integer) 0 1 x))))))

 )

;; We can prove, therefore, that sine(x) is real when x is real.
;; Actually, that was the whole point of the above exercise.

(defthm-std realp-sine
  (implies (realp x)
	   (realp (acl2-sine x)))
  :rule-classes (:rewrite :type-prescription))

;; Similarly, cosine(x) is real for real x.

(defthm-std realp-cosine
  (implies (realp x)
	   (realp (acl2-cosine x)))
  :rule-classes (:rewrite :type-prescription))

;; Here is another way of creating the Taylor approximations to sine
;; and cosine, but this time without the zero terms.

(defun taylor-sincos-list (nterms counter sign x)
  (if (or (zp nterms)
	  (not (integerp counter))
	  (< counter 0))
      nil
    (cons (* sign
	     (expt x counter)
	     (/ (factorial counter)))
	  (taylor-sincos-list (nfix (- nterms 2))
			      (+ counter 2)
			      (- sign)
			      x))))

;; A simple lemma.  If x is even, so is 2+x.

(defthm nat-even-p-2-+-x
  (implies (and (integerp x)
		(<= 0 x))
	   (equal (nat-even-p (+ 2 x))
		  (nat-even-p x)))
  :hints (("Goal" :do-not-induct t
	   :expand ((nat-even-p (+ 2 x))))))

;; Another simple lemma.  If x is even, so is x+2.

(defthm nat-even-p-x-+-2
  (implies (and (integerp x)
		(<= 0 x))
	   (equal (nat-even-p (+ x 2))
		  (nat-even-p x))))

;; Here is a degenerate case.  What happens when we only want one
;; element of the Taylor sine sequence.

(defthm taylorish-sin-list-1
  (equal (taylorish-sin-list 1 counter sign x)
	 (if (or (not (integerp counter)) (< counter 0))
	     nil
	   (if (nat-even-p counter)
	       (list 0)
	     (list (* sign
			(expt x counter)
			(/ (factorial counter)))))))
  :hints (("Goal" :do-not-induct t
	   :expand ((taylorish-sin-list 1 counter sign x)))))

;; Another degenerate case, but with the cosine terms.

(defthm taylorish-cos-list-1
  (equal (taylorish-cos-list 1 counter sign x)
	 (if (or (not (integerp counter)) (< counter 0))
	     nil
	   (if (nat-even-p counter)
	       (list (* sign
			(expt x counter)
			(/ (factorial counter))))
	     (list 0))))
  :hints (("Goal" :do-not-induct t
	   :expand ((taylorish-cos-list 1 counter sign x)))))

;; So now, we show that the new Taylor approximation (without the zero
;; terms) for cosine gives the same results as the old one (with the
;; zero terms).

(defthm taylorish-cos->taylor-sincos
  (implies (nat-even-p counter)
	   (equal (sumlist (taylorish-cos-list nterms counter sign x))
		  (sumlist (taylor-sincos-list nterms counter sign x))))
  :hints (("Goal" :induct (taylor-sincos-list nterms counter sign x)
           :in-theory (enable zp) ; added for v2-6
           )
	  ("Subgoal *1/2.1"
	   :expand ((taylorish-cos-list nterms counter sign x)))))

;; And here is the same result for sine.

(defthm taylorish-sin->taylor-sincos
  (implies (not (nat-even-p counter))
	   (equal (sumlist (taylorish-sin-list nterms counter sign x))
		  (sumlist (taylor-sincos-list nterms counter sign x))))
  :hints (("Goal" :induct (taylor-sincos-list nterms counter sign x))
	  ("Subgoal *1/2"
	   :expand ((TAYLORISH-sin-LIST NTERMS COUNTER SIGN X)))))

;; Now some simple rules for rewriting sign.  First,
;; sign(x*y)=sign(x)*sign(y).

(local
 (defthm sign-*
   (implies (and (realp x) (realp y))
	    (equal (sign (* x y))
		   (* (sign x) (sign y))))
   :hints (("Goal"
	    :in-theory (enable sign)))))

;; And sign(1/x) = sign(x).

(local
 (defthm sign-/
   (implies (realp x)
	    (equal (sign (/ x))
		   (sign x)))
   :hints (("Goal"
	    :in-theory (enable sign)))))

;; Sign(n!) = 1, since n!>=1.

(local
 (defthm sign-factorial
   (equal (sign (factorial x)) 1)
   :hints (("Goal"
	    :in-theory (enable sign)))))

;; And now, sign(x*x) is 0 if x is zero, and 1 otherwise.

(local
 (defthm sign-x-*-sign-x
   (implies (realp x)
	    (equal (* (sign x) (sign x))
		   (if (equal x 0) 0 1)))
   :hints (("Goal"
	    :in-theory (enable sign)))))

;; So, sign(x)*sign(x)*y is equal to 0 if x is zero and to y otherwise.

(local
 (defthm sign-x-*-sign-x-y
   (implies (realp x)
	    (equal (* (sign x) (sign x) y)
		   (if (equal x 0) 0 (fix y))))
   :hints (("Goal"
	    :in-theory (enable sign)))))

;; A typical ACL2 lemma.  This says how to get the first element of a
;; Taylor series approximation to cosine.

(defthm car-taylor-sincos-list
  (implies (and (integerp nterms)
		(< 0 nterms)
		(integerp counter)
		(<= 0 counter))
	   (equal (car (taylor-sincos-list nterms counter sign x))
		  (* sign
		     (expt x counter)
		     (/ (factorial counter))))))

;; A simple consequence:

(defthm sign-car-taylor-sincos-list
  (implies (and (integerp nterms)
		(< 0 nterms)
		(integerp counter)
		(<= 0 counter)
		(realp x)
		(realp sign)
		)
	   (equal (sign (car (taylor-sincos-list nterms counter sign x)))
		  (* (sign sign)
		     (sign (expt x counter))))))

(defthm car-taylor-sincos-list-0
  (implies (and (integerp nterms)
		(< 0 nterms)
		(integerp counter)
		(<= 0 counter)
		(realp sign)
		)
	   (equal (car (taylor-sincos-list nterms counter sign 0))
		  (if (= counter 0) sign 0))))

(defthm sign-expt
  (implies (and (realp x)
		(integerp n)
		(< 0 n))
	   (equal (sign (expt x (+ 2 n)))
		  (sign (expt x n)))))

;; And here is an important theorem.  The new Taylor approximations to
;; sine and cosine satisfy the first criterion for alternating series.

(defthm alternating-sequence-1-p-taylor-sincos
  (implies (and (realp sign)
		(realp x))
	   (alternating-sequence-1-p
	    (taylor-sincos-list nterms
				counter
				sign
				x)))
  :hints (("Subgoal *1/3"
	   :use ((:instance sign-car-taylor-sincos-list
			    (nterms (NFIX (+ -2 NTERMS)))
			    (counter (+ COUNTER 2))
			    (sign (- sign))))
	   :in-theory (enable-disable (sign)
				      (sign-car-taylor-sincos-list
				       car-taylor-sincos-list))))
  )

;; A simple rewrite rule: 1/(n+2)! = 1/(n+2) * 1/(n+1) * 1/n!

(local
 (defthm /-factorial-2-+-counter
   (implies (and (integerp counter)
		 (<= 0 counter))
	    (equal (/ (factorial (+ 2 counter)))
		   (* (/ (+ 2 counter)) (/ (+ 1 counter))
		      (/ (factorial counter)))))
   :hints (("Goal"
	    :expand ((factorial (+ 2 counter)))))))

;; We'll need a better rule for opening up the car of taylor-sincos

(defthm car-taylor-sincos-list-2
  (implies (taylor-sincos-list nterms counter sign x)
	   (equal (car (taylor-sincos-list nterms counter sign x))
		  (* sign
		     (expt x counter)
		     (/ (factorial counter)))))
  :hints (("Goal"
	   :expand ((taylor-sincos-list nterms counter sign x))
	   :do-not-induct t)))

;; Now, we want to show that the new Taylor approximations to sine and
;; cosine satisfy the second requirement of alternating series.

(encapsulate
 ()

 ;; First, if |x|=0, then x=0.

 (local
  (defthm lemma-1
    (implies (acl2-numberp sign)
	     (equal (equal (abs sign) 0)
		    (equal sign 0)))
    :hints (("Goal" :in-theory (enable abs)))))

 ;; A simple inequality that ACL2 should be able to handle :-(

 (local
  (defthm lemma-2
    (implies (and (realp x)
		  (< 0 x)
		  (<= x 2)
		  (integerp counter)
		  (<= 2 counter))
	     (< (* x x (/ (+ 1 counter))
		   (/ (+ 2 counter)))
		1))
    :hints (("Goal"
	     :use ((:instance <-*-/-left
			      (x (* x x))
			      (y (* (+ 1 counter) (+ 2 counter)))
			      (a 1)))
	     :in-theory (disable <-*-/-left
				 distributivity)))))

 ;; More simple algebra.

 (local
  (defthm lemma-3
    (implies (and (realp sign)
		  (not (equal sign 0))
		  (integerp counter)
		  (<= 2 counter)
		  (realp x)
		  (< 0 x)
		  (<= x 2))
	     (< (* x x (abs sign)
		   (/ (factorial counter))
		   (/ (+ 1 counter))
		   (/ (+ 2 counter))
		   (expt x counter))
		(* (abs sign)
		   (/ (factorial counter))
		   (expt x counter))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance <-*-left-cancel
			      (x (* x x (/ (+ 1 counter)) (/ (+ 2 counter))))
			      (y 1)
			      (z (* (abs sign)
				    (/ (factorial counter))
				    (expt x counter)))))
	     :in-theory (disable <-*-left-cancel
				 <-*-right-cancel)))))



 ;; And now, the second property for alternating sequences.  I.e.,
 ;; successive terms in the Taylor expansion of sine and cosine
 ;; decrease in magnitude.

 (defthm alternating-sequence-2-p-taylor-sincos-2
   (implies (and (realp sign)
		 (not (equal sign 0))
		 (integerp counter)
		 (integerp nterms)
		 (<= 0 nterms)
		 (<= 2 counter)
		 (realp x)
		 (< 0 x)
		 (<= x 2))
	    (alternating-sequence-2-p
	     (taylor-sincos-list nterms
				 counter
				 sign
				 x)))
   :hints (("Goal"
	    :induct (taylor-sincos-list nterms counter sign x))))
 )

;; What this means is that the Taylor sequences of sine and cosine are
;; alternating sequences.

(defthm alternating-sequence-p-taylor-sincos-2
  (implies (and (integerp nterms)
		(<= 0 nterms))
	   (alternating-sequence-p
	    (taylor-sincos-list nterms 4 1 2))))

;; Moreover, they are lists of real numbers.

(defthm real-listp-taylor-sincos-list
  (implies (and (realp sign) (realp x))
	   (real-listp (taylor-sincos-list nterms counter sign x))))

;; Here is a simple simplification for the 4th term of the Taylor
;; approximation to cosine of 2.

(defthm car-taylor-sincos-list-nterms-4-1-2
  (implies (and (integerp nterms)
		(< 0 nterms))
	   (equal (car (taylor-sincos-list nterms 4 1 2)) 2/3))
  :hints (("Goal" :do-not-induct t
	   :expand ((taylor-sincos-list nterms 4 1 2)))))

;; This means that the sum of all terms after the 4th can't be more
;; than 2/3.

(defthm remainder-taylor-cos-2
  (implies (and (integerp nterms)
		(< 0 nterms))
	   (<= (abs (sumlist
		     (taylor-sincos-list nterms 4 1 2)))
	       2/3))
  :hints (("Goal"
	   :use ((:instance sumlist-alternating-sequence
			    (x (taylor-sincos-list nterms 4 1 2)))))))

;; Now, we show how we can split the Taylor sequence for cosine(2)
;; into the first couple of terms and then the rest.

(defthm taylor-cos-2-expansion
  (implies (and (integerp nterms)
		(<= 4 nterms))
	   (equal (sumlist (taylor-sincos-list nterms 0 1 2))
		  (+ -1 (sumlist (taylor-sincos-list (+ -4 nterms) 4 1 2)))))
  :hints (("Goal" :do-not-induct t
	   :expand ((taylor-sincos-list nterms 0 1 2)))
	  ("Goal'"
	   :expand ((taylor-sincos-list (+ -2 nterms) 2 -1 2)))))

;; What this means is that cosine(2) is negative.  The expansion is
;; equal to 1 - 2^2/2! + ... = -1 + ... where the "..." term is at
;; most equal to 2/3.

(defthm sumlist-taylor-cos-2-negative
  (implies (and (integerp nterms)
		(<= 4 nterms))
	   (<= (sumlist
		(taylor-sincos-list nterms 0 1 2))
	       -1/3))
  :hints (("Goal"
	   :use ((:instance remainder-taylor-cos-2
			    (nterms (+ -4 nterms))))
	   :in-theory (disable remainder-taylor-cos-2))))

;; A simple theorem: 4 is less than a large integer!

(defthm 4-<-large-integer
  (< 4 (i-large-integer))
  :hints (("Goal"
	   :use ((:instance large->-non-large
			    (x (i-large-integer))
			    (y 4)))
	   :in-theory (disable large->-non-large))))

;; What that means is that |N-4|=N-4.

(defthm abs-large-integer-4
  (equal (abs (+ (i-large-integer) -4))
	 (+ (i-large-integer) -4))
  :hints (("Goal"
	   :use ((:instance 4-<-large-integer))
	   :in-theory (enable-disable (abs) (4-<-large-integer)))))

;; Another simple theorem!  4 < N-4

(defthm 4-<-large-integer-4
  (< 4 (+ (i-large-integer) -4))
  :hints (("Goal"
	   :use ((:instance large->-non-large
			    (x (+ (i-large-integer) -4))
			    (y 4)))
	   :in-theory (disable large->-non-large))))

;; From that, we can conclude that the Taylor approximation for cosine(2)
;; is negative.

(defthm taylor-cos-2-negative
  (<= (sumlist
       (taylor-sincos-list (i-large-integer)
			   0 1 2))
      -1/3)
  :hints (("Goal"
	   :use ((:instance sumlist-taylor-cos-2-negative
			    (nterms (i-large-integer)))
		 (:instance 4-<-large-integer))
	   :in-theory nil)))

(in-theory (disable (:executable-counterpart acl2-cosine)))

;; And therefore, cosine(2) is negative.

(defthm acl2-cos-2-negative-lemma
  (<= (acl2-cosine 2) -1/3)
  :hints (("Goal'"
	   :use ((:instance standard-part-<=
			    (x (sumlist (taylor-sincos-list (i-large-integer) 0 1 2)))
			    (y -1/3))))))

;; Emphatically, cosine(2)<0.

(defthm acl2-cos-2-negative
  (< (acl2-cosine 2) 0)
  :hints (("Goal"
	   :use ((:instance acl2-cos-2-negative-lemma))
	   :in-theory nil)))

;; A simple rule, cosine(0) = 1.

(defthm acl2-cos-0-=-1
  (equal (acl2-cosine 0) 1)
  :hints (("Goal"
	   :in-theory (disable acl2-exp taylorish-cos-valid))))

(in-theory (disable taylorish-cos-valid))

(in-theory (disable acl2-exp))

;; Now, we want to establish that cosine is a continuous function.

(encapsulate
 ()

 ;; First, some algebra.  Given x1, x2, y1, y2 with x1/2 + x2/2 close
 ;; to y1/2+y2/2, then x1+x2 is close to y1+y2.

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp x1) (acl2-numberp x2)
		  (acl2-numberp y1) (acl2-numberp y2))
	     (equal (i-close (+ (* 1/2 x1) (* 1/2 x2))
			     (+ (* 1/2 y1) (* 1/2 y2)))
		    (i-close (+ x1 x2)
			     (+ y1 y2))))
    :hints (("Goal"
	     :in-theory (enable i-close))
	    ("Goal'"
	     :use ((:instance
		    (:theorem
		     (implies (acl2-numberp x)
			      (equal (i-small (* 1/2 x))
				     (i-small x))))
		    (x (+ x1 x2 (- y1) (- y2))))))
	    ("Subgoal 1"
	     :cases ((i-small x)))
	    ("Subgoal 1.2"
	     :use ((:instance limited*small->small
			      (x 2)
			      (y (* 1/2 x))))
	     :in-theory (disable limited*small->small))
	    ("Subgoal 1.1"
	     :use ((:instance limited*small->small
			      (x 1/2)
			      (y x)))
	     :in-theory (disable limited*small->small)))))

 ;; Now, if x1 is close to y1 and x2 is close to y2, then x1+x2 is
 ;; close to y1+y2.

 (local
  (defthm lemma-2
    (implies (and (i-close x1 y1)
		  (i-close x2 y2))
	     (i-close (+ x1 x2)
		      (+ y1 y2)))
    :hints (("Goal"
	     :in-theory (enable i-close)))))

 ;; Similarly, if x is limited and y1 is close to y2, then x*y1 is
 ;; close to x*y2.

 (local
  (defthm lemma-3
    (implies (and (i-limited x)
		  (i-close y1 y2))
	     (i-close (* x y1) (* x y2)))
    :hints (("Goal"
	     :in-theory (enable i-close))
	    ("Goal''"
	     :use ((:instance limited*small->small
			      (y (+ y1 (- y2)))))
	     :in-theory (disable limited*small->small)))))

 ;; Therefore, cosine is continuous.

 (defthm cosine-continuous
   (implies (and (standard-numberp x)
		 (i-close x y))
	    (i-close (acl2-cosine x)
		     (acl2-cosine y)))
   :hints (("Goal"
	    :use ((:instance lemma-2
			     (x1 (acl2-exp (* #c(0 1) x)))
			     (x2 (acl2-exp (- (* #c(0 1) x))))
			     (y1 (acl2-exp (* #c(0 1) y)))
			     (y2 (acl2-exp (- (* #c(0 1) y))))))
	    :in-theory (disable lemma-2)))))

; Let's establish also that sine is continuous

(encapsulate
 ()

 ;; First, some algebra.  Given x1, x2, y1, y2 with x1/2i - x2/2i close
 ;; to y1/2i-y2/2i, then x1-x2 is close to y1-y2.

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp x1) (acl2-numberp x2)
		  (acl2-numberp y1) (acl2-numberp y2))
	     (equal (i-close (- (* #c(0 1/2) x1) (* #c(0 1/2) x2))
			     (- (* #c(0 1/2) y1) (* #c(0 1/2) y2)))
		    (i-close (- x1 x2)
			     (- y1 y2))))
    :hints (("Goal"
	     :in-theory (enable i-close))
	    ("Goal'"
	     :use ((:instance
		    (:theorem
		     (implies (acl2-numberp x)
			      (equal (i-small (* #c(0 1/2) x))
				     (i-small x))))
		    (x (+ x1 (- x2) (- y1) y2)))))
	    ("Subgoal 1"
	     :cases ((i-small x)))
	    ("Subgoal 1.2"
	     :use ((:instance limited*small->small
			      (x #c(0 2))
			      (y (* #c(0 1/2) x))))
	     :in-theory (disable limited*small->small))
	    ("Subgoal 1.1"
	     :use ((:instance limited*small->small
			      (x #c(0 1/2))
			      (y x)))
	     :in-theory (disable limited*small->small)))))

 ;; Now, if x1 is close to y1 and x2 is close to y2, then x1+x2 is
 ;; close to y1+y2.

 (local
  (defthm lemma-2
    (implies (and (i-close x1 y1)
		  (i-close x2 y2))
	     (i-close (+ x1 x2)
		      (+ y1 y2)))
    :hints (("Goal"
	     :in-theory (enable i-close)))))

 ;; Similarly, if x is limited and y1 is close to y2, then x*y1 is
 ;; close to x*y2.

 (local
  (defthm lemma-3
    (implies (and (i-limited x)
		  (i-close y1 y2))
	     (i-close (* x y1) (* x y2)))
    :hints (("Goal"
	     :in-theory (enable i-close))
	    ("Goal''"
	     :use ((:instance limited*small->small
			      (y (+ y1 (- y2)))))
	     :in-theory (disable limited*small->small)))))

 ;; Therefore, sine is continuous.

 (defthm sine-continuous
   (implies (and (standard-numberp x)
		 (i-close x y))
	    (i-close (acl2-sine x)
		     (acl2-sine y)))
   :hints (("Goal"
	    :use ((:instance lemma-2
			     (x1 (- (acl2-exp (* #c(0 1) x))))
			     (x2 (acl2-exp (- (* #c(0 1) x))))
			     (y1 (- (acl2-exp (* #c(0 1) y))))
			     (y2 (acl2-exp (- (* #c(0 1) y)))))
		  (:instance lemma-1
			     (x2 (ACL2-EXP (* #C(0 1) X)))
			     (x1 (ACL2-EXP (- (* #C(0 1) X))))
			     (y2 (ACL2-EXP (* #C(0 1) Y)))
			     (y1 (ACL2-EXP (- (* #C(0 1) Y)))))
		  )
	    :in-theory (disable lemma-1 lemma-2 taylorish-sin-valid))))

)

;; This function will find a root of the cosine function.

(defun find-zero-cos-n-2 (a z i n eps)
  (declare (xargs :measure (nfix (1+ (- n i)))))
  (if (and (realp a)
	   (integerp i)
	   (integerp n)
	   (< i n)
	   (realp eps)
	   (< 0 eps)
	   (< z (acl2-cosine (+ a eps))))
      (find-zero-cos-n-2 (+ a eps) z (1+ i) n eps)
    (realfix a)))

(local
 (defthm open-up-in-interval-nil-nil
     (equal (inside-interval-p x (interval nil nil))
	    (realp x))
   :hints (("Goal"
	    :in-theory (enable interval-definition-theory)))))


(defthm limited-find-zero-cos-2-body
  (implies (and (i-limited a)
		(i-limited b)
		(realp b)
		(realp z))
	   (i-limited (find-zero-cos-n-2 a
					 z
					 0
					 (i-large-integer)
					 (+ (- (* (/ (i-large-integer)) a))
					    (* (/ (i-large-integer)) b)))))
   :hints (("Goal"
	    :by (:functional-instance limited-find-zero-2-body
					(rcfn (lambda (x) (acl2-cosine (realfix x))))
					(rcfn-domain (lambda () (interval nil nil)))
					(find-zero-n-2 find-zero-cos-n-2))
; Added after v4-3 by Matt K.:
            :in-theory (disable (tau-system))
            )
	   ("Subgoal 4"
	    :in-theory (disable acl2-cosine))
	   ("Subgoal 3"
	    :in-theory (enable acl2-exp))))


;; This will find the root for cosine in the range [a,b)

(defun-std find-zero-cos-2 (a b z)
  (if (and (realp a)
	   (realp b)
	   (realp z)
	   (< a b))
	(standard-part (find-zero-cos-n-2 a
					  z
					  0
					  (i-large-integer)
					  (/ (- b a) (i-large-integer))))
    0))
(in-theory (disable (:executable-counterpart find-zero-cos-2)))

(defthm find-zero-cosine
  (and (realp (find-zero-cos-2 0 2 0))
       (< 0 (find-zero-cos-2 0 2 0))
       (< (find-zero-cos-2 0 2 0) 2)
       (equal (acl2-cosine (find-zero-cos-2 0 2 0)) 0))
  :hints (("Goal"
	   :use ((:instance
		  (:functional-instance intermediate-value-theorem-2
					(rcfn (lambda (x) (acl2-cosine (realfix x))))
					(rcfn-domain (lambda () (interval nil nil)))
					(find-zero-2 find-zero-cos-2)
					(find-zero-n-2 find-zero-cos-n-2))
		  (a 0)
		  (b 2)
		  (z 0)))
	   :in-theory (disable intermediate-value-theorem-2
			       taylorish-cos-valid
			       acl2-cosine))))

#|
;; And so, 2*standard-part(r) is standard, since r is limited.

(encapsulate
 ()

 ;; First some silly algebra.....

 (local
  (defthm lemma-1
    (equal (+ (- (* n 0)) (* n 2))
	   (* n 2))))

 (defthm acl2-pi-justification
   (standard-numberp (* 2 (find-zero-cos-2 0 2 0)))
   :hints (("Goal"
	    :use ((:instance limited-find-zero-cos-2-body
			     (a 0)
			     (b 2)
			     (z 0)))
	    :in-theory (disable limited-find-zero-cos-2-body))))
 )
|#

;; So now, we define pi as twice the root of cosine found above.  Note
;; that cosine has a root at pi/2.

(defun acl2-pi ()
  (* 2 (find-zero-cos-2 0 2 0)))

(in-theory (disable (:executable-counterpart acl2-pi)))
(in-theory (disable find-zero-cos-2))

;; It follows that pi is real and positive.

(defthm acl2-pi-type-prescription
  (and (realp (acl2-pi))
       (< 0 (acl2-pi)))
  :hints (("Goal"
	   :use ((:instance find-zero-cosine))
	   :in-theory (disable find-zero-cosine)))
  :rule-classes (:rewrite :type-prescription))

;; Moreover, pi is less than 4.

(defthm acl2-pi-gross-upper-bound
  (< (acl2-pi) 4)
  :hints (("Goal"
	   :use ((:instance find-zero-cosine))
	   :in-theory (disable find-zero-cosine))))

;; Easily, we can see that cosine(pi/2) = 0.

(defthm cosine-pi/2
  ;; For v2-6, (* (acl2-pi) 1/2) has been replaced by (* 1/2 (acl2-pi)) because
  ;; of changes in term-order.
  (equal (acl2-cosine (* 1/2 (acl2-pi))) 0))

;; But how do we know that we have the right value of pi?  What we
;; want to show is that there is only one root of cosine between 0 and
;; 2.  First, we show that the x^5 term of sine(x) is bounded by
;; x^5/120 (since 5!=120).

(defthm car-taylor-sincos-list-nterms-5-1-x
  (implies (and (integerp nterms)
		(< 0 nterms))
	   (equal (car (taylor-sincos-list nterms 5 1 x))
		  (* 1/120 (expt x 5))))
  :hints (("Goal" :do-not-induct t
	   :expand ((taylor-sincos-list nterms 5 1 x)))))


;; So now, we show that for 0<=x<=2, the sum of all the Taylor terms
;; after the x^5 term is bounded by 4/15.

(encapsulate
 ()

 ;; First, we show that if x<y, then x^n < y^n.

 (local
  (defthm expt-upper-bound
    (implies (and (integerp n)
		  (<= 0 n)
		  (realp x)
		  (realp y)
		  (<= 0 x)
		  (<= x y))
	     (<= (expt x n) (expt y n)))
    :rule-classes (:linear :rewrite)))

 ;; Moreover, for positive x, 0 <= x^n.

 (local
  (defthm expt-lower-bound
    (implies (and (integerp n)
		  (<= 0 n)
		  (realp x)
		  (<= 0 x))
	     (<= 0 (expt x n)))
        :rule-classes (:linear :rewrite)))

 ;; That gives a bound for x^5 between 0 and 32 for x in [0,2].

 (defthm expt-x-5-bounds
   (implies (and (realp x)
		 (<= 0 x)
		 (<= x 2))
	    (and (<= 0 (expt x 5))
		 (<= (expt x 5) 32)))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance expt-upper-bound (x x) (y 2) (n 5))
		  (:instance expt-lower-bound (n 5)))
	    :in-theory (disable expt-lower-bound expt-upper-bound)))
        :rule-classes (:linear :rewrite))

 ;; And so the bound for all the Taylor approximation terms after the
 ;; x^5 term is bounded by the x^5 term, which is bounded by x^5/120
 ;; <= 32/120 = 4/15.

 (defthm remainder-taylor-sin-x
   (implies (and (integerp nterms)
		 (< 0 nterms)
		 (realp x)
		 (< 0 x)
		 (<= x 2))
	    (<= (abs (sumlist (taylor-sincos-list nterms 5 1 x))) 4/15))
   :hints (("Goal" :do-not-induct t
	    :use ((:instance sumlist-alternating-sequence
			     (x (taylor-sincos-list nterms 5 1 x)))))))

 )

;; So now, we can split the Taylor expansion of sine into the terms
;; into x - x^3/6 + ... where ... has all terms starting with the x^5
;; term, and hence the sum of ... is at most 4/15.

(defthm taylor-sin-x-expansion
  (implies (and (integerp nterms)
		(<= 4 nterms))
	   (equal (sumlist (taylor-sincos-list nterms 1 1 x))
		  (+ x (* -1/6 (expt x 3))
		     (sumlist (taylor-sincos-list (+ -4 nterms) 5 1 x)))))
  :hints (("Goal" :do-not-induct t
	   :expand ((taylor-sincos-list nterms 1 1 x))
	   :in-theory (disable functional-commutativity-of-minus-*-left))
	  ("Goal'"
	   :expand ((taylor-sincos-list (+ -2 nterms) 3 -1 x)))))

;; So now, we show that the Taylor approximation to sine(x) is positive
;; for x in [0,2].

(encapsulate
 ()

 ;; First, for x in (0,2), x^2 < 4.

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (< 0 x)
		  (< x 2))
	     (< (* x x) 4))
    :hints (("Goal"
	     :use ((:instance <-*-right-cancel
			      (x x)
			      (y 2)
			      (z x))
		   (:instance <-*-right-cancel
			      (x x)
			      (y 2)
			      (z 2)))
	     :in-theory (disable <-*-right-cancel
				 <-*-left-cancel
				 *-preserves->-for-nonnegatives-1)))))

 ;; And that means 0 <= x - x^3/3!

 (local
  (defthm lemma-2
    (implies (and (realp x)
		  (< 0 x)
		  (< x 2))
	     (<= 0 (+ x (- (* 1/6 x x x)))))
    :hints (("Goal''"
	     :use ((:instance <-*-right-cancel
			      (y (* x x))
			      (x 6)
			      (z x))
		   (:instance lemma-1))
	     :in-theory (disable <-*-right-cancel
				 <-*-left-cancel
				 lemma-1)))
    :rule-classes (:rewrite :linear)))


 ;; When a_1, a_2, ... is an alternating sequence and a_1 >= 0, then
 ;; the sum of the a_i is also >= 0.

 (local
  (defthm lemma-3
    (implies (and (alternating-sequence-p x)
		  (real-listp x)
		  (not (null x))
		  (<= 0 (car x)))
	     (<= 0 (sumlist x)))
    :hints (("Goal"
	     :use ((:instance sumlist-alternating-sequence-lemma)
		   (:instance sumlist-alternating-sequence))
	     :in-theory (enable-disable (abs)
					(sumlist-alternating-sequence))))))


 ;; And for 0<=x<=2 the Taylor approximation of sine starting with the
 ;; x^5 term is alternating.

 (defthm alternating-sequence-p-taylor-sincos-x
   (implies (and (integerp nterms)
		 (<= 0 nterms)
		 (realp x)
		 (< 0 x)
		 (<= x 2))
	    (alternating-sequence-p (taylor-sincos-list nterms 5 1 x))))

 ;; Therefore, the sum of that Taylor subsequence is >= 0.

 (local
  (defthm lemma-4
    (implies (and (integerp nterms)
		  (< 4 nterms)
		  (realp x)
		  (< 0 x)
		  (<= x 2))
	     (<= 0 (sumlist (taylor-sincos-list (+ -4 nterms) 5 1 x))))
    :hints (("Goal"
	     :use ((:instance lemma-3
			      (x (taylor-sincos-list (+ -4 nterms) 5 1 x))))
	     :in-theory (disable lemma-3)))
    :rule-classes (:linear :rewrite)))

 ;; And therefore, the sine(x) is >= 0 in that range, since its the
 ;; sum of two non-negative numbers.

 (defthm sumlist-taylor-sin-x-positive
   (implies (and (integerp nterms)
		 (<= 4 nterms)
		 (realp x)
		 (< 0 x)
		 (<= x 2))
	    (<= 0 (sumlist (taylor-sincos-list nterms 1 1 x))))
   :hints (("Goal" :do-not-induct t)
	   ("Goal'"
	    :use ((:instance lemma-2)
		  (:instance lemma-4))
	    :in-theory (disable lemma-2 lemma-4))))
 )

;; What this means, of course, is that the Taylor approximation to
;; sine is negative for x in [0,2].

(defthm taylor-sin-x-positive
  (implies (and (realp x)
		(< 0 x)
		(<= x 2))
           ;; Note:  In v2-6 the term (+ (i-large-integer) -1) was
           ;; replaced below by (+ -1 (i-large-integer)) because of
           ;; changes in term-order.  The :use hint was changed similarly.
	   (<= 0 (sumlist (taylor-sincos-list (+ -1 (i-large-integer))
					      1 1 x))))
  :hints (("Goal"
	   :use ((:instance sumlist-taylor-sin-x-positive
			    (nterms (+ -1 (i-large-integer))))
		 (:instance 4-<-large-integer))
	   :in-theory nil)))

;; And therefore, sine(x) >= 0 for all x in [0,2].

(defthm-std acl2-sin-x-positive
  (implies (and (realp x)
		(< 0 x)
		(<= x 2))
	   (<= 0 (acl2-sine x)))
  :hints (("Goal''"
	   :expand (taylorish-sin-list (i-large-integer) 0 1 x))
	  ("Goal'''"
	   :use ((:instance standard-part-<=
			    (x 0)
			    (y (sumlist (taylor-sincos-list (+ -1 (i-large-integer)) 1 1 x))))))))

(in-theory (disable acl2-pi))

;; In particular, sine(pi/2) >= 0.

(defthm sine-pi/2-positive
  (<= 0 (acl2-sine (* 1/2 (acl2-pi))))
  :hints (("Goal"
	   :use ((:instance acl2-pi-gross-upper-bound)
		 (:instance acl2-sin-x-positive
			    (x (* 1/2 (acl2-pi)))))
	   :in-theory (disable acl2-sin-x-positive
			       acl2-pi-gross-upper-bound
			       acl2-sine))))

;; We now wish to show that sine(pi/2) = 1.

(encapsulate
 ()

 ;; A silly lemma: if x<y, x*x < y*y.

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (realp y)
		  (<= 0 x)
		  (<= 0 y)
		  (< x y))
	     (< (* x x) (* y y)))
    :hints(("Goal"
            :cases ((< (* x x) (* x y)))))))

 ;; Moreover, if x^2<y^2, then x<y.

 (local
  (defthm x*x-<-y*y
    (implies (and (realp x)
		  (realp y)
		  (<= 0 x)
		  (<= 0 y))
	     (equal (< (* x x) (* y y))
		    (< x y)))
    :hints (("Goal"
	     :cases ((< x y) (= x y) (< y x))))))

 ;; So, if x^2=1, then x=1.

 (local
  (defthm lemma-2
    (implies (and (realp x)
		  (<= 0 x)
		  (equal (* x x) 1))
	     (equal (equal x 1) t))
    :hints (("Goal"
	     :cases ((< x 1) (= x 1)))
	    ("Subgoal 3"
	     :use ((:instance x*x-<-y*y (x 1) (y x)))
	     :in-theory (disable x*x-<-y*y))
	    ("Subgoal 2"
	     :use ((:instance x*x-<-y*y (x x) (y 1)))
	     :in-theory (disable x*x-<-y*y)))))


 ;; That means that sine(pi/2)=1, since sine(pi/2)=0, and sin**2+cos**2=1.

 (defthm sine-pi/2
   (equal (acl2-sine (* 1/2 (acl2-pi))) 1)
   :hints (("Goal"
	    :use ((:instance sine-pi/2-positive)
		  (:instance sin**2+cos**2
			     (x (* 1/2 (acl2-pi))))
		  (:instance lemma-2
			     (x (acl2-sine (* 1/2 (acl2-pi))))))
	    :in-theory (disable sine-pi/2-positive
				sin**2+cos**2
				acl2-sine
				acl2-cosine
				lemma-2))))

 )

;; Here is a silly rule: 1/2*x + 1/2*x = x.

(defthm sum-halves
  (implies (acl2-numberp x)
	   (equal (+ (* 1/2 x) (* 1/2 x)) x)))

;; The same rule, only x*1/2 + x*1/2 = x.

(defthm sum-halves-right
  (implies (acl2-numberp x)
	   (equal (+ (* x 1/2) (* x 1/2)) x)))

;; And now, we can conclude that sine(pi)=0, using the sine-of-sums formula.

(defthm sine-pi
  (equal (acl2-sine (acl2-pi)) 0)
  :hints (("Goal"
	   :use ((:instance sine-of-sums
			    (x (* 1/2 (acl2-pi)))
			    (y (* 1/2 (acl2-pi)))))
	   :in-theory (disable sine-of-sums acl2-sine acl2-cosine))))

;; Similarly, cosine(pi)=-1, using the cosine-of-sums formula.

(defthm cosine-pi
  (equal (acl2-cosine (acl2-pi)) -1)
  :hints (("Goal"
	   :use ((:instance cosine-of-sums
			    (x (* 1/2 (acl2-pi)))
			    (y (* 1/2 (acl2-pi)))))
	   :in-theory (disable cosine-of-sums acl2-sine acl2-cosine))))

;; And now, we can prove an important lemma.  The sine(x) is positive
;; in the range (0,pi/2).  This will show that cosine(x) > 0 in the
;; range (0,pi/2) and therefore pi/2 is the first root of cosine in
;; [0,2].  I.e., our definition of pi is the usual one.

(encapsulate
 ()

 ;; Simple algebra.  If y is in (0,1), then x*y<x.

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (< 0 x)
		  (realp y)
		  (< 0 y)
		  (< y 1))
	     (< (* x y) x))))

 ;; If x<2 and n>=1, then x*x/((1+n)*(2+n)) < 1, since x<1+n and x<2+n.

 (local
  (defthm lemma-2
    (implies (and (realp x) (< 0 x) (< x 2) (integerp n) (<= 1 n))
	     (< (* x x (/ (+ 1 n)) (/ (+ 2 n)))
		1))
    :hints (("Goal"
	     :use ((:instance <-*-right-cancel
			      (z (* (/ (+ 1 n))
				    (/ (+ 2 n))))
			      (x (* x x))
			      (y (* (+ 1 n) (+ 2 n)))))
	     :in-theory (disable <-*-right-cancel DISTRIBUTIVITY)))
    :rule-classes (:rewrite :linear)))

 ;; So, x^{n+2}/(n+2)! < x^n/n!

 (local
  (defthm lemma-3
    (implies (and (integerp counter)
		  (<= 1 counter)
		  (realp x)
		  (< 0 x)
		  (< x 2))
	     (< (* (expt x (+ counter 2))
		   (/ (factorial (+ counter 2))))
		(* (expt x counter)
		   (/ (factorial counter)))))
    :hints (("Goal'"
	     :do-not-induct t
	     :use ((:instance lemma-1
			      (x (expt x counter))
			      (y (* x x
				    (/ (+ 1 counter))
				    (/ (+ 2 counter))))))
	     :in-theory (disable lemma-1)))
    :rule-classes (:rewrite :linear)))

 ;; And that means 0 < x^n/n! - x^{n+2}/(n+2)!

 (local
  (defthm lemma-4
    (implies (and (integerp counter)
		  (<= 1 counter)
		  (realp x)
		  (< 0 x)
		  (< x 2))
	     (< 0 (+ (* (expt x counter)
			(/ (factorial counter)))
		     (- (* (expt x (+ counter 2))
			   (/ (factorial (+ counter 2))))))))
    :hints (("Goal"
	     :use ((:instance lemma-3))
	     :in-theory (disable lemma-3)))
    :rule-classes (:rewrite :linear)))


 ;; 4+n is even when n is even.

 (local
  (defthm nat-even-p-4-+-x
    (implies (and (integerp x)
		  (<= 0 x))
	     (equal (nat-even-p (+ 4 x))
		    (nat-even-p x)))
    :hints (("Goal" :do-not-induct t
	     :expand ((nat-even-p (+ 4 x))))
	    ("Subgoal 2"
	     :expand ((nat-even-p (+ 3 x))))
	    ("Subgoal 1"
	     :expand ((nat-even-p (+ 3 x)))))))

 ;; Same goes for n+4.

 (local
  (defthm nat-even-p-x-+-4
    (implies (and (integerp x)
		  (<= 0 x))
	     (equal (nat-even-p (+ x 4))
		    (nat-even-p x)))))

 ;; This function is here only to serve as the basis of an induction
 ;; hint.

 (local
  (defun induction-hint (nterms counter)
    (if (or (zp nterms)
	    (not (integerp counter))
	    (< counter 0))
	0
      (if (< nterms 2)
	  1
	(+ 2 (induction-hint (nfix (- nterms 4)) (+ counter 4)))))))

 ;; And now, the Taylor sine approximation is >= 0 when x is in the
 ;; range (0, x).

 (local
  (defthm taylor-sine-non-negative-in-0-2
    (implies (and (not (nat-even-p counter))
		  (realp x)
		  (< 0 x)
		  (< x 2))
	     (<= 0 (sumlist (taylor-sincos-list nterms counter 1 x))))
    :hints (("Goal"
	     :induct (induction-hint nterms counter))
	    ("Subgoal *1/3.2"
	     :expand ((taylor-sincos-list nterms counter 1 x)))
	    ("Subgoal *1/3.2.2''"
	     :use ((:instance lemma-4))
	     :in-theory (disable lemma-3 lemma-4))
	    ("Subgoal *1/3.1"
	     :expand ((taylor-sincos-list nterms counter 1 x)))
	    ("Subgoal *1/3.1'"
	     :use ((:instance (:theorem (implies (and (realp x) (realp y)
						      (< 0 x) (< 0 y))
						 (< 0 (+ x y))))
			      (x (+ (* (expt x counter)
				       (/ (factorial counter)))
				    (- (* (expt x (+ counter 2))
					  (/ (factorial (+ counter 2)))))))
			      (y (sumlist (taylor-sincos-list (+ -4 nterms)
							      (+ 4 counter)
							      1 x))))
		   (:instance lemma-4))
	     :in-theory (disable lemma-3 lemma-4))
	    ("Subgoal *1/2'''"
	     :expand ((taylor-sincos-list 1 counter 1 x))))
    :rule-classes (:rewrite :linear)))

 ;; Actually, it is positive for x in the range (0,2).

 (local
  (defthm taylor-sine-positive-in-0-2
    (implies (and (not (nat-even-p counter))
		  (integerp nterms)
		  (< 0 nterms)
		  (realp x)
		  (< 0 x)
		  (< x 2))
	     (< 0 (sumlist (taylor-sincos-list nterms counter 1 x))))
    :hints (("Goal" :do-not-induct t
	     :cases ((= nterms 1) (= nterms 2) (= nterms 3) (<= 4 nterms)))
	    ("Subgoal 4''"
	     :expand ((taylor-sincos-list 1 counter 1 x)))
	    ("Subgoal 3''"
	     :expand ((taylor-sincos-list 2 counter 1 x)))
	    ("Subgoal 2''"
	     :expand ((taylor-sincos-list 3 counter 1 x)))
	    ("Subgoal 2'4'"
	     :expand ((taylor-sincos-list 1 (+ 2 counter) -1 x)))
	    ("Subgoal 2'5'"
	     :use ((:instance lemma-4))
	     :in-theory (disable lemma-3 lemma-4))
	    ("Subgoal 1"
	     :expand ((taylor-sincos-list nterms counter 1 x)))
	    ("Subgoal 1.2"
	     :expand ((taylor-sincos-list (+ -2 nterms)
					  (+ 2 counter)
					  -1 x)))
	    ("Subgoal 1.2'"
	     :use ((:instance lemma-4)
		   (:instance taylor-sine-non-negative-in-0-2
			      (nterms (+ -4 nterms))
			      (counter (+ 4 counter))))
	     :in-theory (disable lemma-3 lemma-4 taylor-sine-non-negative-in-0-2
				 /-cancellation-on-left
				 <-*-/-right-commuted)))
    :rule-classes (:rewrite :linear)))

 ;; More to the point, x - x^3/6 < Taylor(sine(x)).

 (local
  (defthm taylor-sine-positive-in-0-2-useful
    (implies (and (integerp nterms)
		  (< 4 nterms)
		  (realp x)
		  (< 0 x)
		  (< x 2))
	     (< (+ x (- (* 1/6 x x x)))
		(sumlist (taylor-sincos-list nterms 1 1 x))))
    :hints (("Goal" :do-not-induct t
	     :expand ((taylor-sincos-list nterms 1 1 x)))
	    ("Goal'" :do-not-induct t
	     :expand ((taylor-sincos-list (+ -2 nterms) 3 -1 x))))))

 ;; A silly rule, 5 < large-integer.

 (local
  (defthm 5-<-i-large-integer
    (< 4 (+ -1 (i-large-integer)))
    :hints (("Goal"
	     :use ((:instance large->-non-large
			      (x (+ -1 (i-large-integer)))
			      (y 4)))
	     :in-theory (disable large->-non-large)))))

 ;; So taking standard parts, x - x^3/6 < standard-part(Taylor(sine(x))).

 (local
  (defthm taylor-sine-positive-in-0-2-really-useful
    (implies (and (realp x)
		  (standard-numberp x)
		  (< 0 x)
		  (< x 2))
	     (<= (+ x (- (* 1/6 x x x)))
		 (standard-part
		  (sumlist (taylor-sincos-list (+ -1 (i-large-integer)) 1 1 x)))))
    :hints (("Goal" :do-not-induct t
	     :use ((:instance standard-part-<=
			      (x (+ x (- (* 1/6 x x x))))
			      (y (sumlist
				  (taylor-sincos-list (+ -1 (i-large-integer))
						      1 1 x))))
		   (:instance taylor-sine-positive-in-0-2-useful
			      (nterms (+ -1 (i-large-integer)))))
	     :in-theory (disable standard-part-<=
				 taylor-sine-positive-in-0-2-useful)))))


 ;; If x<y, x*x<y*y.

 (local
  (defthm lemma-5
    (implies (and (realp x)
		  (realp y)
		  (<= 0 x)
		  (<= 0 y)
		  (< x y))
	     (< (* x x) (* y y)))
    :hints(("Goal"
            :cases ((< (* x x) (* x y)))))))

 ;; So we can conclude that 0 < standard-part(Taylor(sine(x))), for x
 ;; in (0, 2).

 (local
  (defthm taylor-sine-positive-in-0-2-most-useful
    (implies (and (realp x)
		  (standard-numberp x)
		  (< 0 x)
		  (< x 2))
	     (< 0
		(standard-part
		 (sumlist (taylor-sincos-list (+ -1 (i-large-integer)) 1 1 x)))))
    :hints (("Goal"
	     :use ((:instance taylor-sine-positive-in-0-2-really-useful)
		   (:theorem (implies (and (realp x) (< 0 x) (< x 2))
				      (< 0 (+ x (- (* 1/6 x x x)))))))
	     :in-theory (disable taylor-sine-positive-in-0-2-really-useful))
	    ("Subgoal 1'"
	     :use ((:instance <-*-right-cancel
			      (x (* x x))
			      (y 6)
			      (z x))
		   (:instance lemma-5 (x x) (y 2)))
	     :in-theory (disable <-*-right-cancel lemma-5)))))


 ;; And so 0<sine(x) for x in (0,2).

 (defthm-std sine-positive-in-0-2
   (implies (and (realp x)
		 (< 0 x)
		 (< x 2))
	    (< 0 (acl2-sine x)))
   :hints (("Goal''"
	    :expand ((taylorish-sin-list (i-large-integer) 0 1 x)))))

 ;; In particular, 0<sine(x) for x in (0,pi/2).

 (defthm sine-positive-in-0-pi/2
   (implies (and (realp x)
		 (< 0 x)
		 (< x (* 1/2 (acl2-pi))))
	    (< 0 (acl2-sine x)))
   :hints (("Goal"
	    :use ((:instance sine-positive-in-0-2)
		  (:instance acl2-pi-gross-upper-bound))
	    :in-theory (disable sine-positive-in-0-2
				acl2-pi-gross-upper-bound
				acl2-sine))))
 )

(defthm pi-between-2-4
  (and (<= 2 (acl2-pi))
       (< (acl2-pi) 4))
  :hints (("Goal"
	   :use ((:instance sine-positive-in-0-2 (x (acl2-pi)))
		 (:instance acl2-pi-type-prescription)
		 (:instance acl2-pi-gross-upper-bound)
		 (:instance sine-pi))
	   :in-theory nil)))

;; Here's a simple theorem, cosine(-x) = cosine(x).

(defthm cos-uminus
  (equal (acl2-cosine (- x))
	 (acl2-cosine (fix x))))

;; On the other hand, sine(-x) = -sine(x).

(encapsulate
 ()

 ;; First, if x is not a number, then x*y = 0.

 (local
  (defthm lemma-1
    (implies (not (acl2-numberp x))
	     (equal (* y x) 0))))

 ;; And now, sine(-x) = -sine(x).

 (defthm sin-uminus
   (equal (acl2-sine (- x))
	  (- (acl2-sine (fix x))))
   :hints (("Goal"
	    :in-theory (disable taylorish-sin-valid))))
 )

(in-theory (disable taylorish-sin-valid))
(in-theory (disable taylorish-cos-valid))

;; Here is the "completion" theorem for sine.  If x is not a number,
;; then sine(x)=sine(0)=0.

(defthm sin-completion
  (implies (not (acl2-numberp x))
	   (equal (acl2-sine x)
		  (acl2-sine 0))))

;; And here is the "completion" theorem for cosine.  If x is not a number,
;; then cosine(x)=cosine(0)=1.

(defthm cos-completion
  (implies (not (acl2-numberp x))
	   (equal (acl2-cosine x)
		  (acl2-cosine 0))))

(in-theory (disable acl2-sine acl2-cosine))

;; Now, sine(x+pi/2) = cosine(x).

(defthm sin-pi/2+x
  (equal (acl2-sine (+ (* 1/2 (acl2-pi)) x))
	 (acl2-cosine x)))

;; sine(pi/2-x) = cosine(x).

(defthm sin-pi/2-x
  (equal (acl2-sine (+ (* 1/2 (acl2-pi)) (- x)))
	 (acl2-cosine x)))

;; cosine(pi/2+x) = -sine(x).

(defthm cos-pi/2+x
  (equal (acl2-cosine (+ (* 1/2 (acl2-pi)) x))
	 (- (acl2-sine x))))

;; cosine(pi/2-x) = sine(x).

(defthm cos-pi/2-x
  (equal (acl2-cosine (+ (* 1/2 (acl2-pi)) (- x)))
	 (acl2-sine x)))

;; sine(pi+x) = -sine(x).

(defthm sin-pi+x
  (equal (acl2-sine (+ (acl2-pi) x))
	 (- (acl2-sine x))))

;; sine(pi-2) = sine(x).

(defthm sin-pi-x
  (equal (acl2-sine (+ (acl2-pi) (- x)))
	 (acl2-sine x)))

;; cosine(pi+x) = -cosine(x).

(defthm cos-pi+x
  (equal (acl2-cosine (+ (acl2-pi) x))
	 (- (acl2-cosine x))))

;; cosine(pi-x) = -cosine(x).

(defthm cos-pi-x
  (equal (acl2-cosine (+ (acl2-pi) (- x)))
	 (- (acl2-cosine x))))

;; Finally, we can show that for x in (0,pi/2), cosine(x)>0.  We now
;; know that in the first quadrant, both sine and cosine are positive.

(defthm cosine-positive-in-0-pi/2
  (implies (and (realp x)
		(< 0 x)
		(< x (* 1/2 (acl2-pi))))
	   (< 0 (acl2-cosine x)))
  :hints (("Goal"
	   :use ((:instance sin-pi/2-x)
		 (:instance sine-positive-in-0-pi/2
			    (x (+ (* 1/2 (acl2-pi)) (- x)))))
	   :in-theory (disable sin-pi/2-x sin-pi/2+x sine-of-sums
			       sine-positive-in-0-pi/2))))


;; That means that in the second quadrant, sine is positive...

(defthm sine-positive-in-pi/2-pi
  (implies (and (realp x)
		(< (* 1/2 (acl2-pi)) x)
		(< x (acl2-pi)))
	   (< 0 (acl2-sine x)))
  :hints (("Goal"
	   :use ((:instance sin-pi/2+x
			    (x (+ X (- (* 1/2 (acl2-pi))))))
		 (:instance cosine-positive-in-0-pi/2
			    (x (+ X (- (* 1/2 (acl2-pi)))))))
	   :in-theory (disable sin-pi/2-x sin-pi/2+x sine-of-sums
			       cosine-positive-in-0-pi/2))))

;; ... and cosine is negative.

(defthm cosine-negative-in-pi/2-pi
  (implies (and (realp x)
		(< (* 1/2 (acl2-pi)) x)
		(< x (acl2-pi)))
	   (< (acl2-cosine x) 0))
  :hints (("Goal"
	   :use ((:instance cos-pi/2+x
			    (x (+ X (- (* 1/2 (acl2-pi))))))
		 (:instance sine-positive-in-0-pi/2
			    (x (+ X (- (* 1/2 (acl2-pi)))))))
	   :in-theory (disable cos-pi/2-x cos-pi/2+x cosine-of-sums
			       sine-positive-in-0-pi/2))))

;; In the third quadrant, sine is negative....

(defthm sine-negative-in-pi-3pi/2
  (implies (and (realp x)
		(< (acl2-pi) x)
                ;; For v2-6, (* (acl2-pi) 3/2) has been replaced by
                ;; (* 3/2 (acl2-pi)) because of changes in term-order.
		(< x (* 3/2 (acl2-pi))))
	   (< (acl2-sine x) 0))
  :hints (("Goal"
	   :use ((:instance sin-pi+x
			    (x (+ X (- (acl2-pi)))))
		 (:instance sine-positive-in-0-pi/2
			    (x (+ X (- (acl2-pi))))))
	   :in-theory (disable sin-pi-x sin-pi+x sine-of-sums
			       sine-positive-in-0-pi/2))))


;; ...and so is cosine.

(defthm cosine-negative-in-pi-3pi/2
  (implies (and (realp x)
		(< (acl2-pi) x)
		(< x (* 3/2 (acl2-pi))))
	   (< (acl2-cosine x) 0))
  :hints (("Goal"
	   :use ((:instance cos-pi+x
			    (x (+ X (- (acl2-pi)))))
		 (:instance cosine-positive-in-0-pi/2
			    (x (+ X (- (acl2-pi))))))
	   :in-theory (disable cos-pi-x cos-pi+x cosine-of-sums
			       cosine-positive-in-0-pi/2))))

;; And in the fourth quadrant, sine is negative....

(defthm sine-negative-in-3pi/2-2pi
  (implies (and (realp x)
		(< (* 3/2 (acl2-pi)) x)
                ;; For v2-6, (* (acl2-pi) 2) has been replaced by
                ;; (* 2 (acl2-pi)) because of changes in term-order.
		(< x (* 2 (acl2-pi))))
	   (< (acl2-sine x) 0))
  :hints (("Goal"
	   :use ((:instance sin-pi+x
			    (x (+ X (- (acl2-pi)))))
		 (:instance sine-positive-in-pi/2-pi
			    (x (+ X (- (acl2-pi))))))
	   :in-theory (disable sin-pi-x sin-pi+x sine-of-sums
			       sine-positive-in-pi/2-pi))))

;; ...and cosine is positive.

(defthm cosine-positive-in-3pi/2-2pi
  (implies (and (realp x)
		(< (* 3/2 (acl2-pi)) x)
		(< x (* 2 (acl2-pi))))
	   (< 0 (acl2-cosine x)))
  :hints (("Goal"
	   :use ((:instance cos-pi+x
			    (x (+ X (- (acl2-pi)))))
		 (:instance cosine-negative-in-pi/2-pi
			    (x (+ X (- (acl2-pi))))))
	   :in-theory (disable cos-pi-x cos-pi+x sine-of-sums
			       cosine-negative-in-pi/2-pi))))

;; Now, we will show that if sine(x) is non-zero, then cosine(x) is
;; between -1 and 1, and similarly if cosine(x) is non-zero.

(encapsulate
 ()

 ;; First, if c^2+s^2 is true, then s<=1.

 (local
  (defthm lemma-1
    (implies (and (realp c)
		  (realp s)
		  (equal (+ (* c c) (* s s)) 1))
	     (<= s 1))))

 ;; Also, if s < -1, then s*s > 1.

 (local
  (defthm lemma-2
    (implies (and (realp s)
		  (< s -1))
	     (< 1 (* s s)))
    :hints (("Goal"
	     :use ((:instance (:theorem
			       (implies (and (realp s)
					     (< 1 s))
					(< 1 (* s s))))
			      (s (- s))))))
    :rule-classes (:rewrite :linear)))

 ;; That means that if c^2+s^2=1, then -1 <= s.

 (local
  (defthm lemma-3
    (implies (and (realp c)
		  (realp s)
		  (equal (+ (* c c) (* s s)) 1))
	     (<= -1 s))
    :hints (("Goal"
	     :cases ((< s -1))))))

 ;; THerefore, if c^2+s^2 = 1 and c is non-zero, -1<s and s<1.

 (local
  (defthm lemma-4
    (implies (and (realp c)
		  (realp s)
		  (not (equal c 0))
		  (equal (+ (* c c) (* s s)) 1))
	     (and (< -1 s)
		  (< s 1)))
    :hints (("Goal"
	     :cases ((< s -1) (= s -1) (= s 1) (< 1 s))))))

 ;; So, if cosine(x) is non-zero, sine(x) is between -1 and 1.

 (defthm sine-<-1-if-cosine-non-0
   (implies (and (realp x)
		 (not (equal (acl2-cosine x) 0)))
	    (and (< -1 (acl2-sine x))
		 (< (acl2-sine x) 1)))
   :hints (("Goal"
	    :use ((:instance lemma-4
			     (c (acl2-cosine x))
			     (s (acl2-sine x)))
		  (:instance sin**2+cos**2))
	    :in-theory (disable lemma-4 sin**2+cos**2))))

 ;; And, if sine(x) is non-zero, cosine(x) is between -1 and 1.

 (defthm cosine-<-1-if-sine-non-0
   (implies (and (realp x)
		 (not (equal (acl2-sine x) 0)))
	    (and (< -1 (acl2-cosine x))
		 (< (acl2-cosine x) 1)))
   :hints (("Goal"
	    :use ((:instance lemma-4
			     (c (acl2-sine x))
			     (s (acl2-cosine x)))
		  (:instance sin**2+cos**2))
	    :in-theory (disable lemma-4 sin**2+cos**2))))
 )

;; Now, we find sine(3pi/2) and cosine(3pi/2).

(encapsulate
 ()

 ;; First, silly algebra!  x+x*1/2 = x*3/2.

 (local
  (defthm lemma-1 ; changed for v2-6 because of change in term-order.
    (equal (+ x (* 1/2 x))
	   (* 3/2 x))))

 ;; Now, sine(3pi/2) = -1.

 (defthm sine-3pi/2
   (equal (acl2-sine (* 3/2 (acl2-pi))) -1)
   :hints (("Goal"
	    :use ((:instance sine-of-sums
			     (x (acl2-pi))
			     (y (* 1/2 (acl2-pi)))))
	    :in-theory (disable sine-of-sums
				sin-pi+x))))

 ;; And cosine(3pi/2) = 0.

 (defthm cosine-3pi/2
   (equal (acl2-cosine (* 3/2 (acl2-pi))) 0)
   :hints (("Goal"
	    :use ((:instance cosine-of-sums
			     (x (acl2-pi))
			     (y (* 1/2 (acl2-pi)))))
	    :in-theory (disable cosine-of-sums
				cos-pi+x))))
 )

;; And finally, we get sine and cosine(2pi).

(encapsulate
 ()

 ;; Silly lemma, x+x=2x.

 (local
  (defthm lemma-1
    (equal (+ x x) (* x 2))))

 ;; sine(2pi) = 0.

 (defthm sine-2pi
   (equal (acl2-sine (* 2 (acl2-pi))) 0)
   :hints (("Goal"
	    :use ((:instance sine-of-sums
			     (x (acl2-pi))
			     (y (acl2-pi))))
	    :in-theory (disable sine-of-sums
				sin-pi+x))))

 ;; cosine(2pi) = 1.

 (defthm cosine-2pi
   (equal (acl2-cosine (* 2 (acl2-pi))) 1)
   :hints (("Goal"
	    :use ((:instance cosine-of-sums
			     (x (acl2-pi))
			     (y (acl2-pi))))
	    :in-theory (disable cosine-of-sums
				cos-pi+x))))
 )

;; So, sine(2pi+x) = sine(x).

(defthm sin-2pi+x
  (equal (acl2-sine (+ (* 2 (acl2-pi)) x))
	 (acl2-sine x)))

;; Sine(2pi-x) = -sine(x).

(defthm sin-2pi-x
  (equal (acl2-sine (+ (* 2 (acl2-pi)) (- x)))
	 (- (acl2-sine x))))

;; Cosine(2pi+x) = cosine(x).

(defthm cos-2pi+x
  (equal (acl2-cosine (+ (* 2 (acl2-pi)) x))
	 (acl2-cosine x)))

;; Cosine(2pi-x) = cosine(x).

(defthm cos-2pi-x
  (equal (acl2-cosine (+ (* 2 (acl2-pi)) (- x)))
	 (acl2-cosine x)))

;; Sine(0) = 0.

(defthm sine-0
  (equal (acl2-sine 0) 0)
  :hints (("Goal"
	   :use ((:instance sine-of-sums (x (acl2-pi)) (y (- (acl2-pi)))))
	   :in-theory (disable sine-of-sums))))

;; Cosine(0) = 1.

(defthm cosine-0
  (equal (acl2-cosine 0) 1)
  :hints (("Goal"
	   :use ((:instance cosine-of-sums (x (acl2-pi)) (y (- (acl2-pi)))))
	   :in-theory (disable cosine-of-sums))))

;; So now, we look at sine(2npi).

(encapsulate
 ()

 ;; First, a simple induction hint.

 (local
  (defun induction-hint (n)
    (if (and (integerp n)
	     (< 0 n))
	(1+ (induction-hint (+ n -1)))
      1)))

 ;; Now, a silly algebra theorem -- x*0 = 0.

 (local
  (defthm *-x-0
    (equal (* x 0) 0)))

 ;; First, we prove that sine(2npi) = 0 for n>=0.  We do this by
 ;; induction on n.

 (local
  (defthm sin-2npi-n>=0
    (implies (and (integerp n)
		  (<= 0 n))
             ;; For v2-6, (* (acl2-pi) 2 n) has been replaced by
             ;; (* 2 (acl2-pi) n) because of changes in term-order.
	     (equal (acl2-sine (* 2 (acl2-pi) n))
		    0))
    :hints (("Goal"
	     :induct (induction-hint n)))))

 ;; Now, we show that sine(2npi) = 0 for all n, even if n<0.

 (defthm sin-2npi
   (implies (integerp n)
	    (equal (acl2-sine (* 2 (acl2-pi) n))
		   0))
   :hints (("Goal"
	    :cases ((< n 0)
		    (= n 0)
		    (> n 0)))
	   ("Subgoal 3"
	    :use ((:instance sin-uminus
			     (x (* 2 (acl2-pi) n)))
		  (:instance sin-2npi-n>=0 (n (- n))))
	    :in-theory (disable sin-uminus sin-2npi-n>=0))))

 )

;; Next, we consider sine(2x) and cosine(2x).

(encapsulate
 ()

 ;; A simple rule, x+x = 2x.

 (local
  (defthm x+x
    (equal (+ x x) (* 2 x))))

 ;; From the sine-of-sums formula, sine(2x) = 2sine(x)cosine(x).

 (defthm sine-2x
   (implies (syntaxp (not (equal x '0)))
            (equal (acl2-sine (* 2 x))
                   (* 2 (acl2-sine x) (acl2-cosine x))))
   :hints (("Goal"
	    :use ((:instance sine-of-sums (x x) (y x)))
	    :in-theory (disable sine-of-sums))))

 ;; From the cosine-of-sums formula, cosine(2x) = cosine^2(x)-sine^2(x).

 (defthm cosine-2x
   (implies (syntaxp (not (equal x '0)))
            (equal (acl2-cosine (* 2 x))
                   (+ (* (acl2-cosine x) (acl2-cosine x))
                      (- (* (acl2-sine x)
                            (acl2-sine x))))))
   :hints (("Goal"
	    :use ((:instance cosine-of-sums (x x) (y x)))
	    :in-theory (disable cosine-of-sums))))
 )

;; Now, a classic conversion of sine^2 into 1-cosine^2.

(defthm sin**2->1-cos**2
  (equal (* (acl2-sine x)
	    (acl2-sine x))
	 (- 1
	    (* (acl2-cosine x)
	       (acl2-cosine x))))
  :hints (("Goal"
	   :use ((:instance sin**2+cos**2))
	   :in-theory (disable sin**2+cos**2))))

(in-theory (disable sin**2->1-cos**2))

;; And similarly, cosine^2 into 1-sine^2.

(defthm cos**2->1-sin**2
  (equal (* (acl2-cosine x)
	    (acl2-cosine x))
	 (- 1
	    (* (acl2-sine x)
	       (acl2-sine x))))
  :hints (("Goal"
	   :use ((:instance sin**2+cos**2))
	   :in-theory (disable sin**2+cos**2))))

(in-theory (disable cos**2->1-sin**2))

;; Next, we consider sine^2(x/2).  We do sine^2 to avoid the "sign"
;; problem with the sine function.

(defthm sine**2-half-angle
  (equal (* (acl2-sine (* 1/2 x))
	    (acl2-sine (* 1/2 x)))
	 (/ (- 1 (acl2-cosine x)) 2))
  :hints (("Goal"
	   :use ((:instance cosine-2x (x (* 1/2 x))))
	   :in-theory (enable-disable (cos**2->1-sin**2)
				      (sine-2x cosine-2x)))))

;; Similarly, we get the cosine of a half angle.

(defthm cosine**2-half-angle
  (equal (* (acl2-cosine (* 1/2 x))
	    (acl2-cosine (* 1/2 x)))
	 (/ (+ 1 (acl2-cosine x)) 2))
  :hints (("Goal"
	   :use ((:instance cosine-2x (x (* 1/2 x))))
	   :in-theory (enable-disable (sin**2->1-cos**2)
				      (sine-2x cosine-2x)))))

;; Next, we consider sine(pi/4).  We know this is positive, because
;; it's in the first quadrant.

(defthm sine-pi/4-positive
  ;; For v2-6, (* (acl2-pi) 1/4) has been replaced by
  ;; (* 1/4 (acl2-pi)) because of changes in term-order.
  (< 0 (acl2-sine (* 1/4 (acl2-pi))))
  :hints (("Goal"
	   :use ((:instance sine-positive-in-0-pi/2
			    (x (* 1/4 (acl2-pi)))))
	   :in-theory (disable sine-positive-in-0-pi/2)))
  :rule-classes (:linear :rewrite))

;; And so, it follows that sine(pi/4) must be sqrt(1/2).

(defthm sine-pi/4
  (equal (acl2-sine (* 1/4 (acl2-pi)))
	 (acl2-sqrt 1/2))
  :hints (("Goal"
	   :use ((:instance sine**2-half-angle
			    (x (* 1/2 (acl2-pi))))
		 (:instance y*y=x->y=sqrt-x
			    (x 1/2)
			    (y (acl2-sine (* 1/4 (acl2-pi))))))
	   :in-theory (disable sine**2-half-angle
			       y*y=x->y=sqrt-x))))

(in-theory (disable acl2-sqrt))

;; Similarly, we get cosine(pi/4).

(encapsulate
 ()

 ;; First, x/4 = x/2 - x/4.

 (local
  (defthm lemma-1 ; changed for v2-6 because of change in term-order.
    (equal (+ (* 1/2 x) (- (* 1/4 x)))
	   (* 1/4 x))))

 ;; So, we get cosine(pi/4) = sine(pi/2-pi/4) = sine(pi/4) = sqrt(2).

 (defthm cosine-pi/4
   (equal (acl2-cosine (* 1/4 (acl2-pi)))
	  (acl2-sqrt 1/2))
   :hints (("Goal"
	    :use ((:instance cos-pi/2-x
			     (x (* 1/4 (acl2-pi)))))
	    :in-theory (disable cos-pi/2-x cos-pi/2+x))))
 )

;; So now, we find a formula for sine(3x).

(encapsulate
 ()

 ;; First, 3x = x + 2x.

 (local
  (defthm lemma-1
    (equal (+ x (* 2 x))
	   (* 3 x))))

 ;; Algebra!  x+y+2x = 3x+y.

 (local
  (defthm lemma-2
    (equal (+ x y (* 2 x))
	   (+ (* 3 x) y))))

 ;; cox^2 = 1-sin^2.

 (local
  (defthm lemma-3
    (equal (equal (* (acl2-cosine x) (acl2-cosine x))
		  (+ 1 (- (* (acl2-sine x) (acl2-sine x)))))
	   t)
    :hints (("Goal"
	     :in-theory (enable cos**2->1-sin**2)))))

 ;; 3*cos*cos*sin = 3*sin - 3*sin*sin*sin follows from cos^x = 1-sin^2.

 (local
  (defthm lemma-4
    (equal (* 3 (acl2-cosine x)
	      (acl2-cosine x)
	      (acl2-sine x))
	   (- (* 3 (acl2-sine x))
	      (* 3
		 (acl2-sine x)
		 (acl2-sine x)
		 (acl2-sine x))))
    :hints (("Goal"
	     :use ((:instance
		    (:theorem (implies (equal x y)
				       (equal (* x z) (* y z))))
		    (x (* (acl2-cosine x) (acl2-cosine x)))
		    (y (- 1 (* (acl2-sine x) (acl2-sine x))))
		    (z (* 3 (acl2-sine x)))))))))

 ;; And so, we get a formula for sin(3x).

 (defthm sine-3x
   (implies (syntaxp (not (equal x '0)))
	    (equal (acl2-sine (* 3 x))
		   (- (* 3 (acl2-sine x))
		      (* 4
			 (acl2-sine x)
			 (acl2-sine x)
			 (acl2-sine x)))))
   :hints (("Goal'"
	    :use ((:instance sine-of-sums (x (* 2 x)) (y x)))
	    :in-theory (disable sine-of-sums))))
 )

;; We use that formula to get sine(pi/3).

(encapsulate
 ()

 ;; First, 3x = 4x^3 if and only 3 = 4x^2.

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp x)
		  (not (equal x 0)))
	     (equal (equal (* 3 x) (* 4 x x x))
		    (equal 3 (* 4 x x))))
    :hints (("Goal"
	     :use ((:instance
		    (:theorem
		     (implies (and (acl2-numberp x)
				   (acl2-numberp y)
				   (acl2-numberp z)
				   (not (= x 0)))
			      (equal (equal (* x y) (* x z))
				     (equal y z))))
		    (x x)
		    (y 3)
		    (z (* 4 x x))))))))

 ;; Now, sine(pi/3) is not zero, since pi/3 is in the first quadrant.

 (local
  (defthm lemma-2
    ;; For v2-6, (* (acl2-pi) 1/3) has been replaced by
    ;; (* 1/3 (acl2-pi)) because of changes in term-order.
    (not (equal (acl2-sine (* 1/3 (acl2-pi))) 0))
    :hints (("Goal"
	     :use ((:instance sine-positive-in-0-pi/2
			      (x (* 1/3 (acl2-pi)))))
	     :in-theory (disable sine-positive-in-0-pi/2)))))

 ;; And so, sine(pi/3) = sqrt(3)/2.

 (defthm sine-pi/3
   (equal (acl2-sine (* 1/3 (acl2-pi)))
	  (/ (acl2-sqrt 3) 2))
   :hints (("Goal"
	    :use ((:instance sine-3x
			     (x (* 1/3 (acl2-pi)))))
	    :in-theory (disable sine-3x))))
 )

;; Similarly, we look at cosine(pi/3).

(encapsulate
 ()

 ;; Algebra! 1 = x^2/3 iff 3 = x^2.

 (local
  (defthm lemma-1
    (equal (equal 1 (* x x 1/3))
	   (equal 3 (* x x)))))

 ;; sqrt(3)*sqrt(3)*1/3 = 3/4.

 (local
  (defthm lemma-2
    (equal (* (acl2-sqrt 3) (acl2-sqrt 3) 1/4) 3/4)
    :hints (("Goal"
	     :use ((:instance sqrt-sqrt (x 3)))
	     :in-theory (disable sqrt-sqrt)))))

 ;; And so, cosine(pi/3) = 1/2.

 (defthm cosine-pi/3
   (equal (acl2-cosine (* 1/3 (acl2-pi))) 1/2)
   :hints (("goal"
	    :use ((:instance cos**2->1-sin**2
			     (x (* 1/3 (acl2-pi)))))
	    :in-theory (disable cos**2->1-sin**2))
	   ("goal'''"
	    :use ((:instance y*y=x->y=sqrt-x
			     (x 1)
			     (y (* 2 (acl2-cosine (* 1/3 (acl2-pi)))))))
	    :in-theory (disable y*y=x->y=sqrt-x))))
 )

;; So now, we look at sine(pi/6) and cosine(pi/6).

(encapsulate
 ()

 ;; First, algebra!  x/2 - x/3 = x/6.

 (local
  (defthm lemma-1 ; changed for v2-6 because of change in term-order.
    (equal (+ (* 1/2 x) (- (* 1/3 x)))
	   (* 1/6 x))))

 ;; Now, sine(pi/6) = 1/2.

 (defthm sine-pi/6
   ;; For v2-6, (* (acl2-pi) 1/6) has been replaced by
   ;; (* 1/6 (acl2-pi)) because of changes in term-order.
   ;; The proof does actually go through without this change,
   ;; but perhaps the correct normal forms are needed when this
   ;; lemma and others like it are applied.
   (equal (acl2-sine (* 1/6 (acl2-pi))) 1/2)
   :hints (("Goal"
	    :use ((:instance sin-pi/2-x
			     (x (* 1/3 (acl2-pi)))))
	    :in-theory (disable sin-pi/2-x sin-pi/2+x))))

 ;; And cosine(pi/6) = sqrt(3)/2.

 (defthm cosine-pi/6
   (equal (acl2-cosine (* 1/6 (acl2-pi)))
	  (/ (acl2-sqrt 3) 2))
   :hints (("Goal"
	    :use ((:instance cos-pi/2-x
			     (x (* 1/3 (acl2-pi)))))
	    :in-theory (disable cos-pi/2-x cos-pi/2+x))))
 )

;; Some simple rewrite rules.  x^2 = x*x.

(local
 (defthm expt-2
   (equal (expt x 2) (* x x))))

;; x^3 = x*x*x

(local
 (defthm expt-3
   (equal (expt x 3) (* x x x))))

;; x^4 = x*x*x*x

(local
 (defthm expt-4
   (equal (expt x 4) (* x x x x))))

;; Now, we tackle some simple trigonometric identities.

(encapsulate
 ()

 ;; Observe, 3*cos*cos*cos*cos = 3*(1-sin*sin)*(1-sin*sin)

 (local
  (defthm lemma-1
    (equal (* 3
	      (acl2-cosine x) (acl2-cosine x)
	      (acl2-cosine x) (acl2-cosine x))
	   (* 3
	      (- 1 (* (acl2-sine x) (acl2-sine x)))
	      (- 1 (* (acl2-sine x) (acl2-sine x)))))
    :hints (("Goal"
	     :in-theory (enable sin**2->1-cos**2)))))

 ;; Therefore, 3*cos^4(x) + 6*sine^2(x) = 3+3*sine^4(x).

 (defthm identity-1
   (equal (+ (* 3 (expt (acl2-cosine x) 4))
	     (* 6 (expt (acl2-sine x) 2)))
	  (+ 3
	     (* 3 (expt (acl2-sine x) 4)))))
 )

;; We define tangent(x) = sine(x)/cosine(x).

(defmacro acl2-tangent (x)
  `(/ (acl2-sine ,x) (acl2-cosine ,x)))

;; Cotangent(x) == cosine(x)/sine(x).

(defmacro acl2-cotangent (x)
  `(/ (acl2-cosine ,x) (acl2-sine ,x)))

;; Secant(x) == 1/cosine(x)

(defmacro acl2-secant (x)
  `(/ (acl2-cosine ,x)))

;; Cosecant(x) == 1/sine(x)

(defmacro acl2-cosecant (x)
  `(/ (acl2-sine ,x)))

;; Now, another identity.

(encapsulate
 ()

 ;; Simple algebra...

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp x)
		  (not (equal x 0)))
	     (equal (equal (+ (* (/ x) (/ x))
			      (- (* (/ x) (/ x) y z)))
			   1)
		    (equal (+ 1 (- (* y z)))
			   (* x x))))
    :hints (("Goal"
	     :use ((:instance
		    (:theorem
		     (implies (and (acl2-numberp x)
				   (acl2-numberp y)
				   (acl2-numberp z)
				   (not (= x 0)))
			      (equal (equal (* x y) (* x z))
				     (equal y z))))
		    (x (* x x))
		    (y (+ (* (/ x) (/ x))
			  (- (* (/ x) (/ x) y z))))
		    (z 1)))))))

 ;; More algebra....

 (local
  (defthm lemma-2
    (equal (+ (expt x 4)
	      (- (expt y 4)))
	   (* (+ (expt x 2)
		 (expt y 2))
	      (- (expt x 2)
		 (expt y 2))))))

 ;; And now, secant^2(x) + tangent^2(x) = secant^4(x)-tangent^4(x).

 (defthm identity-2
   (equal (+ (expt (acl2-secant x) 2)
	     (expt (acl2-tangent x) 2))
	  (- (expt (acl2-secant x) 4)
	     (expt (acl2-tangent x) 4)))
   :hints (("Goal"
	    :cases ((equal (acl2-cosine x) 0)))
	   ("Subgoal 2"
	    :in-theory (enable-disable (cos**2->1-sin**2)
				       (expt-4
					expt-3
					functional-commutativity-of-expt-/-base
					expt-x*y^n
					distributivity-of-expt-over-*
					distributivity)))))
 )

;; Another identity!  (sin+cot)/cos = tan + csc.

(defthm identity-3
  (implies (not (equal (acl2-cosine x) 0))
	   (equal (/ (+ (acl2-sine x)
			(acl2-cotangent x))
		     (acl2-cosine x))
		  (+ (acl2-tangent x)
		     (acl2-cosecant x)))))

;; More identities!

(encapsulate
 ()

 ;; First, if sine != 0, then 1+cosine != 0.

 (local
  (defthm lemma-1
    (implies (and (realp x)
		  (not (equal (acl2-sine x) 0)))
	     (not (equal (+ 1 (acl2-cosine x)) 0)))
    :hints (("Goal"
	     :use ((:instance cosine-<-1-if-sine-non-0))
	     :in-theory (disable cosine-<-1-if-sine-non-0)))))

 ;; Algebra!

 (local
  (defthm lemma-2
    (implies (and (acl2-numberp z)
		  (not (equal z 0)))
	     (equal (equal 2 (+ 1 c (* s s (/ z))))
		    (equal (* 2 z) (+ (* (+ 1 c) z) (* s s)))))
    :hints (("Goal"
	     :use ((:instance
		    (:theorem
		     (implies (and (acl2-numberp x)
				   (acl2-numberp y)
				   (acl2-numberp z)
				   (not (= x 0)))
			      (equal (equal (* x y) (* x z))
				     (equal y z))))
		    (x z)
		    (y (+ 1 c (* s s (/ z))))
		    (z 2)))))))

 ;; And so, sin/(1+cos) + (1+cos)/sin = 2*csc

 (defthm identity-4
   (implies (realp x)
	    (equal (+ (/ (acl2-sine x)
			 (+ 1 (acl2-cosine x)))
		      (/ (+ 1 (acl2-cosine x))
			 (acl2-sine x)))
		   (* 2 (acl2-cosecant x))))
   :hints (("Goal"
	    :cases ((equal (acl2-sine x) 0)))))
 )

;; And a last identity.

(encapsulate
 ()

 ;; Algebra!  1/(-1 + 1/s) = s / (1- s)

 (local
  (defthm lemma-1
    (implies (and (acl2-numberp s)
		  (not (equal s 0)))
	     (equal (/ (+ -1 (/ s)))
		    (/ s (- 1 s))))
    :hints (("Goal"
	     :use ((:instance
		    (:theorem (implies (and (acl2-numberp s) (not (equal s 0)))
				       (equal (/ x) (/ s (* s x)))))
		    (x (+ -1 (/ s)))))
	     :in-theory (disable distributivity-of-/-over-*))
	    ("Subgoal 1"
	     :in-theory (enable distributivity-of-/-over-*)))))

 ;; More algebra!

 (local
  (defthm lemma-2
    (implies (and (acl2-numberp c)
		  (acl2-numberp x)
		  (not (equal c 0))
		  (not (equal x 0)))
	     (equal (equal (* c (/ x))
			   (+ (/ c)
			      (* (/ c) y)))
		    (equal (* c c)
			   (* x (+ 1 y)))))
    :hints (("Goal"
	     :use ((:instance
		    (:theorem
		     (implies (and (acl2-numberp x)
				   (acl2-numberp y)
				   (acl2-numberp z)
				   (not (= x 0)))
			      (equal (equal (* x y) (* x z))
				     (equal y z))))
		    (y (* c c))
		    (z (* x (+ 1 y)))
		    (x (* (/ c) (/ x)))))))))

 ;; And if cosine is non-zero, 1-sine is non-zero.

 (local
  (defthm lemma-3
    (implies (and (realp x)
		  (not (equal (acl2-cosine x) 0)))
	     (not (equal (+ 1 (- (acl2-sine x))) 0)))
    :hints (("Goal"
	     :use ((:instance sine-<-1-if-cosine-non-0))
	     :in-theory (disable sine-<-1-if-cosine-non-0)))))

 ;; Another identity.  cot/(csc - 1) = (csc + 1) / cot.

 (defthm identity-5
   (implies (realp x)
	    (equal (/ (acl2-cotangent x)
		      (- (acl2-cosecant x) 1))
		   (/ (+ (acl2-cosecant x) 1)
		      (acl2-cotangent x))))
   :hints (("Goal"
	    :cases ((equal (acl2-sine x) 0)))
	   ("Subgoal 2"
	    :cases ((equal (acl2-cosine x) 0))
	    :in-theory (enable sin**2->1-cos**2))))
 )

;; The definition of PI in <math.h> on an HPUX 10.20 is the following:
;;
;; #  define M_PI		3.14159265358979323846
;;
;; Below, we try to justify that number

(defun m-pi ()
  314159265358979323846/100000000000000000000)

(defun m-pi+eps ()
  314159265358979323847/100000000000000000000)

;; The following theorem is here to show that m_pi is between 3 and 4.
;; This is only here because it would be too easy to type one too many
;; or one too few zeros above!

(defthm m-pi-sanity-check
  (and (< 3 (m-pi))
       (< (m-pi) 4)))

;; We want to prove that m-pi and m-pi+eps are both standard numbers.
;; Unfortunately, their numerator/denominators are such large
;; integers, that the simple rules in nsa.lisp to determine standard
;; integers don't apply.  So, we need to prove that some bigger
;; integers are standard by repeatedly multiplying our largest known
;; standard integer....
;;

;; AHA! -- No longer are these needed, now that standard-numberp is
;; executable.

#|

;; We're up to 10**8 -- now we go to 10**16

(local
 (defthm standard-numberp-10000*10000*10000*10000
   (standard-numberp 10000000000000000)
   :hints (("Goal"
	    :use ((:instance standard-numberp-times
			     (x 100000000)
			     (y 100000000)))))))

;; ... and on to 10**24

(local
 (defthm standard-numberp-10000*10000*10000*10000*10000*10000
   (standard-numberp 1000000000000000000000000)
   :hints (("Goal"
	    :use ((:instance standard-numberp-times
			     (x 10000000000000000)
			     (y 100000000)))))))

|#

;; Since 10**24 is standard, so are all positive integers smaller than
;; it.

(local
 (defthm standard-integer-<=-10000*10000*10000*10000*10000*10000
   (implies (and (integerp x)
		 (<= 0 x)
		 (<= x 1000000000000000000000000))
	    (standard-numberp x))
   :hints (("Goal"
	    :use ((:instance large-if->-large
			     (x x)
			     (y 1000000000000000000000000))
		  (:instance limited-integers-are-standard))
	    :in-theory (disable large-if->-large
				limited-integers-are-standard)))))

;; Now, it's obvious that m-pi is standard.

(defthm m-pi-standard
  (standard-numberp (m-pi)))

;; And the same goes for m-pi+eps.

(defthm m-pi+eps-standard
  (standard-numberp (m-pi+eps)))

;; This function is a quick check on whether ACL2 will be able to
;; prove that cos(x) is negative, using the first nterms of the cosine
;; Taylor approximation.

(defun cosine-clearly-negative (x nterms)
  (and (< (sumlist (taylor-sincos-list nterms 0 1 x)) 0)
       (< (car (taylor-sincos-list 2
				   nterms
				   (if (evenp
					(/ nterms 2))
				       1
				     -1)
				   x))
	  0)))

;; Same as above, but testing for cos(x) positive.

(defun cosine-clearly-positive (x nterms)
  (and (> (sumlist (taylor-sincos-list nterms 0 1 x)) 0)
       (> (car (taylor-sincos-list 2 nterms (if (evenp (/ nterms 2)) 1 -1) x))
	  0)))

;; This is a *program* mode ACL2 function.  I.e., ACL2 does not know
;; any axioms about it, but it can execute it.  It simply finds the
;; smallest number of terms needed to verify that cos(x) is positive
;; or negative for a give x.  Note, it would fail (for example) with
;; x=0, so its termination can not be guaranteed.
;;
;; Some wisdom gained from using this function:
;;
;; (cosine-clear-sign (/ (m-pi) 2) 0)     => '(POSITIVE . 28)
;; (cosine-clear-sign (/ (m-pi+eps) 2) 0) => '(NEGATIVE . 26)

(local
 (defun cosine-clear-sign (x nterms)
   (declare (xargs :mode :program))
   (if (cosine-clearly-negative x nterms)
       (cons 'negative nterms)
     (if (cosine-clearly-positive x nterms)
	 (cons 'positive nterms)
       (cosine-clear-sign x (+ nterms 2))))))


;; Next, we show how the Taylor series for cosine can be split into a
;; finite prefix and an "infinite" suffix.

(encapsulate
 ()

 ;; We define the following function purely to give ACL2 an induction
 ;; hint on the following theorem.

 (local
  (defun natural-induction (n)
    (if (zp n)
	1
      (+ n (natural-induction (1- n))))))

 ;; You would think ACL2 knew this fact already!  For that matter, I
 ;; think I've proved this before.  If n is an integer, either it's
 ;; even or n-1 is even.

 (local
  (defthm even-x-or-even-x-1
    (implies (and (<= 0 n)
		  (integerp n)
		  (not (integerp (* 1/2 n))))
	     (integerp (+ -1/2 (* 1/2 n))))
    :hints (("Goal" :induct (natural-induction n)))))

 ;; This simple lemma opens up a specific instance of the Taylor
 ;; approximation.

 (local
  (defthm lemma-1
    (implies (and (integerp counter)
		  (<= 0 counter)
		  (integerp sign))
	     (equal (taylor-sincos-list 2 counter sign x)
		    (list (* sign (/ (factorial counter))
			     (expt x counter)))))
    :hints (("Goal" :expand
	     ((taylor-sincos-list 2 counter sign x))))))

 ;; And now, we can state explicitly how a Taylor series can be split
 ;; into two parts.

 (defthm taylor-sincos-list-split
   (implies (and (integerp n1)
		 (<= 0 n1)
		 (evenp n1)
		 (integerp n2)
		 (<= 0 n2)
		 (integerp counter)
		 (<= 0 counter)
		 (integerp sign))
	    (equal (taylor-sincos-list (+ n1 n2) counter sign x)
		   (append (taylor-sincos-list n1 counter sign x)
			   (taylor-sincos-list n2
					       (+ counter n1)
					       (if (evenp (/ n1 2))
						   sign
						 (- sign))
					       x))))
   :hints (("Goal" :in-theory (enable zp)) ; for v2-6
           ("Subgoal *1/2.4"
	    :expand ((taylor-sincos-list (+ n1 n2)
					 counter sign x)))
	   ("Subgoal *1/2.3"
	    :use ((:instance even-x-or-even-x-1 (n (* 1/2 n1))))
	    :in-theory (disable even-x-or-even-x-1))
	   ("Subgoal *1/2.1"
	    :expand ((taylor-sincos-list (+ n1 n2)
					 counter sign x)))))
 )

;; The theorem above can be specialized to the case when we are
;; splitting a list with precisely i-large-integer terms -- such as
;; the one used in the definition of cosine!

(defthm taylor-sincos-list-split-limited-nterms
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(i-limited nterms)
		(evenp nterms)
		(integerp counter)
		(<= 0 counter)
		(integerp sign))
	   (equal (taylor-sincos-list (i-large-integer) counter sign x)
		  (append (taylor-sincos-list nterms counter sign x)
			  (taylor-sincos-list (- (i-large-integer)
						 nterms)
					      (+ counter nterms)
					      (if (evenp (/ nterms 2))
						  sign
						(- sign))
					      x))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance taylor-sincos-list-split
			    (n1 nterms)
			    (n2 (- (i-large-integer) nterms))))
	   :in-theory (disable taylor-sincos-list-split))
	  ("Goal''"
	   :use ((:instance large->-non-large
			    (x (i-large-integer))
			    (y nterms)))
	   :in-theory (disable large->-non-large))))

;; Here is the specific split we're interested in for m-pi.

(defthm taylor-sincos-list-split-for-m-pi
  (equal (taylor-sincos-list (i-large-integer)
			     0
			     1
                             ;; For v2-6, (* (m-pi) 1/2) has been replaced by
                             ;; (* 1/2 (m-pi)) because of changes in term-order.
			     (* 1/2 (m-pi)))
	 (append (taylor-sincos-list 28 0 1
				     (* 1/2 (m-pi)))
		 (taylor-sincos-list (-
				      (i-large-integer)
				      28)
				     28
				     1
				     (* 1/2 (m-pi)))))
  :hints (("Goal"
	   :use ((:instance taylor-sincos-list-split-limited-nterms
			    (nterms 28)
			    (counter 0)
			    (sign 1)
			    (x (* 1/2 (m-pi)))))
	   :in-theory (disable taylor-sincos-list-split-limited-nterms))))

;; And likewise for m-pi+eps.

(defthm taylor-sincos-list-split-for-m-pi+eps
  ;; For v2-6, (* (m-pi+eps) 1/2) has been replaced by (* 1/2 (m-pi+eps))
  ;; because of changes in term-order.
  (equal (taylor-sincos-list (i-large-integer) 0 1 (* 1/2 (m-pi+eps)))
	 (append (taylor-sincos-list 26 0 1 (* 1/2 (m-pi+eps)))
		 (taylor-sincos-list (- (i-large-integer) 26)
				     26
				     -1
				     (* 1/2 (m-pi+eps)))))
  :hints (("Goal"
	   :use ((:instance taylor-sincos-list-split-limited-nterms
			    (nterms 26)
			    (counter 0)
			    (sign 1)
			    (x (* 1/2 (m-pi+eps)))))
	   :in-theory (disable taylor-sincos-list-split-limited-nterms))))


;; A typical ACL2 lemma.  This lets ACL2 know when a Taylor series is
;; non-empty.

(defthm consp-taylor-sincos-list
  (implies (and (integerp nterms)
		(< 0 nterms)
		(integerp counter)
		(<= 0 counter))
	   (consp (taylor-sincos-list nterms counter sign x))))

;; There has to be a better way than the following!  Here are a bunch
;; of obvious lemmas about 2[68] < large-integer and simple
;; variations.  Maybe there's a simple rewrite rule that can eliminate
;; all this.

;; 26 < large-integer

(local
 (defthm 26-<-i-large-integer
   (< 26 (i-large-integer))
   :hints (("Goal"
	    :use ((:instance large->-non-large
			     (x (i-large-integer))
			     (y 26)))
	    :in-theory (disable large->-non-large)))))

;; 28 < large-integer

(local
 (defthm 28-<-i-large-integer
   (< 28 (i-large-integer))
   :hints (("Goal"
	    :use ((:instance large->-non-large
			     (x (i-large-integer))
			     (y 28)))
	    :in-theory (disable large->-non-large)))))

;; 0 <= large-integer - 28

(local
 (defthm i-large-integer-28->=-0
   ;; For v2-6, (+ (i-large-integer) -28) has been replaced by (+ -28 (i-large-integer))
   ;; because of changes in term-order.
   (<= 0 (+ -28 (i-large-integer)))
   :hints (("Goal" :use ((:instance 28-<-i-large-integer))
	    :in-theory (disable 28-<-i-large-integer)))))

;; 0 <= large-integer - 26

(local
 (defthm i-large-integer-26->=-0
   ;; For v2-6, (+ (i-large-integer) -26) has been replaced by (+ -26 (i-large-integer))
   ;; because of changes in term-order.
   (<= 0 (+ -26 (i-large-integer)))
   :hints (("Goal" :use ((:instance 26-<-i-large-integer))
	    :in-theory (disable 26-<-i-large-integer)))))

;; Now that we know how to split a Taylor series into the finite and
;; infinite parts, we try to prove that each part is negative (or
;; positive) to get a feel for the sign of the total sum.

;; First, the finite part of cosine(m-pi/2) is positive.

(defthm taylor-sincos-list-prefix-m-pi->-0
  (> (sumlist (taylor-sincos-list 28 0 1
				  (* 1/2 (m-pi)))) 0))

;; And cosine(m-pi+eps/2) is negative.

(defthm taylor-sincos-list-prefix-m-pi+eps-<-0
  (< (sumlist (taylor-sincos-list 26 0 1 (* 1/2 (m-pi+eps)))) 0))

;; Now, to get a handle on the infinite parts, we notice that the sum
;; is alternating, so the first element is an upper bound.

;; The sum is alternating for m-pi/2.

(defthm alternating-sequence-2-p-taylor-sincos-m-pi
   (implies (and (realp sign)
		 (not (equal sign 0))
		 (integerp counter)
		 (integerp nterms)
		 (<= 0 nterms)
		 (<= 2 counter))
	    (alternating-sequence-2-p (taylor-sincos-list nterms
							  counter sign
							  (* 1/2 (m-pi)))))
   :hints (("Goal"
	    :use ((:instance alternating-sequence-2-p-taylor-sincos-2
			     (x (* 1/2 (m-pi))))))))

;; The sum is also alternating for m-pi+eps/2.

(defthm alternating-sequence-2-p-taylor-sincos-m-pi+eps
   (implies (and (realp sign)
		 (not (equal sign 0))
		 (integerp counter)
		 (integerp nterms)
		 (<= 0 nterms)
		 (<= 2 counter))
	    (alternating-sequence-2-p (taylor-sincos-list nterms
							  counter sign
							  (* 1/2 (m-pi+eps)))))
   :hints (("Goal"
	    :use ((:instance alternating-sequence-2-p-taylor-sincos-2
			     (x (* 1/2 (m-pi+eps))))))))

;; Now, the first element of the infinite part of the Taylor sequence
;; for cosine(m-pi/2) is positive.

(defthm car-taylor-sincos-list-postfix-m-pi->-0
  ;; For v2-6, (- (i-large-integer) 28) has been replaced by (+ -28 (i-large-integer))
  ;; because of changes in term-order.
  (> (car (taylor-sincos-list (+ -28 (i-large-integer))
			      28
			      1
			      (* 1/2 (m-pi))))
     0))

;; And the first element of the infinite part of the Taylor sequence
;; for cosine(m-pi+eps/2) is negative.

(defthm car-taylor-sincos-list-postfix-m-pi+eps-<-0
  (< (car (taylor-sincos-list (+ -26 (i-large-integer))
			      26
			      -1
			      (* 1/2 (m-pi+eps))))
     0))

;; So, we can conclude that the sum of the infinite list for
;; cosine(m-pi+eps) must be positive.

(defthm taylor-sincos-list-postfix-m-pi->-0
  (> (sumlist (taylor-sincos-list (+ -28 (i-large-integer))
				  28
				  1
				  (* 1/2 (m-pi))))
     0)
  :hints (("Goal"
	   :use ((:instance sumlist-alternating-sequence-lemma
			    (x (taylor-sincos-list (+ -28 (i-large-integer))
						   28
						   1
						   (* 1/2 (m-pi)))))
		 (:instance car-taylor-sincos-list-postfix-m-pi->-0))
	   :in-theory (disable car-taylor-sincos-list-postfix-m-pi->-0
			       m-pi
			       (m-pi)))))

;; And similarly, the inifinite sum for cosine(m-pi+eps/2) is negative.

(defthm taylor-sincos-list-postfix-m-pi+eps-<-0
  (< (sumlist (taylor-sincos-list (+ -26 (i-large-integer))
				  26
				  -1
				  (* 1/2 (m-pi+eps))))
     0)
  :hints (("Goal"
	   :use ((:instance sumlist-alternating-sequence-lemma
			    (x (taylor-sincos-list (+ -26 (i-large-integer))
						   26
						   -1
						   (* 1/2 (m-pi+eps)))))
		 (:instance car-taylor-sincos-list-postfix-m-pi+eps-<-0))
	   :in-theory (disable car-taylor-sincos-list-postfix-m-pi+eps-<-0
			       m-pi+eps
			       (m-pi+eps)))))

;; We need to know more than just the sign, though.  Specifically, we
;; need to know that the sum is limited.  Before we can prove that, we
;; need a few lemmas.

;; First of all, x^n is standard when x and n are both standard.

(defthm expt-standard
  (implies (and (standard-numberp x)
		(standard-numberp n))
	   (standard-numberp (expt x n))))

;; Also, n! is standard for standard n.

(defthm factorial-standard
  (implies (standard-numberp n)
	   (standard-numberp (factorial n)))
  :hints (("Goal" :in-theory (enable limited-integers-are-standard))))

;; An unfortunate lemma is that m-pi**28 is limited.

(local
 (defthm limited-pi**28
   (i-limited (expt (m-pi) 28))
   :hints (("Goal" :in-theory (enable-disable (standards-are-limited)
					      (m-pi (m-pi)))))))

;; Likewise for m-pi+eps**26 is limited.

(local
 (defthm limited-pi+eps**26
   (i-limited (expt (m-pi+eps) 26))
   :hints (("Goal" :in-theory (enable-disable (standards-are-limited)
					      (m-pi+eps (m-pi+eps)))))))

;; Some more unfortunate theorems.  This constant (obviously very
;; close to 0) is i-limited.

(local
 (defthm limited-/-fact-28
   (not (i-large 1/81842841814930553085241614925824000000))
   :hints (("Goal"
	    :use ((:instance
		   large-if->-large
		   (x 1/81842841814930553085241614925824000000)
		   (y 1)))
	    :in-theory (disable large-if->-large)))))

;; And the same goes for this other small positive constant.

(local
 (defthm limited-/-fact-26
   (not (i-large 1/27064431817106664380040216576000000))
   :hints (("Goal"
	    :use ((:instance
		   large-if->-large
		   (x 1/27064431817106664380040216576000000)
		   (y 1)))
	    :in-theory (disable large-if->-large)))))

;; Now we can prove that the infinite part of the Taylor sum for
;; cosine(m-pi/2) is limited.

(defthm taylor-sincos-list-postfix-limited
  (i-limited
   (sumlist (taylor-sincos-list (+ (i-large-integer)
				   -28)
				28
				1
				(* 1/2 (m-pi)))))
  :hints (("Goal"
	   :use ((:instance sumlist-alternating-sequence
			    (x (taylor-sincos-list (+ -28 (i-large-integer))
						   28
						   1
						   (* 1/2 (m-pi)))))
		 (:instance large-if->-large
			    (x (sumlist (taylor-sincos-list (+ -28 (i-large-integer))
							    28
							    1
							    (* 1/2 (m-pi)))))
			    (y (car (taylor-sincos-list (+ -28 (i-large-integer))
							28
							1
							(* 1/2 (m-pi)))))))
	   :in-theory (disable sumlist-alternating-sequence
			       m-pi (m-pi)
			       large-if->-large))
	  ("Goal'''"
	   :use ((:instance i-limited-times
			    (x (expt (m-pi) 28))
			    (y 1/81842841814930553085241614925824000000)))
	   :in-theory (disable i-limited-times m-pi (m-pi)))))

;; And so is the infinite part of the sum for cosine(m-pi+eps/2).

(defthm taylor-sincos-list-postfix-limited-2
  (i-limited (sumlist (taylor-sincos-list (+ -26 (i-large-integer))
					  26
					  -1
					  (* 1/2 (m-pi+eps)))))
  :hints (("Goal"
	   :use ((:instance sumlist-alternating-sequence
			    (x (taylor-sincos-list (- (i-large-integer) 26)
						   26
						   -1
						   (* 1/2 (m-pi+eps)))))
		 (:instance large-if->-large
			    (x (sumlist (taylor-sincos-list (- (i-large-integer) 26)
							    26
							    -1
							    (* 1/2 (m-pi+eps)))))
			    (y (car (taylor-sincos-list (- (i-large-integer) 26)
						   26
						   -1
						   (* 1/2 (m-pi+eps)))))))
	   :in-theory (disable sumlist-alternating-sequence
			       m-pi+eps (m-pi+eps)
			       large-if->-large))
	  ("Goal'''"
	   :use ((:instance i-limited-times
			    (x (expt (m-pi+eps) 26))
			    (y 1/27064431817106664380040216576000000)))
	   :in-theory (disable i-limited-times m-pi+eps (m-pi+eps)))))

;; Now we're almost done.  But first, we have to prove that the Taylor
;; series for cosine really is the same as the cosine function.
;; Earlier, we had a similar result about the Taylorish series, and we
;; showed the Taylorish series was the same as cosine, but we never
;; needed to go straight from cosine to this Taylor series.

(defthm taylor-cos-valid
  (implies (standard-numberp x)
	   (equal (acl2-cosine x)
		  (standard-part (sumlist (taylor-sincos-list
					   (i-large-integer) 0 1
					   x)))))
  :hints (("Goal"
	   :in-theory (enable taylorish-cos-valid))))

;; A final trick.  The finite part of the Taylor sum is not just
;; limited, it's also standard!  This is good, because it means we
;; know its standard-part.  In particular, standard-part preserves the
;; signs of the finite part of the Taylor sums, so the theorems we
;; have above will apply with the strict inequalities.

(defthm taylor-sincos-list-standard
  (implies (and (standard-numberp sign)
		(integerp counter)
		(<= 0 counter)
		(standard-numberp counter)
		(integerp nterms)
		(<= 0 nterms)
		(standard-numberp nterms)
		(standard-numberp x))
	   (standard-numberp
	    (sumlist (taylor-sincos-list nterms
					 counter
					 sign
					 x)))))


;; But what about the infinite parts?  We can't keep the strict
;; inequalities (easily), but we can relax them into non-strict
;; inequalities.  I.e., if x is positive, std-pt(x)>=0.  So we can
;; conclude that the standard-part of the infinite part of the Taylor
;; series for cosine (m-pi/2) is non-negative.

(defthm stdpart-part-taylor-sincos-list-postfix-m-pi->=-0
  (>= (standard-part (sumlist (taylor-sincos-list (+ -28 (i-large-integer))
						  28 1 (* 1/2 (m-pi)))))
      0)
  :hints (("Goal"
	   :use ((:instance taylor-sincos-list-postfix-m-pi->-0)
		 (:instance standard-part-<=
			    (x 0)
			    (y (SUMLIST (TAYLOR-SINCOS-LIST (+ -28 (I-LARGE-INTEGER))
							    28 1 (* 1/2 (M-PI)))))))
	   :in-theory (disable taylor-sincos-list-postfix-m-pi->-0
			       standard-part-<=
			       m-pi
			       (m-pi)))))

;; Likewise, the standard-part of the infinite part of the Taylor
;; series for cosine(m-pi+eps/2) is non-positive.

(defthm stdpart-part-taylor-sincos-list-postfix-m-pi+eps-<=-0
  (<= (standard-part (sumlist (taylor-sincos-list (+ -26 (i-large-integer))
						  26 -1 (* 1/2 (m-pi+eps)))))
      0)
  :hints (("Goal"
	   :use ((:instance taylor-sincos-list-postfix-m-pi+eps-<-0)
		 (:instance standard-part-<=
			    (x (SUMLIST (TAYLOR-SINCOS-LIST (+ -26 (I-LARGE-INTEGER))
							    26 -1 (* 1/2 (m-pi+eps)))))
			    (y 0)))
	   :in-theory (disable taylor-sincos-list-postfix-m-pi+eps-<-0
			       standard-part-<=
			       m-pi+eps
			       (m-pi+eps)))))

;; Here's a silly lemma -- I wonder why it hasn't been needed
;; earlier.  If x is real, then so is its standard part.

(defthm realp-standard-part
  (implies (realp x)
	   (realp (standard-part x))))

;; And now, we can prove beyond a shadow of a doubt that
;; cosine(m-pi/2) > 0.  Basically, cosine(m-pi/2) is the standard-part
;; of F+L where F is positive and standard, and L is positive and
;; limited.  So, standard-part(F+L) =
;; standard-part(F)+standard-part(L) = F+standard-part(L) > 0, since
;; F>0 and standard-part(L)>=0.

(defthm cosine-m-pi/2->-0
  (> (acl2-cosine (* 1/2 (m-pi))) 0)
  :hints (("Goal"
	   :in-theory (disable acl2-cosine m-pi (m-pi)))
	  ("Goal'"
	   :use ((:instance
		  (:theorem (implies (and (realp x) (< 0 x)
					  (realp y) (<= 0 y))
				     (< 0 (+ x y))))
		  (x (sumlist (taylor-sincos-list 28 0 1 (* 1/2 (m-pi)))))
		  (y (standard-part (sumlist (taylor-sincos-list (+ -28 (i-large-integer))
								 28 1 (* 1/2 (m-pi))))))))
	   :in-theory (disable sumlist
			       taylor-sincos-list
			       m-pi (m-pi)))))


;; And a similar argument proves cosine(m-pi+eps/2) < 0.

(defthm cosine-m-pi+eps/2-<-0
  (< (acl2-cosine (* 1/2 (m-pi+eps))) 0)
  :hints (("Goal"
	   :in-theory (disable acl2-cosine m-pi+eps (m-pi+eps)))
	  ("Goal'"
	   :use ((:instance
		  (:theorem (implies (and (realp x) (> 0 x)
					  (realp y) (>= 0 y))
				     (> 0 (+ x y))))
		  (x (sumlist (taylor-sincos-list 26 0 1 (* 1/2 (m-pi+eps)))))
		  (y (standard-part (sumlist (taylor-sincos-list (+ -26 (i-large-integer))
								 26 -1 (* 1/2 (m-pi+eps))))))))
	   :in-theory (disable sumlist
			       taylor-sincos-list
			       m-pi+eps (m-pi+eps)))))

;; We can forget about the Taylor expansion of cosine now.

(in-theory (disable taylor-cos-valid))

;; For the remainder of the proof, we need to show that m-pi/2 is in
;; the first quadrant and m-pi+eps/2 is in the second quadrant.
;; First, we show simply that these are the only two possibilities.
;; This follows because both m-pi/2 and m-pi+eps/2 are around 1.57 and
;; we know pi>=2.  So, m-pi is in the first or second quadrant....

(defthm m-pi/2-in-first-or-second-quadrant
  (< (* 1/2 (m-pi)) (acl2-pi))
  :hints (("Goal"
	   :use ((:instance (:theorem (implies (and (< x y) (<= y z)) (< x z)))
			    (x (* 1/2 (m-pi)))
			    (y 2)
			    (z (acl2-pi)))))))

;; ....and so is m-pi+eps.

(defthm m-pi+eps/2-in-first-or-second-quadrant
  (< (* 1/2 (m-pi+eps)) (acl2-pi))
  :hints (("Goal"
	   :use ((:instance (:theorem (implies (and (< x y) (<= y z)) (< x z)))
			    (x (* 1/2 (m-pi+eps)))
			    (y 2)
			    (z (acl2-pi)))))))

;; Now, we can narrow m-pi to be in the first quadrant only, since its
;; cosine is positive, and cosine(x)<0 in the second quadrant!

(defthm m-pi-in-first-quadrant
  (and (< 0 (* 1/2 (m-pi)))
       (< (* 1/2 (m-pi)) (* 1/2 (acl2-pi))))
  :hints (("Goal"
	   :use ((:instance cosine-m-pi/2->-0)
		 (:instance cosine-negative-in-pi/2-pi (x (* 1/2 (m-pi)))))
	   :in-theory (disable cosine-m-pi/2->-0 cosine-negative-in-pi/2-pi
			       m-pi (m-pi)))))

;; Similarly, m-pi+eps is in the second quadrant, since its cosine is
;; negative, and cosine(x)>0 in the first quadrant.

(defthm m-pi+eps-in-second-quadrant
  (and (< (* 1/2 (acl2-pi)) (* 1/2 (m-pi+eps)))
       (< (* 1/2 (m-pi+eps)) (acl2-pi)))
  :hints (("Goal"
	   :use ((:instance cosine-m-pi+eps/2-<-0)
		 (:instance cosine-positive-in-0-pi/2 (x (* 1/2 (m-pi+eps)) )))
	   :in-theory (disable cosine-m-pi+eps/2-<-0 cosine-positive-in-0-pi/2
			       m-pi+eps (m-pi+eps)))))

;; So now, m-pi/2 <= pi/2 <= m-pi+eps/2.  So, multiplying everything
;; by 2 gives a really tight estimate for pi :-)

(defthm pi-tight-bound
  (and (< (m-pi) (acl2-pi))
       (< (acl2-pi) (m-pi+eps))
       (<= (abs (- (m-pi) (m-pi+eps)))
	   1/100000000000000000000))
  :hints (("Goal"
	   :use ((:instance m-pi-in-first-quadrant)
		 (:instance m-pi+eps-in-second-quadrant))
	   :in-theory (disable m-pi-in-first-quadrant
			       m-pi+eps-in-second-quadrant
			       m-pi (m-pi)
			       m-pi+eps (m-pi+eps)))
	  ("Goal'''" :in-theory '(abs m-pi m-pi+eps))))
