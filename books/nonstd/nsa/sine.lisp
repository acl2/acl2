;;; This book develops a simple theory of the sine function.  This is
;;; a "throwawy" book, meant to flush out bugs and missing features in
;;; the non-standard analysis code of acl2(r).  The work was inspired
;;; by Matt Kaufmann's earlier book on sine; in fact, the main
;;; theorem, which is an approximation of sin(1/2) is his.

;;; This book should not be confused the trigonometric book of acl2(r),
;;; which follows a different path, defining sine(x) in terms of e^x.
;;; If you want to do real trigonometry, do NOT include this book.  If
;;; you want to learn about the non-standard analysis features in
;;; ACL2, by all means, go ahead and read this book!

;;; The approach here is to define the sine function in terms of its
;;; Taylor expansion.  The terms in the expansion are stored in a
;;; list, and their sum is computed by a separate function.  It is
;;; shown that the expansion sequence can be split into two parts.
;;; The first part has a i-limited number of terms, and its sum is
;;; i-limited.  The second part is a strictly alternating series, and
;;; so its sum is also i-limited.  Therefore, the entire sum is
;;; i-limited, hence the series is convergent and sine(x) can be
;;; well-defined.  The definition is given by the standard-part of the
;;; sum of an i-large number of terms.

(in-package "ACL2")

(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))
(local (include-book "arithmetic/abs" :dir :system))

(include-book "nsa")
(include-book "factorial")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;;; We begin by defining the function 'sumlist' which adds up all the
;;; elements of a list.

(defun sumlist (x)
  (if (consp x)
      (+ (car x)
	 (sumlist (cdr x)))
    0))

;; The sum of a list of real elements is obviously real.

(defthm realp-sumlist
  (implies (real-listp x)
	   (realp (sumlist x))))

;; If you split a list into two halves and sum each half separately,
;; the sum of the sums is the same as the sum of the original list.

(defthm sumlist-append
  (equal (sumlist (append x y))
	 (+ (sumlist x) (sumlist y))))


;;; We also need to include some theorems about the factorial function.

;; We start with a rule to reduce terms of the form (n+1)! into
;; (n+1)*n!  The use of "hide" below is to keep ACL2 from further
;; reducing the result into n*n! + n! which is usually a big loser.

(defthm factorial-+1-x
  (implies (and (integerp x)
		(<= 0 x))
	   (equal (factorial (+ 1 x))
		  (* (hide (+ 1 x)) (factorial x))))
  :hints (("Goal" :expand ((hide (+ 1 x)))
	   :in-theory (enable factorial))))

;; We special-case the value (n+3)! since we find this term often.

(defthm factorial-+3-x
  (implies (and (integerp x)
		(<= 0 x))
	   (equal (factorial (+ 3 x))
		  (* (hide (+ 3 x))
		     (hide (+ 2 x))
		     (hide (+ 1 x))
		     (factorial x))))
  :hints (("Goal" :expand ((hide (+ 1 x))
			   (hide (+ 2 x))
			   (hide (+ 3 x)))
	   :in-theory (enable factorial))))


;;; We need some important lemmas about the expt or x^n function.

;; First, we want to talk about (-x)^n.  If n is even, this is just
;; x^n, and if n is odd this is -(x^n).

(encapsulate
 ()

 ;; We need this function strictly as an induction hint.  Who would
 ;; have thought the fibonnaci function would be so reduced!

 (local
  (defun fn (counter)
    (if (zp counter)
	0
      (if (= counter 1)
	  1
	(+ (fn (- counter 1)) (fn (- counter 2)))))))

 ;; The fundamental lemma that we need is that if n is an integer
 ;; either n/2 is an integer or n/2-1/2 is an integer.

 (local
  (defthm lemma1
    (implies (and (integerp counter)
		  (<= 0 counter)
		  (NOT (INTEGERP (* 1/2 COUNTER))))
	     (INTEGERP (+ -1/2 (* 1/2 COUNTER))))
    :hints (("Goal" :induct (fn counter)))))


 ;; Now, we can use induction to find that (-x)^n is equal to x^n when
 ;; n is even and -(x^n) when n is odd.

 (defthm expt-uminus
   (implies (and (realp x)
		 (integerp counter)
		 (<= 0 counter))
	    (equal (expt (- x) counter)
		   (if (evenp counter)
		       (expt x counter)
		     (- (expt x counter)))))))

;; A very useful lemma is that -1^n is either 1 or -1.....

(local
 (defthm expt--1-counter
   (or (equal (expt -1 counter) 1)
       (equal (expt -1 counter) -1))
   :hints (("Goal" :in-theory (enable expt)))
   :rule-classes nil))

;; ....so in particular |-1^n| is always 1.

(local
 (defthm abs-expt--1-counter
   (equal (abs (expt -1 counter)) 1)
   :hints (("Goal" :use ((:instance expt--1-counter))))))

;; A very important theorem.  When both x and n are limited, so is
;; x^n.  The use of recursion is justified, since we're only
;; interested in limited n.  Moreover, the theorem follows trivially,
;; since if x^{n-1} is limited, then obviously so is x*n^{n-1}.

(defthm expt-limited
  (implies (and (<= 0 n)
		(i-limited n)
		(i-limited x))
	   (i-limited (expt x n))))

;; When we see 0^n, we can immediately rewrite that as 0 -- or so we
;; thought until we realized 0^0 = 1 in ACL2.

(defthm expt-0-counter
  (equal (expt 0 counter)
	 (if (and (integerp counter)
		  (not (equal counter 0)))
	     0
	   1)))

;; In all cases, though, x^0 is equal to 1.

(defthm expt-x-0
  (equal (expt x 0) 1))

;; This rule rewrites x^{n+1} into x*x^n.  We see this term often in
;; our inductions.

(local
 (defthm expt-x-1+-c
   (implies (and (integerp c) (<= 0 c))
	    (equal (expt x (1+ c)) (* x (expt x c))))
   :hints (("Goal" :expand (expt x (1+ c))))))

;; As was the case with factorial, we special-case x^3.

(local
 (defthm expt-x-3
   (equal (expt x 3) (* x x x))
   :hints (("Goal" :expand (expt x 3))
	   ("Subgoal 1" :expand (expt x 2)))))

(in-theory (disable expt))

;;; Now we build up the theory of alternating series.

;; We start by defining the "sign" function, returning -1, 0, or 1 for
;; negative, zero, and positive reals.

(defun sign (x)
  (if (< x 0)
      -1
    (if (= x 0)
	0
      1)))

;; Now we try some important lemmas.  We find the special case x*x*y
;; often, so we decide quickly that its sign is the sign of y, as long
;; as x is non-zero.

(defthm sign-*-x-x-y
  (implies (and (realp x)
		(case-split (not (= 0 x)))
		(realp y))
	   (equal (sign (* x x y))
		  (sign y))))

;; If x is positive, then the sign of x*y is just the sign of y....

(defthm sign-*-x-y
  (implies (and (realp x)
		(< 0 x)
		(realp y))
	   (equal (sign (* x y))
		  (sign y))))

;; Of course, sign(-x) = -sign(x)

(defthm sign--x
  (implies (acl2-numberp x)
	   (equal (sign (- x))
		  (- (sign x)))))

(in-theory (disable sign))

;; We consider two numbers to be of opposite sign if either one of
;; them is a zero or one is positive and the other negative.  The
;; reason for allowing zero to be of the "right" sign as needed is
;; that we want to consider a strictly zero sequence to be an
;; alternating sequence.

(defun opposite-signs-p (x y)
  (or (= x 0)
      (= y 0)
      (equal (sign x) (- (sign y)))))

;; Here is the definition of the first alternating sign property.  A
;; sequence has this property if successive elements are of opposite
;; signs.

(defun alternating-sequence-1-p (lst)
  (if (null lst)
      t
    (if (null (cdr lst))
	t
      (and (opposite-signs-p (car lst) (cadr lst))
	   (alternating-sequence-1-p (cdr lst))))))

;; The second alternating sign property is that successive elements
;; decrease in magnitude.  In the special case that one element is
;; zero, then all subsequent elements must also be zero.

(defun alternating-sequence-2-p (lst)
  (if (null lst)
      t
    (if (null (cdr lst))
	t
      (and (or (and (equal (car lst) 0)
		    (equal (cadr lst) 0))
	       (< (abs (cadr lst))
		  (abs (car lst))))
	   (alternating-sequence-2-p (cdr lst))))))

;; The two properties combine to define an alternating sequence.

(defun alternating-sequence-p (lst)
  (and (alternating-sequence-1-p lst)
       (alternating-sequence-2-p lst)))

;; Next, we want to consider the sum of an alternating sequence.  We
;; start by considering three cases, depending on the sign of the
;; first element of the sequence.  In all cases, the remaining terms
;; add up to a number that is smaller in magnitude than and opposite
;; in signs to that first element.

(defthm sumlist-alternating-sequence-lemma
  (implies (and (alternating-sequence-p x)
		(real-listp x)
		(not (null x)))
	   (cond ((< 0 (car x))
		  (and (< (- (car x)) (sumlist (cdr x)))
		       (<= (sumlist (cdr x)) 0)))
		 ((equal 0 (car x))
		  (and (equal (sumlist x) 0)
		       (equal (sumlist (cdr x)) 0)))
		 ((< (car x) 0)
		  (and (< (sumlist (cdr x)) (- (car x)))
		       (<= 0 (sumlist (cdr x)))))))
  :hints (("Subgoal *1/1"
	   :cases ((= 0 (car x))
		   (= 0 (cadr x))
		   (and (< 0 (car x)) (> 0 (cadr x)))
		   (and (< 0 (car x)) (< 0 (cadr x)))
		   (and (> 0 (car x)) (> 0 (cadr x)))
		   (and (> 0 (car x)) (< 0 (cadr x))))
	   :in-theory (enable abs sign)))
  :rule-classes nil)

;; Therefore, we can conclude that the sum of an alternating sequence
;; is smaller in magnitude than its first element.

(defthm sumlist-alternating-sequence
  (implies (and (alternating-sequence-p x)
		(real-listp x)
		(not (null x)))
	   (not (< (abs (car x)) (abs (sumlist x)))))
  :hints (("Goal"
	   :use ((:instance sumlist-alternating-sequence-lemma)))
	  ("Goal'"
	   :cases ((< 0 (car x))
		   (= 0 (car x))
		   (> 0 (car x)))
	   :in-theory (enable abs))))

;;; Next, we define the Taylor approximation to the sine function

;; We start with a simple term in the Taylor sequence.  This is just
;; x^n/n!, without even worrying about the alternating sign part.

(defun base-taylor-sin-term (x counter)
  (* (expt x counter)
     (/ (factorial counter))))

;; Now, we define the true term in the Taylor sequence, including the
;; sign bit twiddling.

(defun taylor-sin-term (x counter)
  (* (expt -1 counter)
     (base-taylor-sin-term x (1+ (* 2 counter)))))

;; Now, we can define the Taylor sequence.  Initially, this should be
;; called with counter=0.  Nterms is the number of terms desired in
;; the sequence, and x is the value you're taking the sine of.  So for
;; example, you would say (taylor-sin-list 10 0 1/2) to get the sine
;; of 1/2 by adding up the first 10 terms in the Taylor sequence.

(defun taylor-sin-list (nterms counter x)
  (if (or (zp nterms)
	  (not (integerp counter))
	  (< counter 0)
	  (not (realp x)))
      nil
    (cons (taylor-sin-term x counter)
	  (taylor-sin-list (1- nterms) (1+ counter) x))))

;; A silly theorem.  Sometimes (taylor-sin-list ....) appears as a
;; hypothesis in a theorem, just to show that it isn't equal to nil.
;; The following theorem tells ACL2 how to figure that out.

(defthm iff-taylor-sin-list
  (iff (taylor-sin-list nterms counter x)
       (and (not (zp nterms))
	    (integerp counter)
	    (<= 0 counter)
	    (realp x)))
  :hints (("Goal" :expand ((taylor-sin-list nterms counter x)))))

;; A typical ACL2 lemma.  How to "open up" (car (taylor-sin-list ...))
;; terms to get the first term in a sequence.

(defthm car-taylor-sin-list
  (equal (car (taylor-sin-list nterms counter x))
	 (if (and (not (zp nterms))
		  (integerp counter)
		  (<= 0 counter)
		  (realp x))
	     (taylor-sin-term x counter)
	   nil))
  :hints (("Goal" :expand ((taylor-sin-list nterms counter x)))))

;; This is an important lemma.  It defines a recurrence relation for
;; getting the terms in the Taylor sequence.

(local
 (defthm base-taylor-sin-term-x-+1-counter
   (implies (and (integerp counter)
		 (<= 0 counter))
   (equal (base-taylor-sin-term x (1+ counter))
	  (* x
	     (/ (+ 1 counter))
	     (base-taylor-sin-term x counter))))
   :hints (("Subgoal 2"
	    :expand ((hide (let ((x counter)) (+ 1 x)))))
	   ("Subgoal 1"
	    :expand ((hide (let ((x counter)) (+ 1 x))))))))

;; Since we're skipping all the even terms (those involving x^2n), we
;; really want to have a recurrence relation that goes up by 2 at a
;; time!

(local
 (defthm base-taylor-sin-term-x-+2-counter
   (implies (and (integerp counter)
		 (<= 0 counter))
	    (equal (base-taylor-sin-term x (+ 2 counter))
		   (* x
		      (/ (+ 2 counter))
		      (base-taylor-sin-term x (1+ counter)))))
   :hints (("Goal"
	    :use ((:instance base-taylor-sin-term-x-+1-counter
			     (counter (1+ counter))))
	    :in-theory (disable base-taylor-sin-term-x-+1-counter
				base-taylor-sin-term)))))

;; We usually end up looking at p(n) and p(n+3), so we show how that's
;; done here.  The reason "3" shows up is that we have (2n+1) and
;; (2(n+1)+1) which ends up being 2n+1 and 2n+3.  The 2n+1 gets
;; rewritten into 2n by the +1 rules, but that leaves 2n and 2n+3.

(local
 (defthm base-taylor-sin-term-x-+3-counter
   (implies (and (integerp counter)
		 (<= 0 counter))
	    (equal (base-taylor-sin-term x (+ 3 counter))
		   (* x
		      (/ (+ 3 counter))
		      (base-taylor-sin-term x (1+ (1+ counter))))))
   :hints (("Goal"
	    :use ((:instance base-taylor-sin-term-x-+1-counter
			     (counter (1+ (1+ counter)))))
	    :in-theory (disable base-taylor-sin-term-x-+1-counter
				base-taylor-sin-term)))))

;; Since we know how the base sine term (w/o the -1^n) behaves, now we
;; can look at the actual terms in the Taylor requence.

(local
 (defthm taylor-sin-term-x-+1-counter
   (implies (and (integerp counter)
		 (<= 0 counter))
	    (equal (taylor-sin-term x (+ 1 counter))
		   (* -1 x x (/ (+ 3 (* 2 counter))) (/ (+ 2 (* 2 counter)))
		      (taylor-sin-term x counter))))
   :hints (("Goal" :in-theory (disable base-taylor-sin-term)))))


;; Obviously, such terms are real...sigh....

(defthm realp-taylor-sin-term
  (implies (and (realp x)
		(integerp counter))
	   (realp (taylor-sin-term x counter)))
  :rule-classes (:rewrite :type-prescription))

(in-theory (disable taylor-sin-term))

;; It is simple to show that adjacent terms in the Taylor sign
;; sequence have opposite signs.

(defthm opposite-signs-p-taylor-sin-term
  (implies (and (integerp counter)
		(<= 0 counter)
		(realp x))
	   (opposite-signs-p (taylor-sin-term x counter)
			     (taylor-sin-term x (1+ counter)))))

;; And so, we get the first property required for an alternating
;; sequence.

(defthm alternating-sequence-1-p-taylor-sin-list
  (alternating-sequence-1-p (taylor-sin-list nterms counter x)))


;; The second property is harder.  We start by showing that if n is
;; large enough, successive terms a_n and a_{n+1} decrease in
;; magnitude.  "Large enough" is in relation to x.

(encapsulate
 ()

 ;; ACL2 is pathetic when it comes to algebra.  So, we start with some
 ;; simplifications....

 (local
  (defthm lemma0
    (implies (and (realp 3-ax) (<= 0 3-ax)
		  (realp 1-fc) (< 0 1-fc)
		  (realp 4-c)  (<= 0 4-c)
		  (realp 2-ex) (< 0 2-ex))
	     (iff (< (* 3-ax 1-fc 4-c 2-ex) (* 1-fc 2-ex))
		  (< (* 3-ax 4-c) 1)))))

 ;; That's all that's needed to prove the desired result.  After a
 ;; certain point, successive terms decrease in magnitude.

 (defthm abs-base-taylor-sin-term-decreasing
  (implies (and (integerp counter)
		(<= 0 counter)
		(realp x)
		(not (equal x 0))
		(< (abs x) counter))
	   (< (abs (base-taylor-sin-term x (1+ counter)))
	      (abs (base-taylor-sin-term x counter))))))

;; Now, the terms in the sequence are always real numbers.

(defthm realp-base-taylor-sin-term
  (implies (realp x)
	   (realp (base-taylor-sin-term x counter)))
  :rule-classes (:rewrite :type-prescription))

;; Moreover, if x is zero, sine(x) starts with a zero -- watch out for
;; the empty list case!

(defthm base-taylor-sin-term-zero
  (equal (base-taylor-sin-term 0 counter)
	 (if (zip counter) 1 0))
  :hints (("Goal" :in-theory (enable factorial))))

;; And, if x is non-zero, the Taylor sequence for sine(x) has no zeros.

(defthm base-taylor-sin-term-non-zero
  (implies (not (equal (fix x) 0))
	   (not (equal (base-taylor-sin-term x counter) 0))))

(in-theory (disable base-taylor-sin-term))

;; We already know that successive base terms (i.e., without the -1^n)
;; decrease in magnitude.  Now, we carry that out to two terms out,
;; since we're skipping all the even terms.

(defthm abs-base-taylor-sin-term-decreasing-2
  (implies (and (integerp counter)
		(<= 0 counter)
		(realp x)
		(not (equal x 0))
		(< (abs x) counter))
	   (< (abs (base-taylor-sin-term x (+ 2 counter)))
	      (abs (base-taylor-sin-term x counter))))
  :hints (("Goal"
	   :use ((:instance abs-base-taylor-sin-term-decreasing
			    (counter (+ 1 counter)))
		 (:instance abs-base-taylor-sin-term-decreasing))
	   :in-theory (disable abs-base-taylor-sin-term-decreasing
			       base-taylor-sin-term-x-+2-counter))))

;; Same as the previous theorem, except we're looking at terms of the
;; form 2n+1 and 2n+3, since those are the ones we actually look for
;; -- i.e., successive odd terms.

(defthm abs-base-taylor-sin-term-decreasing-3
  (implies (and (integerp counter)
		(<= 0 counter)
		(realp x)
		(not (equal x 0))
		(< (abs x) counter))
	   (< (abs (base-taylor-sin-term x (+ 3 counter)))
	      (abs (base-taylor-sin-term x (+ 1 counter)))))
  :hints (("Goal"
	   :use ((:instance abs-base-taylor-sin-term-decreasing-2
			    (counter (1+ counter)))
		 (:instance abs-base-taylor-sin-term-decreasing-2))
	   :in-theory (disable abs-base-taylor-sin-term-decreasing
			       abs-base-taylor-sin-term-decreasing-2
			       base-taylor-sin-term-x-+3-counter
			       base-taylor-sin-term-x-+2-counter))))

(in-theory (enable taylor-sin-term))

;; Since the -1^n doesn't contribute to an abs(...), we can get it out
;; of the Taylor magnitude computation.

(defthm abs-of-taylor-sin-term
  (implies (and (integerp counter)
		(<= 0 counter)
		(realp x))
	   (equal (abs (taylor-sin-term x counter))
		  (abs (base-taylor-sin-term x (1+ (* 2 counter))))))
  :hints (("Goal"
	   :in-theory (enable taylor-sin-term))))

;; And that's all we need to show that successive terms in the real
;; Taylor sine sequence decrease -- as long as we go far enough out in
;; the sequence.

(defthm abs-taylor-sin-term-decreasing
  (implies (and (integerp counter)
		(<= 0 counter)
		(realp x)
		(not (equal x 0))
		(< (abs x) counter))
	   (< (abs (taylor-sin-term x (1+ counter)))
	      (abs (taylor-sin-term x counter))))
  :hints (("Goal"
	   :in-theory (disable taylor-sin-term-x-+1-counter
			       base-taylor-sin-term-x-+3-counter
			       base-taylor-sin-term-x-+2-counter
			       base-taylor-sin-term-x-+1-counter))))

;; Now, we characterize the Taylor sequence terms for when x is zero
;; and non-zero.  If zero, then all terms are zero....

(defthm taylor-sin-term-zero
  (implies (and (integerp counter)
		(<= 0 counter))
	   (equal (taylor-sin-term 0 counter) 0))
  :hints (("Goal" :expand ((taylor-sin-term 0 counter)))))

;; ...otherwise, no terms are equal to zero.

(defthm taylor-sin-term-non-zero
  (implies (not (equal (fix x) 0))
	   (not (equal (taylor-sin-term x counter) 0)))
  :hints (("Goal" :expand ((taylor-sin-term x counter)))))

(in-theory (disable taylor-sin-term))

(local
 (in-theory (disable base-taylor-sin-term-x-+3-counter
		     base-taylor-sin-term-x-+2-counter
		     base-taylor-sin-term-x-+1-counter)))

;; So we get a trivial result.  When x=0, the Taylor expansion of
;; sin(x) -- which is a list of zeros -- satisfies the second property
;; for alternating sequences (non-zero terms decrease in magnitude,
;; and zeros continue until the end of time).

(local
 (defthm alternating-sequence-2-p-taylor-sin-list-0
   (alternating-sequence-2-p (taylor-sin-list nterms counter 0))))

;; More importantly, we get that this magnitude-decreasing property is
;; true when x is non-zero, as long as we go out far enough in the
;; sequence.

(local
 (defthm alternating-sequence-2-p-taylor-sin-list-non-0
   (implies (and (not (equal x 0))
		 (< (abs x) counter))
	    (alternating-sequence-2-p (taylor-sin-list nterms counter x)))
   :hints (("Goal"
	    :in-theory (disable taylor-sin-term-x-+1-counter)))))

;; So, as long as we go far enough out in the sequence, we know the
;; magnitude-decreasing property is true for all Taylor sine
;; sequences, regardless of the value of x.

(defthm alternating-sequence-2-p-taylor-sin-list
   (implies (< (abs x) counter)
	    (alternating-sequence-2-p (taylor-sin-list nterms counter x)))
   :hints (("Goal"
	    :cases ((= x 0)))))

;; So that means if you go enough out, both properties are met for an
;; alternating sequence.  Hence the Taylor sequence for sine has a
;; suffix that is an alternating sequence.

(defthm alternating-sequence-p-taylor-sin-list
  (implies (< (abs x) counter)
	   (alternating-sequence-p (taylor-sin-list nterms counter x))))

;; But what about the first part of the sequence?  The first step is
;; to show that if we go out only a limited number of steps, the
;; resulting sum is still limited.

(encapsulate
 ()

 ;; A trivial fact is that -1^n is limited -- trivial since it's
 ;; either -1 or 1!

 (local
  (defthm limited-expt--1-counter
    (i-limited (expt -1 counter))
    :hints (("Goal"
	     :use ((:instance expt--1-counter)))
	    ("Subgoal 1"
	     :induct (expt -1 counter)
	     :in-theory (enable expt)))))

 ;; An important lemma:  When x is limited, the nth term in the Taylor
 ;; expansion of sine(x) is also limited (as long as n is limited.)

 (local
  (defthm limited-base-taylor-sin-term
    (implies (and (<= 0 counter)
	      	  (i-limited counter)
	      	  (i-limited x))
	     (i-limited (base-taylor-sin-term x counter)))
    :hints (("Goal" :in-theory (enable base-taylor-sin-term)))))

 ;; This holds even if we consider the -1^n term -- duh!

 (defthm limited-taylor-sin-term
   (implies (and (<= 0 counter)
		 (i-limited counter)
		 (i-limited x))
	    (i-limited (taylor-sin-term x counter)))
   :hints (("Goal" :in-theory (enable taylor-sin-term))))

 ;; Since we're talking about summing up a limited number of limited
 ;; numbers, we find that the sum of the first n terms in the Taylor
 ;; sequence of the sine of a limited x is also limited.

 (defthm taylor-sin-list-limited-up-to-limited-counter
   (implies (and (i-limited nterms)
		 (integerp counter)
		 (i-limited counter)
		 (i-limited x))
	    (i-limited (sumlist (taylor-sin-list nterms counter x))))
   :hints (("Goal" :in-theory (enable limited-integers-are-standard))))
 )

;; So now, we show that the sum of a Taylor sine sequence can be split
;; into two arbitrary parts.

(defthm taylor-sin-list-split
  (implies (and (integerp n1)
		(<= 0 n1)
		(integerp n2)
		(<= 0 n2)
		(integerp counter)
		(<= 0 counter))
	   (equal (taylor-sin-list (+ n1 n2) counter x)
		  (append (taylor-sin-list n1 counter x)
			  (taylor-sin-list n2 (+ counter n1) x)))))

;; To get the split we want, we define the next-integer function.
;; This is very much like the "ceiling" function, but without using
;; non-negative-integer-quotient, so it's easier to reason about!
;; It's actually not quite ceiling, since next-integer(1) == 2....

(defun next-integer (x)
  (1+ (floor1 x)))

;; We show that next-integer(x) <= 1+x....

(local
 (defthm next-integer-<=-x+1
   (implies (realp x)
	    (not (< (+ 1 x) (next-integer x))))
   :otf-flg t
   :rule-classes (:linear :rewrite)))

;; ...and x < next-integer(x).  Note for ceiling, the "=" part of the
;; inequality moves over.

(local
 (defthm x-<-next-integer
   (implies (realp x)
	    (< x (next-integer x)))
   :rule-classes (:linear :rewrite)))

;; We have that next-integer(|x|)>=0 since |x|>= 0

(defthm next-integer-positive
  (implies (realp x)
	   (not (< (next-integer (abs x)) 0)))
  :rule-classes (:linear :rewrite))

;; Better yet, we have that next-integer(|x|)>0 since |x|>=0 and
;; next-integer(x)=1 for 0<=x<1....

(defthm next-integer-positive-stronger
  (implies (realp x)
	   (< 0 (next-integer (abs x))))
  :rule-classes (:linear :rewrite))

(in-theory (disable next-integer))

;; Trivially, if x is limited, so is next-integer(x)....

(defthm limited-next-integer
  (implies (and (realp x)
		(<= 0 x)
		(i-limited x))
	   (i-limited (next-integer x)))
  :hints (("Goal"
	   :use ((:instance large-if->-large
			    (x (next-integer x))
			    (y (1+ x))))
	   :in-theory (enable-disable (standards-are-limited)
				      (large-if->-large)))))

;; ...and for that matter, so is next-integer(abs(x))

(defthm limited-next-integer-abs
  (implies (and (realp x)
		(i-limited x))
	   (i-limited (next-integer (abs x))))
  :hints (("Goal" :in-theory (enable abs))))

;; Because of that, if x is limited, next-integer(x) < i-large-integer!

(defthm next-integer-abs-<-i-large-integer
  (implies (and (realp x)
		(i-limited x))
	   (not (< (i-large-integer)
		   (next-integer (abs x)))))
  :hints (("Goal"
	   :use ((:instance large->-non-large
			    (x (i-large-integer))
			    (y (next-integer (abs x)))))
	   :in-theory (disable large->-non-large)))
  :rule-classes (:rewrite :linear))

;; Now, we show how we want to split up a Taylor sequence.  Basically,
;; we look at the first |x| elements, and the remaining elements.

(defthm taylor-sin-list-split-for-limited
  (implies (and (realp x)
		(i-limited x)
		(integerp counter)
		(<= 0 counter))
	   (equal (taylor-sin-list (i-large-integer) counter x)
		  (append (taylor-sin-list (next-integer (abs x)) counter x)
			  (taylor-sin-list (- (i-large-integer)
					      (next-integer (abs x)))
					   (+ counter (next-integer (abs x)))
					   x))))
  :hints (("Goal"
	   :use ((:instance taylor-sin-list-split
			    (n1 (next-integer (abs x)))
			    (n2 (- (i-large-integer)
				   (next-integer (abs x))))))
	   :in-theory (disable taylor-sin-list-split))))

;; The Taylor sequence for sine is a sequence of real numbers....

(defthm real-listp-taylor-sin-list
  (real-listp (taylor-sin-list nterms counter x)))

;; Any element of a Taylor sequence for sine, even when we go out past
;; the |x|th element is limited.

(defthm limited-real-car-taylor-sin-list
  (implies (and (integerp nterms)
		(< 0 nterms)
		(integerp counter)
		(<= 0 counter)
		(i-limited counter)
		(realp x)
		(i-limited x)
		(< (abs x) counter))
	   (and (realp (car (taylor-sin-list nterms counter x)))
		(i-limited (car (taylor-sin-list nterms counter x))))))

;; So, since the sequence is alternating after we go out far enough,
;; we can conclude that the sum of that alternating part is limited
;; (since it's no larger than its first element, which we just showed
;; was limited).

(defthm taylor-sin-list-limited-alternating-part
  (implies (and (not (zp nterms))
		(integerp counter)
		(<= 0 counter)
		(i-limited counter)
		(realp x)
		(i-limited x)
		(< (abs x) counter))
	   (i-limited (sumlist (taylor-sin-list nterms counter x))))
  :hints (("Goal"
	   :use ((:instance large-if->-large
			    (x (car (taylor-sin-list nterms counter x)))
			    (y (sumlist (taylor-sin-list nterms counter x))))
		 (:instance sumlist-alternating-sequence
			    (x (taylor-sin-list nterms counter x)))
		 (:instance alternating-sequence-p-taylor-sin-list)
		 )
	   :in-theory (disable large-if->-large
			       sumlist-alternating-sequence
			       alternating-sequence-p
			       alternating-sequence-p-taylor-sin-list
			       car-taylor-sin-list
			       taylor-sin-list))))

;; Now we prove some lemmas that come up in showing that the entire
;; sequence is limited.

;; First, the first part of the sequence is limited -- it's the sum of
;; a limited number of limited numbers....

(defthm taylor-sin-list-limited-lemma-1
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(realp x)
		(i-limited x))
	   (i-limited (sumlist (taylor-sin-list (next-integer (abs x))
						0 x)))))

;; The second half is also limited -- it's an alternating sequence
;; starting up with a limited term.

(defthm taylor-sin-list-limited-lemma-2
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(realp x)
		(i-limited x))
	   (i-limited (sumlist (taylor-sin-list nterms
						(next-integer (abs x))
						x))))
  :hints (("Goal" :cases ((< 0 nterms)))))

;; Since both parts are limited, so is their sum...

(defthm taylor-sin-list-limited-lemma
  (implies (and (integerp nterms)
		(<= 0 nterms)
		(realp x)
		(i-limited x))
	   (i-limited (+ (sumlist (taylor-sin-list (next-integer (abs x))
						   0 x))
			 (sumlist (taylor-sin-list nterms
						   (next-integer (abs x))
						   x))))))

;; And so, the entire sequence is limited!

(defthm taylor-sin-list-limited-almost
  (implies (and (realp x)
		(i-limited x))
	   (i-limited (sumlist (taylor-sin-list (i-large-integer) 0 x))))
  :hints (("Goal"
	   :use ((:instance taylor-sin-list-limited-lemma
			    (nterms (- (i-large-integer)
				       (next-integer (abs x))))))
	   :in-theory (disable taylor-sin-list-limited-lemma))))

;; But wait, we had an extra hypothesis in there, about x being real.
;; We can get rid of it, since sine(x)=0 when x is not real....

(defthm taylor-sin-list-limited
  (implies (i-limited x)
	   (i-limited (sumlist (taylor-sin-list (i-large-integer) 0 x))))
  :hints (("Goal" :cases ((realp x)))))

;;; Now we can define the sine function.  We had to wait until this
;;; point, because the defun-std principle requires that we prove that
;;; the function body returns a standard number when its argument is
;;; standard.  That's true in this case, since we're taking a
;;; standard-part -- but only if the sumlist is limited.  We've just
;;; proved that above, and so we can introduce the sine function!

(defun-std sine (x)
  (if (acl2-numberp x)
      (standard-part (sumlist (taylor-sin-list (i-large-integer) 0 x)))
      0))

;;; Now let's prove something about it.  We'll show that
;;; sin(-x)=-sin(x).

;; First, the nth term in the Taylor sequence for -x is minus the nth
;; term of the sequence for x.  I.e., we prove the result for each
;; term in the sequence first.

(defthm taylor-sin-term-uminus
  (implies (and (realp x)
		(integerp counter)
		(<= 0 counter))
	   (equal (taylor-sin-term (- x) counter)
		  (- (taylor-sin-term x counter))))
  :hints (("Goal" :in-theory (enable taylor-sin-term base-taylor-sin-term))))

;; Since it's true for each term, the result follows when we add up
;; all the terms.

(defthm taylor-sin-list-uminus
  (implies (realp x)
	   (equal (sumlist (taylor-sin-list nterms counter (- x)))
		  (- (sumlist (taylor-sin-list nterms counter x))))))

;; And now, we can prove the result for the actual sine function.
;; Defthm-std lets us prove the theorem by worrying only about the
;; standard values of x.  There, we can open up the body to find a
;; standard-part term -- note that unary minus can go through a
;; standard-part, so that's not a problem.  Inside the standard-part
;; is a (sumlist ... -x) term and a (sumlist ... x) -- and there we
;; can use the previous term to take the unary minus out of the
;; sumlist and then out of the standard-part.  Voila!

(defthm-std sine-uminus
  (implies (realp x)
	   (equal (sine (- x))
		  (- (sine x)))))

;;; Now another cute theorem.  Let's approximate sine(1/2).

;; We'll use three terms in the Taylor sequence.  For starters, we
;; need to know we're looking at a limited sequence -- i.e., 3 is a
;; limited number....duh....

(defthm 3-<-i-large-integer
  (< 3 (i-large-integer))
  :hints (("Goal" :use ((:instance large->-non-large
				   (x (i-large-integer))
				   (y 3)))
	   :in-theory (disable large->-non-large)))
  :rule-classes (:linear :rewrite))

;; Now, we show how we can split the Taylor sequence into its first
;; three terms and then the rest.

(defthm taylor-sin-approx-by-3
  (equal (sumlist (taylor-sin-list (i-large-integer) 0 x))
	 (+ (sumlist (taylor-sin-list 3 0 x))
	    (sumlist (taylor-sin-list (- (i-large-integer) 3) 3 x))))
  :hints (("Goal"
	   :use ((:instance taylor-sin-list-split
			    (n1 3)
			    (n2 (- (i-large-integer) 3))
			    (counter 0)))
	   :in-theory (disable taylor-sin-list-split))))

;; We find a bound for "the rest" of the terms.  We can do this since
;; we know the sequence is alternating here -- because 3 is bigger
;; than next-integer(1/2)!  So first, show that it's alternating...

(defthm taylor-sin-approx-by-3-error-lemma
  (implies (< (abs x) 3)
	   (alternating-sequence-p (taylor-sin-list  (- (i-large-integer) 3) 3 x)))
  :hints (("Goal" :in-theory (disable taylor-sin-list alternating-sequence-p))))

;; A silly lemma:  the taylor-sin-list term is not nil, because it's a
;; non-empty list.

(local
 (defthm taylor-sin-list-approx-by-3-error-silly-lemma
   (implies (realp x)
	    (taylor-sin-list (binary-+ (i-large-integer) '-3) '3 x))
   :hints (("Goal" :in-theory (disable taylor-sin-list-split)))))

;; Now, we can get an upper bound for the error as the absolute value
;; of the 4th term in the sequence.

(defthm taylor-sin-approx-by-3-error
  (implies (and (< (abs x) 3)
		(realp x))
	   (not (< (abs (car (taylor-sin-list (- (i-large-integer) 3) 3 x)))
		   (abs (sumlist (taylor-sin-list (- (i-large-integer) 3)
						  3
						  x))))))
  :hints (("Goal"
	   :use ((:instance sumlist-alternating-sequence
			    (x (taylor-sin-list (- (i-large-integer) 3) 3 x))))
	   :in-theory (disable car-taylor-sin-list
			       taylor-sin-list
			       sumlist-alternating-sequence))))

;; Let's rewrite that error bound as the difference of the first half
;; of the sequence and the whole sequence, instead of just the sum of
;; the second half....

(defthm taylor-sin-approx-by-3-error-better
  (implies (and (< (abs x) 3)
		(realp x))
	   (not (< (abs (car (taylor-sin-list (- (i-large-integer) 3) 3 x)))
		   (abs (- (sumlist (taylor-sin-list (i-large-integer) 0 x))
			   (sumlist (taylor-sin-list 3 0 x)))))))
  :hints (("Goal"
	   :use ((:instance taylor-sin-approx-by-3-error))
	   :in-theory (disable car-taylor-sin-list
			       taylor-sin-list
			       taylor-sin-approx-by-3-error))))

;; Quick needed type lemma: we're talking about real Taylor sine terms....

(defthm realp-car-taylor-sin-approx-3
  (implies (realp x)
	   (realp (abs (car (taylor-sin-list (binary-+ (i-large-integer) -3)
					     3
					     x))))))

;; Now, add "standard-part" to our error bounds, so we have it just
;; like it will be in the definition of sine.

(defthm taylor-sin-approx-by-3-error-best
  (implies (and (< (abs x) 3)
		(realp x))
	   (not (< (standard-part (abs (car (taylor-sin-list (- (i-large-integer) 3) 3 x))))
		   (standard-part (abs (- (sumlist (taylor-sin-list (i-large-integer) 0 x))
					  (sumlist (taylor-sin-list 3 0 x))))))))
  :hints (("Goal"
	   :use ((:instance taylor-sin-approx-by-3-error-better))
	   :in-theory (disable taylor-sin-approx-by-3-error-better))))

;; I've no clue why ACL2 doesn't do this on its own.  Shrug.

(defthm sine-one-half-silly
  (equal (+ 1/2
	    X
	    -1841/3840)
	 (+ X 79/3840)))

;; Just as I had decided nobody would ever use an integer larger than
;; 10,000, here comes 645,120.....so we have to prove it's standard
;; from scratch.  Luckily, 645,120 = 5376*120, so it's easy :-)
;; -- Actually, we no longer need this now that standard-numberp can be
;; executed.

#|
(defthm standard-1/645120
  (standard-numberp 1/645120)
  :hints (("Goal"
	   :by (:instance standard-numberp-rationals-num-demom-100000000
			  (x 1/645120)))))
|#

;; standard-part(abs) = abs(standard-part), since unary minus goes
;; through standard-parts

(defthm standard-part-abs
  (implies (realp x)
	   (equal (standard-part (abs x))
		  (abs (standard-part x))))
  :hints (("Goal" :in-theory (enable abs))))

;; Trivial theorem, needed by the rewriter.  The sum of a Taylor sine
;; sequence is a real number.

(defthm realp-sumlist-taylor-sin-list
  (realp (sumlist (taylor-sin-list nterms counter x))))

;; And finally, here's an approximation for sine(1/2), together with a
;; very tight error bound!

(defthm sine-one-half
  (<= (abs (- (sine 1/2)
	      1841/3840))
      1/645120)
  :hints (("Goal"
	   :use ((:instance taylor-sin-approx-by-3-error-best (x 1/2)))
	   :in-theory (disable taylor-sin-approx-by-3-error-best
			       taylor-sin-approx-by-3
			       taylor-sin-list))))
