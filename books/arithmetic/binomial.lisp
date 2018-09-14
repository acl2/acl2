;;; Contributed by Ruben A. Gamboa

; Copyright (C) 2014, University of Wyoming
; All rights reserved.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;; This file includes a proof of the binomial theorem.

(in-package "ACL2")

(local (include-book "top"))
(include-book "factorial")
(include-book "sumlist")

;; We begin with the definition of (choose k n), which counts the
;; number of ways k items can be selected out of n distinct items.

(defun choose (k n)
  ; (declare (xargs :guard (and (integerp k) (integerp n) (<= 0 k) (<= k n))))
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (/ (factorial n)
	 (* (factorial k) (factorial (- n k))))
    0))

;; Unfortunately, ACL2 looks at the previous definition and assumes
;; that choose is a rational number -- not necessarily integer.  So
;; our first step is to establish the fact that choose is an integer
;; function.  First we need a few simplification rules.


;; The first rule is that n!/(n-1)! is equal to n.....

(defthm factorial-n/n-1
  (implies (and (integerp n)
		(<= 1 n))
	   (equal (* (factorial n)
		     (/ (factorial (+ -1 n))))
		  n))
  :hints (("Goal" :expand ((factorial n)))))

;; A more powerful rule is that n!*x/(n-1)! is equan to n*x.

(local
 (defthm factorial-n/n-1/x
   (implies (and (integerp n)
		 (<= 1 n))
	    (equal (* (factorial n)
		      (/ (factorial (+ -1 n)))
		      x)
		   (* n x)))))

;; Now, we can prove the following lemma, which was suggested to us by
;; Matt Kaufmann (thanks, Matt!).  We show that the choose function
;; can be defined by a recurrence relation.  Basically, the way to
;; choose k things out of n things is to choose 1 thing and take it
;; out.  Then, if we decide to choose that item, we need to pick an
;; additional k-1 things out of n-1 things; if not, we still need to
;; pick k things out of n-1 things....  The sum of those is the number
;; we want.

(defthm choose-reduction
  (implies (and (integerp k)
		(integerp n)
		(< 0 k)
		(< k n))
	   (equal (choose k n)
		  (+ (choose (1- k) (1- n))
		     (choose k (1- n)))))

; Matt K. change for v2-9: Subgoal number has changed, probably because of the
; change to call-stack to preserve quote-normal form.

  :hints (("Subgoal 4'" :expand ((factorial n))))
  :rule-classes nil)


;; So, we can define a new function choose-mk which follows the
;; recurrence mentioned above....

(defun choose-mk (k n)
  (if (and (integerp k)
	   (integerp n))
      (if (and (< 0 k)
	       (< k n))
	  (+ (choose-mk (1- k) (1- n))
	     (choose-mk k (1- n)))
	(if (and (<= 0 k)
		 (<= k n))
	    1
	  0))
    0))

;; ...and we can prove that it's the exact same function as choose.

(defthm choose-mk-choose
  (equal (choose-mk k n)
	 (choose k n))
  :hints (("Goal" :induct (choose-mk k n))
	  ("Subgoal *1/1" :use (:instance choose-reduction)
	   :in-theory (disable choose)))
  :rule-classes nil)

;; Now, the function choose-mk is obviously integer, so that means
;; choose must be obviously integer!

(defthm choose-is-non-negative-integer
  (and (integerp (choose k n))
       (<= 0 (choose k n)))
  :hints (("Goal" :use (:instance choose-mk-choose)
	   :in-theory (disable choose choose-mk)))
  :rule-classes (:rewrite :type-prescription))


;; We can now define the binomial expansion of (x+y)^n, starting at
;; the term containing x^k.  I.e., to get the entire binomial
;; expansion, use (binomial-expansion x y 0 n).

(defun binomial-expansion (x y k n)
  (declare (xargs :measure (nfix (1+ (- n k)))))
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (cons (* (choose k n) (expt x k) (expt y (- n k)))
	    (binomial-expansion x y (1+ k) n))
    nil))

;; We find it useful to explicitly define the expansion of x*(x+y)^n.

(defun binomial-expansion-times-x (x y k n)
  (declare (xargs :measure (nfix (1+ (- n k)))))
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (cons (* (choose k n) (expt x (1+ k)) (expt y (- n k)))
	    (binomial-expansion-times-x x y (1+ k) n))
    nil))

;; This lemma shows that our expansion for x*(x+y)^n indeed works.

(defthm binomial-expansion-times-x-correct
  (equal (* x (sumlist (binomial-expansion x y k n)))
	 (sumlist (binomial-expansion-times-x x y k n)))
  :hints (("Goal" :in-theory (disable choose))))

;; Similarly, we define an expansion of y*(x+y)^n....

(defun binomial-expansion-times-y (x y k n)
  (declare (xargs :measure (nfix (1+ (- n k)))))
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (cons (* (choose k n) (expt x k) (expt y (1+ (- n k))))
	    (binomial-expansion-times-y x y (1+ k) n))
    nil))

;; ...and prove it works, too.

(defthm binomial-expansion-times-y-correct
  (equal (* y (sumlist (binomial-expansion x y k n)))
	 (sumlist (binomial-expansion-times-y x y k n)))
  :hints (("Goal" :in-theory (disable choose))))

;; The following function expands (x+y)^n in a manner reminiscent of
;; Pascal's triangle.  Consider (x+y)^n.  It is equal to
;; (x+y)*(x+y)^{n-1} or x*(x+y)^{n-1} + y*(x+y)^{n-1}.  If we can show
;; that the binomial theorem is true for (x+y)^{n-1} (for induction,
;; for example), then we can reduce (x+y)^n to x times the binomial
;; expansion of (x+y)^{n-1} plus y times the binomial expansion of
;; (x+y)^{n-1} -- and we already have a function for x/y * the
;; binomial expansion of (x+y) from above!  We start with a function
;; which computes x*(x+y)^{n-1} + y*(x+y)^{n-1} by interleaving the
;; terms from each of the two sums.  I.e., x*a1, y*a1, x*a2, y*a2, etc
;; where ai are the terms in the binomial expansion of (x+y)^{n-1}.

(defun binomial-expansion-triangle (x y k n)
  (declare (xargs :measure (nfix (1+ (- n k)))))
  (if (and (integerp k) (integerp n) (<= 0 k) (<= k n))
      (cons (* (choose k n) (expt x (1+ k)) (expt y (- n k)))
	    (cons (* (choose k n) (expt x k) (expt y (1+ (- n k))))
		  (binomial-expansion-triangle x y (1+ k) n)))
    nil))

;; This is the key lemma that states that our function defined above
;; really does behave the way we said it did.

(defthm binomial-expansion-times-x-plus-times-y
  (equal (+ (sumlist (binomial-expansion-times-x x y k n))
	    (sumlist (binomial-expansion-times-y x y k n)))
	 (sumlist (binomial-expansion-triangle x y k n)))
  :hints (("Goal" :in-theory (disable choose expt))))

;; The following function computes the same value, but it does it by
;; emulating Pascal's triangle directly.  We will next show that this
;; function computes the same value as above, and hence that it is a
;; faithful computation of (a+b)^n.  Later, we will only have to
;; reduct the two choose terms below by collecting like x^k*y^{n-k}
;; terms and we'll have the needed result.

(defun binomial-expansion-pascal-triangle (x y k n)
  (declare (xargs :measure (nfix (1+ (- n k)))))
  (if (and (integerp k) (integerp n) (<= 0 k))
      (if (< k n)
	  (cons       (* (choose k n)      (expt x (1+ k)) (expt y (- n k)))
		(cons (* (choose (1+ k) n) (expt x (1+ k)) (expt y (- n k)))
		      (binomial-expansion-pascal-triangle x y (1+ k) n)))
	(if (= k n)
	    (list (* (choose k n) (expt x (1+ k)) (expt y (- n k))))
	  nil))
    nil))

;; Interesting that ACL2 needs a rewrite rule for this....

(local
 (defthm silly-inequality
   (implies (and (integerp k)
		 (integerp n)
		 (< k n))
	    (<= (+ 1 k) n))))

;; Now we need to show ACL2 how to reduse some of the terms that
;; appear in the main proof below.  First (choose k k) is equal to 1
;; (except in malformed cases when it's equal to 0).


(local
 (defthm choose-k-k
   (equal (choose k k)
	  (if (and (integerp k) (<= 0 k))
	      1
	    0))))

;; I think this is proved elsewhere, but x^0 = 1.

(local
 (defthm expt-x-0
   (equal (expt x 0) 1)))

;; Now, the binomial-expansion-triangle function returns an empty list
;; when we want to start at item k+1 and go up to item k....

(local
 (defthm binomial-expansion-triangle-x-y-k-1+k
   (equal (binomial-expansion-triangle x y (+ 1 k) k) nil)
   :hints (("Goal" :expand (binomial-expansion-triangle x y (+ 1 k) K)))))

;; We also show how the last term in the binomial-expansion-triangle
;; is expanded.

(local
 (defthm binomial-expansion-triangle-x-y-k-k-lemma
   (equal (binomial-expansion-triangle x y k k)
	  (if (and (integerp k) (<= 0 k))
	      (list (expt x (1+ k))
		    (* (expt x k) y))
	    nil))))

;; And finally, we can show that the Pascal triangle develops the
;; correct binomial coefficients....

(defthm binomial-expansion-pascal-triangle-correct
  (implies (and (integerp k) (integerp n) (<= 0 k) (<= k n))
	   (equal (sumlist (binomial-expansion-triangle x y k n))
		  (+ (* (choose k n) (expt x k) (expt y (1+ (- n k))))
		     (sumlist (binomial-expansion-pascal-triangle x y k n)))))
  :hints (("Goal"
	   :in-theory (disable choose expt
			       right-unicity-of-1-for-expt
			       expt-minus distributivity-of-expt-over-*
			       exponents-multiply
			       functional-commutativity-of-expt-/-base
			       exponents-add
			       exponents-add-for-nonneg-exponents))
	  ("Subgoal *1/5"
	   :in-theory (disable choose expt))))

;; Now, we show what happens when we try to get the binomial-expansion
;; of an empty interval.

(defthm binomial-expansion-zero
  (implies (< n k)
	   (equal (binomial-expansion x y k n) nil)))

;; From our previous lemma, we can establish quickly that the Pascal
;; triangle computes the same value as the binomial expansion.

(defthm pascal-triangle-binomial
  (implies (and (integerp k) (integerp n) (<= 0 k))
	   (equal (sumlist (binomial-expansion-pascal-triangle x y k n))
		  (sumlist (binomial-expansion x y (1+ k) (1+ n)))))
  :hints (("Goal"
	   :induct (binomial-expansion-pascal-triangle x y k n)
	   :in-theory (disable choose expt
			       right-unicity-of-1-for-expt
			       expt-minus distributivity-of-expt-over-*
			       exponents-multiply
			       functional-commutativity-of-expt-/-base
			       exponents-add
			       exponents-add-for-nonneg-exponents))
	  ("Subgoal *1/1''"
	   :use ((:instance choose-reduction
			    (k (+ 1 k))
			    (n (+ 1 n)))))))

;; We are almost ready now to prove the binomial theorem.  First, we
;; show ACL2 how to evaluate more terms that appear in the proofs to
;; follow.  For example, there's only 1 way to choose the empty set
;; out of a bunch of items -- unless we have a malformed set, in which
;; case it happens to be 0....

(defthm choose-0-n
  (equal (choose 0 n)
	 (if (and (integerp n) (<= 0 n))
	     1
	   0)))

;; The heart of the proof is the following lemma, which formalizes the
;; (x+y)^n = x*(x+y)^{n-1} + y*(x+y)^{n-1} argument given earlier.

(defthm binomial-theorem-induction-lemma
  (implies (and (integerp n) (< 0 n))
	   (equal (+ (* x (sumlist (binomial-expansion x y 0 (1- n))))
		     (* y (sumlist (binomial-expansion x y 0 (1- n)))))
		  (sumlist (binomial-expansion x y 0 n))))

  :hints (("Goal"
	   :in-theory (disable expt))))

;; It's easier to reason about the following function than about the
;; real expt function -- take a look at the definition of expt to see
;; what we mean!

(defun n-expt (x n)

; The conjunct (<= 0 n) was formerly (<= n 0), which was wrong (as pointed out
; in an acl2-help email from Dmitry Nadezhin, Sept. 12, 2018).

  (declare (xargs :guard (and (acl2-numberp x) (integerp n) (<= 0 n))))
  (if (and (integerp n) (< 0 n))
      (* x (n-expt x (1- n)))
    1))

;; This little theorem is pretty useful below.  I'm not sure why it
;; isn't a standard theorem of ACL2, but there's probably a subtle
;; reason involving cyclic rules....

(local
 (defthm distributivity-2
   (equal (* (+ x y) z)
	  (+ (* x z) (* y z)))))

;; Now, we're almost there.  We prove the binomial theorem, but using
;; the function n-expt instead of expt -- we told you it was easier to
;; reason about!

(defthm binomial-theorem-fake
  (implies (and (integerp n) (<= 0 n))
	   (equal (n-expt (+ x y) n)
		  (sumlist (binomial-expansion x y 0 n))))
  :hints (("Goal" :induct (n-expt x n))
	  ("Subgoal *1/1'" :in-theory (disable binomial-expansion))
	  ("Subgoal *1/1'''" :by (:instance binomial-theorem-induction-lemma))))

;; For the big step, we now show that our definition of expt really is
;; the same as expt.

(defthm n-expt-expt
  (implies (and (integerp n) (<= 0 n))
 	   (equal (expt x n)
 		  (n-expt x n))))

;; And therefore, we can now prove the binomial theorem!

(defthm binomial-theorem
  (implies (and (integerp n) (<= 0 n))
	   (equal (expt (+ x y) n)
		  (sumlist
		   (binomial-expansion x y 0 n)))))


;; Here's an added bonus.  It's not obvious that the binomial
;; expansions of (x+y)^n and (y+x)^n are the same -- it's a deep
;; consequence of the fact that (choose k n) and (choose (- n k) n)
;; are the same.  But, it's obvious if you look at just (x+y)^n
;; vs. (y+x)^n.  So, we get the fact that the binomial expansions
;; commute x&y for free!

(defthm binomial-sum-commutes
  (implies (and (integerp n) (<= 0 n))
	   (equal (sumlist (binomial-expansion x y 0 n))
		  (sumlist (binomial-expansion y x 0 n))))
  :hints (("Goal"
	   :use ((:instance binomial-theorem)
		 (:instance binomial-theorem (x y) (y x)))
	   :in-theory (disable binomial-theorem)))
  :rule-classes nil)
