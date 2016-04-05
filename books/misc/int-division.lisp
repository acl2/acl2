;  Book           int-division
;  Contributed by Matyas Sustik
;  Date created   2000-05-05
;  $Id: int-division.lisp,v 1.16 2001/09/05 19:14:10 matyas Exp $
;
;  Special thanks to Robert Bellarmine Krug and Matt Kaufmann for
;  their insight and help in simplifying the proofs.
;
;  Matt K. pointed out numerous unnecesarry hypotheses, wrongly formed
;  rewrite rules which prevented them from being used, helped to use
;  rewrite rules where I originally used forward-chaining ones.


(in-package "ACL2")
(include-book "arithmetic/equalities" :dir :system)
(include-book "arithmetic/inequalities" :dir :system)

(defun integer-quotient (a b)
  (if (and (integerp a)
	   (integerp b))
      (if (equal 0 a)
	  (if (equal 0 b)
	      1
	    nil)
	(if (integerp (/ b a))
	    (/ b a)
	  nil))
    nil))

(defthm integer-quotient-type
  (or (integerp (integer-quotient a b))
      (equal (integer-quotient a b) nil))
  :rule-classes :type-prescription)

; Should be a rewrite rule?!
(defthm integer-quotient-arg-1-type
  (implies (integerp (integer-quotient a b))
	   (equal (integerp a) t))
  :rule-classes :type-prescription)

(defthm integer-quotient-arg-2-type
  (implies (integerp (integer-quotient a b))
	   (equal (integerp b) t))
  :rule-classes :type-prescription)

(defthm integer-quotient-spec-0-0
  (equal (integer-quotient 0 0) 1))

(defthm integer-quotient-spec-a-0
  (implies (and (integerp a)
		(case-split (not (equal 0 a))))
	   (equal (integer-quotient a 0) 0)))

; Is this ever used??
(defthm integer-quotient-spec-0-b
  (implies (integerp (integer-quotient 0 b))
	   (equal 0 b))
  :rule-classes :forward-chaining)

(defthm integer-quotient-spec-a-a
  (equal (integer-quotient a a)
	 (if (integerp a)
	     1
	   nil)))

(local
 (defthm inequality-lemma-1
   (implies (and (integerp a)
		 (< 0 a)
		 (not (equal 1 a)))
	    (<= 2 a))
   :rule-classes :forward-chaining))  ; no maximal terms

(local
 (defthm inequality-lemma-2
   (implies (and (integerp a)
		 (< a 0)
		 (not (equal -1 a)))
	    (<= a -2))
   :rule-classes :forward-chaining))

(local
 (defthm inequality-lemma-3
   (implies (and (integerp (/ a))
		 (integerp a)
		 (case-split (not (equal 0 a))))
	    (or (equal 1 a)
		(equal -1 a)))
   :rule-classes :forward-chaining
   :hints (("Goal"

; Matt K. mod, April 2016: The addition of a type-set bit for the set {1}
; caused this proof to fail.  Investigation revealed that a literal was being
; rewritten to nil instead of t because the type-alist (from type-alist-clause)
; was now sufficiently strong to deduce that (/ A) = 1.  That didn't seem to me
; to indicate a need to modify heuristics, so when I found that commenting out
; the first two lemma instances below restored the proof, I decided simply to
; do that and move on.

	    :use (;inequality-lemma-1
		  ;inequality-lemma-2
		  (:instance inequality-lemma-1 (a (/ a)))
		  (:instance inequality-lemma-2 (a (/ a))))))))

(defthm integer-quotient-spec-a-1
  (implies (and (integerp (integer-quotient a 1)))
	   (or (equal 1 a)
	       (equal -1 a)))
  :rule-classes :forward-chaining)

(defthm integer-quotient-spec-1-b
  (equal (integer-quotient 1 b)
	 (if (integerp b)
	     b
	   nil)))

(defthm integer-quotient-commutes-with-+
  (implies (and	(integerp (integer-quotient a b))
		(integerp (integer-quotient a c))
		(case-split (not (equal 0 a))))
	   (equal (integer-quotient a (+ b c))
		  (+ (integer-quotient a b)
		     (integer-quotient a c)))))

(defthm integer-quotient-commutes-with-unary-minus-1
  (equal (integer-quotient a (- a))
	 (if (integerp a)
	     (if (equal 0 a)
		 1
	       (- 1))
	   nil)))

(defthm integer-quotient-commutes-with-unary-minus-2
  (equal (integer-quotient (- a) a)
	 (if (integerp a)
	     (if (equal 0 a)
		 1
	       (- 1))
	   nil)))

(local
 (defun ind-int-abs (n)
   (if (integerp n)
       (if (equal 0 n)
	   t
	 (if (< 0 n)
	     (ind-int-abs (+ -1 n))
	   (ind-int-abs (+ +1 n))))
     t)))

;; Is this used??
(defthm integer-quotient-commutes-with-*
  (implies (and	(integerp (integer-quotient a b))
		(case-split (not (equal 0 b)))
		(integerp c))
	   (equal (integer-quotient a (* b c))
		  (* (integer-quotient a b) c)))
  :hints (("Goal" :induct (ind-int-abs c))))

(in-theory (disable integer-quotient-commutes-with-*))

(defthm integer-quotient-commutes-with-*-alt
  (equal (integer-quotient a (* b c))
	 (if (and (integerp (integer-quotient a b))
		  (case-split (not (equal 0 b)))
		  (integerp c))
	     (* (integer-quotient a b) c)
	   (integer-quotient a (* b c))))
  :hints (("Goal" :induct (ind-int-abs c))))

; Is this used??
(defthm integer-quotient-*-cancellation
  (implies (and (integerp a)
		(case-split (not (equal 0 a)))
		(integerp q))
	   (equal (integer-quotient a (* a q)) q)))

(local
 (defthm crap001
   (implies (and (integerp a)
		 (integerp b)
		 (integerp c)
		 (not (equal 0 a))
		 (not (equal 0 b)))
	    (equal (* (/ b a) (/ c b))
		   (/ c a)))
   :rule-classes nil))

(local
 (defthm crap002
   (implies (and (integerp a)
		 (integerp b))
	    (integerp (* a b)))
   :rule-classes :type-prescription))

; Care must be taken when formulating the next lemma.  In order for
; ACL2 to use it automatically the first term should include the free
; variable b.  Furthermore the conclusion must have exactly (* (/ a)
; c)) and not (* c (/ a)) or (/ c a).  Note that when storing a rule
; ACL2 does not normalize the terms, therefore to have successful
; match the user has to do the work.
 (defthm crap003
   (implies (and (integerp (* (/ a) b))
		 (integerp a)
		 (integerp b)
		 (integerp c)
		 (not (equal 0 a))
		 (not (equal 0 b))
		 (integerp (/ c b)))
	    (integerp (* (/ a) c)))
   :hints (("Goal"
	    :use (crap001
		  (:instance crap002
			     (a (/ b a))
			     (b (/ c b)))))))

(defthm integer-quotient-factorization
  (implies (and (integerp a)
		(integerp b)
		(integerp c)
		(case-split (not (equal 0 a)))
		(case-split (not (equal 0 b)))
		(integerp (integer-quotient a b))
		(integerp (integer-quotient b c)))
  (equal (* (integer-quotient a b) (integer-quotient b c))
	 (integer-quotient a c))))

(defun divides (a b)
  (and (integerp a)
       (integerp b)
       (equal b (* a (integer-quotient a b)))))

; The type of divides is deduced automatically.

(defthm divides-integer-quotient-equivalence
  (equal (divides a b)
	 (and (integerp a)
	      (integerp b)
	      (integerp (integer-quotient a b))
	      (equal b (* a (integer-quotient a b))))))

(in-theory (disable divides))

(defthm divides-spec-0-0
  (divides 0 0))

(defthm divides-spec-a-0
  (implies (integerp a)
	   (divides a 0)))

(defthm divides-spec-0-b
  (implies (divides 0 b)
	   (equal 0 b))
  :rule-classes :forward-chaining)

(defthm divides-spec-a-1
  (implies (divides a 1)
	   (or (equal 1 a)
	       (equal -1 a)))
  :rule-classes :forward-chaining)

(defthm divides-spec-1-b
  (implies (integerp b)
	   (divides 1 b)))

(defthm divide-sum
  (implies (and	(divides d a)
		(divides d b))
	   (divides d (+ a b))))

; Is this needed?
(defthm divide-factor
  (implies (and (equal b (* a q))
		(integerp a)
		(integerp q))
	   (divides a b)))

; Is this used??
(defthm divides-reflexivity
  (implies (integerp a)
	   (divides a a)))

(defthm divide-product
  (implies (and	(integerp b)
		(divides d a))
	   (divides d (* a b)))
  :hints (("Goal"
	   :use ((:Instance crap002
			    (a (* a (/ d))))))))

(defthm divide-factorization
  (implies (divides a b)
	   (equal (* a (integer-quotient a b))
		  b)))

(in-theory (disable divide-factorization))

(local
 (defthm inequality-lemma-4
   (implies (and (integerp a)
		 (< 0 a)
		 (integerp q)
		 (< 0 q))
	    (<= a (* a q)))
   :rule-classes :forward-chaining))

(in-theory (disable integer-quotient))

(defthm divider-<
  (implies (and (divides a b)
		(integerp a)
		(<= 0 a)
		(integerp b)
		(< 0 b))
	   (<= a b))
  :rule-classes :forward-chaining
  :hints (("Goal"
	   :use ((:instance inequality-lemma-4
			    (q (integer-quotient a b)))))))

(in-theory (enable integer-quotient))

(defthm divide-transitivity
  (implies (and (divides a b)
		(divides b c))
	   (divides a c))
  :hints (("Goal"
	   :in-theory (enable integer-quotient)
	   :use crap003)))

(defthm equality-from-division
  (implies (and (divides a b)
		(divides b a)
		(integerp a)
		(< 0 a)
		(integerp b)
		(< 0 b))
	   (equal a b))
  :rule-classes :forward-chaining
  :hints (("Goal"
	   :in-theory (disable divider-<)
	   :use (divider-<
		 (:instance divider-<
			   (a b)
			   (b a))))))

(defthm divide-linear-combination
  (implies (and (integerp x)
		(integerp y))
	   (implies (and (divides d a)
			 (divides d b))
		    (divides d (+ (* a x) (* b y))))))

(in-theory (disable divides))
(in-theory (disable integer-quotient))
