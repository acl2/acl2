;;; This file defined the function e^x.  The idea is to define e^x
;;; using its Taylor series approximation.  In particular, we have
;;; e^x = standard_part(1+x+x^2/2! + ... +x^N/N!) where N is an
;;; i-large integer.  Before we can accept this definition, however,
;;; we must establish that 1+x+x^2/2! + ... +x^N/N! is limited for
;;; standard values of x.  To show that, we split the sum into two
;;; parts.  The sum of the first |x| elements is limited, since it is
;;; the sum of a limited number of limited numbers.  The sum of the
;;; remaining terms can be shown to be limited by using an argument
;;; similar to the proof of the ratio test.  We start by showing that
;;; geometric series converge, as long as the ratio r is less than 1.
;;; Then, we show a particular geometric sequence which is larger
;;; element by element than the x^i/i! terms.  From the comparison
;;; test, therefore, we can conclude that ths sum of the x^i/i! terms
;;; converges.  Why do we need to split the sum into two parts at all?
;;; Because the geometric series we will need is not necessarily
;;; smaller than the x^i/i! for small values of i.  Note, the argument
;;; above tacitly assumed that x was real -- in particular, we talked
;;; about terms being smaller, etc.  The development below defines e^x
;;; for all complex numbers.  The "norm" function is used to specify
;;; the ordering required.  E.g., the comparison test will require
;;; that norm(a_i) <= norm(b_i).

(in-package "ACL2")

(local (include-book "arithmetic/abs" :dir :system))
(include-book "arithmetic/sumlist" :dir :system)
(local (include-book "arithmetic/idiv" :dir :system))
(local (include-book "arithmetic/realp" :dir :system))

(include-book "nsa")
(include-book "norm")
(include-book "next-integer")
(include-book "factorial")

; Added by Matt K. for v2-7.
(add-match-free-override :once t)
(set-match-free-default :once)

;;; We begin with some simple lemmas that allow us to conclude that a
;;; given value is a number when all we know about it is that it is
;;; close to something or is standard or whatever.  These theorems are
;;; true because our "standard" test only tests whether numbers are
;;; standard.

;; This is an important lemma.  Two numbers are i-close to each other if
;; and only if their difference is i-small.

(defthm  ismall-iclose
  (implies (and (acl2-numberp x)
		(acl2-numberp y))
	   (iff (i-small (- x y))
		(i-close x y)))
  :hints (("Goal" :in-theory (enable i-close i-small))))

(in-theory (disable ismall-iclose))

;; We will be reasoning about next-integer in the future.  In fact, we
;; will be looking at terms like next-integer(next-integer(x)) --
;; i.e., next two integer.  So, we prove here that this term is
;; limited precisely when x is limited.

(local
 (defthm limited-next-integer-norm
   (implies (acl2-numberp x)
	    (equal (i-large (next-integer (norm x)))
		   (i-large x)))
   :hints (("Goal"
	    :use ((:instance large-next-integer (x (norm x))))
	    :in-theory (disable large-next-integer)))))

(local
 (defthm limited-next-integer-next-integer-norm
   (implies (acl2-numberp x)
	    (equal (i-large (next-integer (next-integer (norm x))))
		   (i-large x)))))

;;; Now we derive the theory of geometric series.

;; First, we define a recognizer for geometric sequences.  Basically,
;; a sequence is geometric if it has at least one element, it contains
;; only numbers, and for adjacent elements a_{i+1} = factor*a_i.

(defun geometric-sequence-p (seq ratio)
  (if (consp seq)
      (if (consp (cdr seq))
	  (and (acl2-numberp (car seq))
	       (equal (* (car seq) ratio)
		      (car (cdr seq)))
	       (geometric-sequence-p (cdr seq) ratio))
	(acl2-numberp (car seq)))
    nil))

;; Next, we define the function last-elem that returns the last
;; element of a sequence.  This will be used in finding a "short-cut"
;; form for the sum of the sequence.

(defun last-elem (x)
  (if (consp x)
      (if (consp (cdr x))
	  (last-elem (cdr x))
	(car x))
    nil))

;; So now we define the sum of a geometric function.

(encapsulate
 ()

 ;; ACL2 needs some very simple algebraic rules to get very far.
 ;; Unfortunately, once you start down this road, you end up having to
 ;; do a *lot* of algebra.  Here's the first rule:

 (local
  (defthm lemma-1
    (implies (acl2-numberp seq1)
	     (equal (- seq1 (* factor seq1))
		    (* (- 1 factor) seq1)))))

 ;; This allows us to prove the following simplification:

 (local
  (defthm lemma-2
    (implies (and (acl2-numberp seq1)
		  (acl2-numberp factor)
		  (not (equal factor 1)))
	     (equal (+ (* seq1 (/ (+ 1 (- factor))))
		       (- (* factor seq1
			     (/ (+ 1 (- factor))))))
		    seq1))))

 (local
  (in-theory (disable lemma-1)))

 ;; Now we have a simple simplification, cancellation of a number on
 ;; the left of an addition.

 (local
  (defthm lemma-3-1
    (implies (and (acl2-numberp x)
		  (acl2-numberp y))
	     (equal (equal x (+ x y))
		    (equal 0 y)))))

 ;; And the same theorem with x on the other side.

 (local
  (defthm lemma-3-2
    (implies (and (acl2-numberp x)
		  (acl2-numberp y))
	     (equal (equal 0 (+ (- x) y))
		    (equal x y)))))

 ;; Another similar theorem, this time with multiplication instead.

 (local
  (defthm lemma-3-3
    (implies (and (acl2-numberp x)
		  (acl2-numberp y)
		  (acl2-numberp z))
	     (equal (equal (* x y) z)
		    (if (equal x 0)
			(equal z 0)
		      (equal y (/ z x)))))))

 ;; And from the above we can arrive at an important simplification.
 ;; The term x+(f*x/(1-f)) is equal to x/(1-f).

 (local
  (defthm lemma-3
    (implies (and (acl2-numberp seq1)
		  (acl2-numberp factor)
		  (not (equal factor 1)))
	     (equal (+ seq1
		       (* factor seq1 (/ (+ 1 (- factor)))))
		    (* seq1 (/ (+ 1 (- factor))))))))

 ;; Now we restate the previous theorem, but allow an "extra" number
 ;; to be added to both sides of the equation.

 (local
  (defthm lemma-4
    (implies (and (acl2-numberp seq1)
		  (acl2-numberp factor)
		  (not (equal factor 1))
		  (acl2-numberp extra))
	     (equal (+ seq1
		       (* factor seq1 (/ (+ 1 (- factor))))
		       extra)
		    (+ (* seq1 (/ (+ 1 (- factor))))
		       extra)))))

 ;; And finally, we show that x=y/g-f*f*y/g if and only if x*g is
 ;; equal to y-f*f*y

 (local
  (defthm lemma-5
    (implies (and (acl2-numberp x)
		  (acl2-numberp seq1)
		  (acl2-numberp factor)
		  (acl2-numberp 1-factor)
		  (not (equal 1-factor 0)))
	     (equal (equal x
			   (+ (* seq1 (/ 1-factor))
			      (- (* factor factor
				    seq1 (/ 1-factor)))))
		    (equal (* x 1-factor)
			   (+ seq1
			      (- (* factor factor seq1))))))))

 ;; With all that algebra out of the way, we can prove that the sum of
 ;; a geometric sequence is equal to (r*a_n - a_1)/(1-r) where a_n is
 ;; the last element, a_1 is the first element, and r is the ratio
 ;; between successive elements.

 (defthm sumlist-geometric
   (implies (and (geometric-sequence-p seq ratio)
		 (acl2-numberp ratio)
		 (not (equal ratio 1)))
	    (equal (sumlist seq)
		   (if (consp seq)
		       (/ (- (car seq)
			     (* ratio (last-elem seq)))
			  (- 1 ratio))
		     0)))))

;; Now, we extend the result above by finding an alternate definition
;; for the last-element of a geometric sequence.  In fact, if r is the
;; ratio between adjacent elements in the sequence a_1, a_2, ..., a_n
;; then a_n = a_1*r^{n-1}.

(encapsulate
 ()

 ;; We start with a simple theorem.  The length of a list is always
 ;; non-negative.

 (local
  (defthm lemma-1
    (<= 0 (len seq))
    :rule-classes (:rewrite :linear :type-prescription)))

 ;; Moreover, if a list has at least one element, its length is at
 ;; least 1.  This is the sort of theorem that makes computers look
 ;; dumb!

 (local
  (defthm lemma-2
    (implies (consp seq)
	     (<= 1 (len seq)))
   :rule-classes (:rewrite :linear :type-prescription)))

 ;; Here's an important lemma, because it relates terms we'll see in
 ;; the induction to follow!  Basically, r^{len(L)-1} is the same as
 ;; r*r^{len(L)-1-1} = r*r^{len(cdr(L))-1}.

 (local
  (defthm lemma-3
    (implies (and (consp seq)
		  (consp (cdr seq)))
	     (equal (expt factor (+ -1 (len seq)))
		    (* factor (expt factor (+ -1 (len (cdr seq)))))))))

 ;; We seem to need this lemma often -- maybe it should be exported.
 ;; x^0=1.

 (local
  (defthm lemma-4
    (equal (expt factor 0) 1)))

 (local
  (in-theory
   (disable expt)))

 ;; Those are all the pieces we need to show that a_n = a_1*r^{n-1} in
 ;; a geometric series with factor r.

 (defthm last-geometric
   (implies (and (geometric-sequence-p seq ratio)
		 (consp seq))
	    (equal (last-elem seq)
		   (* (car seq)
		      (expt ratio (- (len seq) 1))))))
 )

;; So now, we can combine the two previous results to find an
;; expression for the sum of a sequence.

(encapsulate
 ()

 ;; Here it is again!  x^0=1.

 (local
  (defthm lemma-1
    (equal (expt factor 0) 1)))

 ;; Here is a dangerous theorem -- it goes against the definition of
 ;; x^n, by converting x*x^n into x^{n+1}.  It works though.

 (local
  (defthm x-expt-x-n
    (implies (and (integerp n) (<= 0 n))
	     (equal (* x (expt x n))
		    (expt x (1+ n))))))

 ;; And we need this lemma again! r^{len(L)-1} = r*r^{len(cdr(L))-1}.
 ;; I really should just export these above.

 (local
  (defthm lemma-2
    (implies (and (consp seq)
		  (acl2-numberp factor))
	     (equal (expt factor (len seq))
		    (* factor (expt factor (+ -1 (len seq))))))))

 (local
  (in-theory (disable x-expt-x-n expt)))

 ;; Again, the length of a list is non-negative.

 (local
  (defthm lemma-3
    (<= 0 (len seq))
    :rule-classes (:rewrite :linear :type-prescription)))

 ;; And if the list is non-empty, its length is at least 1.

 (local
  (defthm lemma-4
    (implies (consp seq)
	     (<= 1 (len seq)))
   :rule-classes (:rewrite :linear :type-prescription)))

 ;; So now, we find our final expression for the sum of a geometric
 ;; series.  It is a_1 * (1 - r^n) / (1-r).  Beautiful, isn't it?

 (defthm sumlist-geometric-useful
      (implies (and (geometric-sequence-p seq ratio)
                    (acl2-numberp (car seq))
                    (acl2-numberp ratio)
                    (not (equal ratio 1)))
               (equal (sumlist seq)
                      (* (car seq)
                         (/ (- 1 (expt ratio (len seq)))
                            (- 1 ratio))))))
 )

;; Now, we consider what happens when we add not the numbers in a
;; list, but their norm.  Here is the definition:

(defun sumlist-norm (x)
  (if (consp x)
      (+ (norm (car x))
	 (sumlist-norm (cdr x)))
    0))

;; Clearly, the sum of the norms of a sequence is always real and
;; non-negative.

(defthm sumlist-norm-positive
  (and (realp (sumlist-norm x))
       (<= 0 (sumlist-norm x)))
  :rule-classes (:rewrite :type-prescription))

;; Moreover, it can be split into parts, just like the sum of a sequence.

(defthm sumlist-norm-append
  (equal (sumlist-norm (append x y))
	 (+ (sumlist-norm x) (sumlist-norm y))))

;; An interesting theorem is that the norm of a sum is at most equal
;; to the sum of the norms!

(defthm norm-sumlist-<=-sumlist-norm
  (<= (norm (sumlist l))
      (sumlist-norm l))
  :hints (("Subgoal *1/1'"
	   :use ((:instance norm-triangle-inequality
			    (a (car l))
			    (b (sumlist (cdr l)))))
	   :in-theory (disable norm-triangle-inequality)))
  :rule-classes (:rewrite :linear))

;; And now, we find an expression for the sum of the norms of a
;; geometric sequence.

(encapsulate
 ()

 ;; The following is needed for v2-6 in order to get lemma-1 proved.
 (local (in-theory (enable exponents-add-unrestricted)))

 ;; First, we show that for a real 0<=r<1, r^n is positive and
 ;; r^n<=1.

 (local
  (defthm lemma-1
    (implies (and (realp factor)
		  (<= 0 factor)
		  (< factor 1)
		  (integerp n)
		  (<= 0 n))
	     (and (<= 0 (expt factor n))
		  (<= (expt factor n) 1)))))

 ;; Now, here's an interesting theorem.  The norm of an inverse is the
 ;; inverse of the norm.  This is a consequence of the result for
 ;; products and the fact that norm(1)=1.

 (local
  (defthm lemma-2
    (equal (norm (/ x)) (/ (norm x)))
    :hints (("Goal" :use ((:instance norm-product (a x) (b (/ x))))
	     :in-theory (disable norm-product))
	    ("Goal'" :cases ((not (acl2-numberp x)) (equal x 0))))))

 ;; And now -- with a lot of work! -- we get a nice result for the sum
 ;; of the norm of a geometric sequence, when the ratio is a real
 ;; between 0 and 1.  There should be a simpler proof of this, but I
 ;; just don't see one.

 (local
  ;; [Jared]: Awful hack to deal with awful, brittle :instructions in the proof
  ;; below.  This is a !&@(* nightmare.  I'm pretty sure a proper fix is beyond
  ;; me.  Thanks very much to Matt Kaufmann for a very useful hint toward
  ;; figuring out that this lemma was the one causing the damage.
  (in-theory (disable <-*-/-right-commuted)))

 (defthm sumlist-norm-real-geometric
   (implies (and (geometric-sequence-p seq ratio)
		 (acl2-numberp (car seq))
		 (realp ratio)
		 (<= 0 ratio)
		 (< ratio 1))
	    (equal (sumlist-norm seq)
		   (* (norm (car seq))
		      (norm (/ (- 1 (expt ratio
					  (len seq)))
			       (- 1 ratio))))))
   :INSTRUCTIONS
   #| The use of CLAIM is not allowed in v2-6, at least not in its
      development version as of 9/20/01.  So we replace the following
      by a version obtained by running the instructions after calling
      verify, (do-all <instr1> <instr2> ...), and then exit,
      (toggle-pc-macro claim), (verify), replay, and finally
      (exit sumlist-norm-real-geometric).
      Matt K., 9/20/01.
   (:INDUCT
    :PROVE
    :PROVE :PROVE :PROMOTE (:DEMOTE 5)
    (:DV 1 1)
    (:= T)
    :UP :S :TOP :PROMOTE (:DV 1)
    :X (:DV 2)
    := (:DROP 10)
    (:DV 1 1)
    := (:DROP 4)
    :UP
    (:= (* (NORM (CAR SEQ)) (NORM RATIO)))
    :UP
    (:= (* (NORM (CAR SEQ))
           (* (NORM RATIO)
              (NORM (+ (/ (+ 1 (- RATIO)))
                       (- (* (/ (+ 1 (- RATIO)))
                             (EXPT RATIO (LEN (CDR SEQ))))))))))
    (:DIVE 2)
    (:=
     (NORM (* RATIO
              (+ (/ (+ 1 (- RATIO)))
                 (- (* (/ (+ 1 (- RATIO)))
                       (EXPT RATIO (LEN (CDR SEQ)))))))))
    (:DV 1 2)
    (:= (* (+ 1 (- (EXPT RATIO (LEN (CDR SEQ)))))
           (/ (+ 1 (- RATIO)))))
    :UP
    (:= (* (+ RATIO
              (* RATIO
                 (- (EXPT RATIO (LEN (CDR SEQ))))))
           (/ (+ 1 (- RATIO)))))
    (:DV 1 2)
    :SL (:DV 1)
    (:= (EXPT RATIO (LEN SEQ)))
    :UP
    (:CLAIM (<= (EXPT RATIO (LEN SEQ)) RATIO))
    :TOP
    (:CLAIM (<= 0
                (* (+ RATIO (- (EXPT RATIO (LEN SEQ))))
                   (/ (+ 1 (- RATIO))))))
    (:DV 1 1)
    (:= (* (NORM (CAR SEQ)) (NORM 1)))
    :UP :TOP
    (:USE (:INSTANCE NORM-DISTRIBUTIVITY (A 1)
                     (B (* (+ RATIO (- (EXPT RATIO (LEN SEQ))))
                           (/ (+ 1 (- RATIO)))))
                     (X (CAR SEQ))))
    :PROMOTE (:FORWARDCHAIN 1)
    (:DV 1)
    (:= (NORM (+ (* 1 (CAR SEQ))
                 (* (* (+ RATIO (- (EXPT RATIO (LEN SEQ))))
                       (/ (+ 1 (- RATIO))))
                    (CAR SEQ)))))
    (:DV 1)
    (:= (* (CAR SEQ)
           (+ 1
              (* (+ RATIO (- (EXPT RATIO (LEN SEQ))))
                 (/ (+ 1 (- RATIO)))))))
    :UP (:REWRITE NORM-PRODUCT)
    (:DV 2 1 1)
    (:= (* (+ 1 (- RATIO))
           (/ (+ 1 (- RATIO)))))
    (:REWRITE COMMUTATIVITY-OF-*)
    :NX (:REWRITE COMMUTATIVITY-OF-*)
    :UP
    (:= (* (/ (+ 1 (- RATIO)))
           (+ (+ 1 (- RATIO))
              (+ RATIO
                 (- (EXPT RATIO (LEN SEQ)))))))
    (:DV 2)
    :S :TOP :S)
   |#
   (:INDUCT :PROVE
            :PROVE :PROVE :PROMOTE (:DEMOTE 5)
            (:DV 1 1)
            (:= T)
            :UP :S :TOP :PROMOTE (:DV 1)
            :X (:DV 2)
            := (:DROP 10)
            (:DV 1 1)
            := (:DROP 4)
            :UP
            (:= (* (NORM (CAR SEQ)) (NORM RATIO)))
            :UP
            (:= (* (NORM (CAR SEQ))
                   (* (NORM RATIO)
                      (NORM (+ (/ (+ 1 (- RATIO)))
                               (- (* (/ (+ 1 (- RATIO)))
                                     (EXPT RATIO (LEN (CDR SEQ))))))))))
            (:DIVE 2)
            (:= (NORM (* RATIO
                         (+ (/ (+ 1 (- RATIO)))
                            (- (* (/ (+ 1 (- RATIO)))
                                  (EXPT RATIO (LEN (CDR SEQ)))))))))
            (:DV 1 2)
            (:= (* (+ 1 (- (EXPT RATIO (LEN (CDR SEQ)))))
                   (/ (+ 1 (- RATIO)))))
            :UP
            (:= (* (+ RATIO
                      (* RATIO (- (EXPT RATIO (LEN (CDR SEQ))))))
                   (/ (+ 1 (- RATIO)))))
            (:DV 1 2)
            :SL (:DV 1)
            (:= (EXPT RATIO (LEN SEQ)))
            :UP
            (:CASESPLIT (<= (EXPT RATIO (LEN SEQ)) RATIO)
                        NIL NIL)
            :CHANGE-GOAL (:UP 6)
            (:CONTRAPOSE 9)
            (:DROP 9)
            :PROVE :TOP
            (:CASESPLIT (<= 0
                            (* (+ RATIO (- (EXPT RATIO (LEN SEQ))))
                               (/ (+ 1 (- RATIO)))))
                        NIL NIL)
            :CHANGE-GOAL (:CONTRAPOSE 10)
            (:DROP 10)
            :PROVE (:DV 1 1)
            (:= (* (NORM (CAR SEQ)) (NORM 1)))
            :UP :TOP
            (:USE (:INSTANCE NORM-DISTRIBUTIVITY (A 1)
                             (B (* (+ RATIO (- (EXPT RATIO (LEN SEQ))))
                                   (/ (+ 1 (- RATIO)))))
                             (X (CAR SEQ))))
            :PROMOTE (:DV 1)
            (:= (NORM (+ (* 1 (CAR SEQ))
                         (* (* (+ RATIO (- (EXPT RATIO (LEN SEQ))))
                               (/ (+ 1 (- RATIO))))
                            (CAR SEQ)))))
            (:DV 1)
            (:= (* (CAR SEQ)
                   (+ 1
                      (* (+ RATIO (- (EXPT RATIO (LEN SEQ))))
                         (/ (+ 1 (- RATIO)))))))
            :UP (:REWRITE NORM-PRODUCT)
            (:DV 2 1 1)
            (:= (* (+ 1 (- RATIO)) (/ (+ 1 (- RATIO)))))
            (:REWRITE COMMUTATIVITY-OF-*)
            :NX (:REWRITE COMMUTATIVITY-OF-*)
            :UP
            (:= (* (/ (+ 1 (- RATIO)))
                   (+ (+ 1 (- RATIO))
                      (+ RATIO (- (EXPT RATIO (LEN SEQ)))))))
            (:DV 2)
            :S :TOP :S))
 )

;;; Next, we define the Taylor approximation to e^x.

;; We start with one of the terms in the sequence, x^i/i!

(defun taylor-exp-term (x counter)
  (* (expt x counter)
     (/ (factorial counter))))

;; Now, we define a list of these terms.  Nterms has the number of
;; terms we would like to create, and counter is the index of the
;; first term.

(defun taylor-exp-list (nterms counter x)
  (if (or (zp nterms)
	  (not (integerp counter))
	  (< counter 0))
      nil
    (cons (taylor-exp-term x counter)
	  (taylor-exp-list (1- nterms)
			   (1+ counter)
			   x))))

;; We show that the sequence can be split into two parts.  Later, we
;; will choose a specific split that makes the second part smaller
;; than a geometric sequence.

(defthm taylor-exp-list-split
  (implies (and (integerp n1)
		(<= 0 n1)
		(integerp n2)
		(<= 0 n2)
		(integerp counter)
		(<= 0 counter))
	   (equal (taylor-exp-list (+ n1 n2) counter x)
		  (append (taylor-exp-list n1 counter x)
			  (taylor-exp-list n2 (+ counter n1) x)))))

;; First, we want to show that the first part of the sequence will be
;; limited.  We start by showing that x^n is limited when both x and n
;; are.

(defthm expt-limited
  (implies (and (<= 0 n)
		(i-limited n)
		(i-limited x))
	   (i-limited (expt x n))))

;; That means that x^n/n! must be limited as well, if both x and n are.

(defthm limited-taylor-exp-term
  (implies (and (<= 0 counter)
		(i-limited counter)
		(i-limited x))
	   (i-limited (taylor-exp-term x counter)))
  :hints (("Goal''"
	   :use ((:instance i-limited-times
			    (x (/ (factorial counter)))
			    (y (expt x counter))))
	   :in-theory (disable i-limited-times))))

;; And therefore the sum of the first n terms in the Taylor sequence
;; for e^x must be limited, if x and n are limited.

(defthm taylor-exp-list-limited-up-to-limited-counter
  (implies (and (i-limited nterms)
		(integerp counter)
		(i-limited counter)
		(i-limited x))
	   (i-limited (sumlist
		       (taylor-exp-list nterms
					counter
					x))))
  :hints (("Goal"
	   :in-theory (enable-disable (limited-integers-are-standard)
				      (taylor-exp-term)))))

;; Now, we define a different way of getting the x^n/n! terms.  This
;; one is based on a recurrence relation.

(defun taylor-exp-term-2 (x counter)
  (if (and (integerp counter)
	   (< 0 counter))
      (* x (/ counter) (taylor-exp-term-2 x (1- counter)))
    1))

;; We prove that both definitions give the same result.

(defthm taylor-exp-term-2-=-taylor-exp-term
  (implies (and (integerp counter)
		(<= 0 counter))
	   (equal (taylor-exp-term-2 x counter)
		  (taylor-exp-term x counter)))
  :hints (("Goal" :in-theory (enable factorial expt))))

(in-theory (disable taylor-exp-term-2-=-taylor-exp-term))

;; Now, we split a term of the form x^i/i! into two parts.  The first
;; has x^j/j! where j<=i and j<=norm(x).  The second part has the rest.

(defun taylor-exp-term-2l (x counter)
  (if (and (integerp counter)
	   (< 0 counter))
      (if (<= counter (norm x))
	  (* x (/ counter) (taylor-exp-term-2l x (1- counter)))
	(taylor-exp-term-2l x (1- counter)))
    1))
(defun taylor-exp-term-2u (x counter)
  (if (and (integerp counter)
	   (< 0 counter))
      (if (<= counter (norm x))
	  (taylor-exp-term-2u x (1- counter))
	(* x (/ counter) (taylor-exp-term-2u x (1- counter))))
    1))

;; Of course, the product of the two halves is equal to the original
;; x^i/i! term.

(defthm taylor-exp-term-2-=-taylor-exp-term-2l*2u
  (equal (taylor-exp-term-2 x counter)
	 (* (taylor-exp-term-2l x counter)
	    (taylor-exp-term-2u x counter))))

;; Now, when i and j are both bigger than x, then the "lower" product
;; is really equal to x^n/n! for all n up to norm(x).  So, it doesn't
;; matter what values i and j have (as long as they're larger than x).

(defthm taylor-exp-term-2l-large-counters-lemma
  (implies (and (integerp counter1)
		(integerp counter2)
		(<= 0 counter1)
		(<= (norm x) counter1)
		(<= counter1 counter2))
	   (equal (taylor-exp-term-2l x counter2)
		  (taylor-exp-term-2l x counter1)))
  :hints (("Subgoal *1/3"
	   :use ((:instance norm-preserves-<=-for-reals
			    (x counter1)
			    (y counter2)))
	   :in-theory (disable norm-preserves-<=-for-reals)))
  :rule-classes nil)

;; So in particular, if i is larger than norm(x) then it follows that
;; the lower sum of the first i terms is the same as the sum up to the
;; first next-integer(norm(x)) terms!

(defthm taylor-exp-term-2l-large-counters
  (implies (and (integerp counter)
		(<= 0 counter)
		(< (norm x) counter))
	   (equal (taylor-exp-term-2l x counter)
		  (taylor-exp-term-2l x (next-integer (norm x)))))
  :hints (("Goal"
	   :use ((:instance taylor-exp-term-2l-large-counters-lemma
			    (counter1 (next-integer (norm x)))
			    (counter2 counter))
		 (:instance taylor-exp-term-2l-large-counters-lemma
			    (counter1 counter)
			    (counter2 (next-integer (norm x)))))
	   :do-not-induct t)
	  )
  :rule-classes nil)

;; Now, recall that the lower sum is clearly limited up to a limited
;; counter.

(defthm taylor-exp-term-2l-limited-lemma
  (implies (and (i-limited x)
		(i-limited counter))
	   (i-limited (taylor-exp-term-2l x counter)))
  :hints (("Goal" :in-theory (enable standards-are-limited))))

;; When x is limited, even if the counter isn't, we know that the sum
;; was limited up to a limited counter (e.g., next-integer(norm(x)))
;; and that the sum for larger counters is equal to that, so it must
;; be limited, too!

(defthm taylor-exp-term-2l-limited
  (implies (i-limited x)
	   (i-limited (taylor-exp-term-2l x counter)))
  :hints (("Goal"
	   :cases ((i-limited counter))
	   :do-not-induct t)
	  ("Subgoal 2"
	   :use ((:instance taylor-exp-term-2l-large-counters)
		 (:instance taylor-exp-term-2l-limited-lemma
			    (counter (next-integer (norm x))))
		 (:instance large-if->-large
			    (x counter)
			    (y (norm x))))
	   :in-theory (disable taylor-exp-term-2l-limited-lemma
			       large-if->-large))
	  ("Subgoal 2'''"
	   :cases ((< counter 0))
	   :in-theory (enable abs))))

;; Now, we want to consider the norm of the upper sum.  We expect it
;; to be at most 1, since we're talking about the product of numbers
;; all of whom have norm<1 by definition.

;; First, though, we need to show that norm(x) is less than or equal
;; to norm(next-integer(norm(x)))

(defthm norm-next-integer-norm
  (<= (norm x)
      (norm (next-integer (norm x))))
  :hints (("Goal"
	   :use ((:instance norm-norm)
		 (:instance norm-preserves-<=-for-reals
			    (x (norm x))
			    (y (next-integer (norm x)))))
	   :in-theory (disable norm-norm norm-preserves-<=-for-reals))))

;; Here is a restatement of the important property that the norm(x) is
;; zero only when x is positive.

(defthm norm->-0
  (implies (and (acl2-numberp x)
		(not (equal x 0)))
	   (< 0 (norm x)))
  :hints (("Goal" :cases ((< 0 (norm x)) (= 0 (norm x)) (> 0 (norm x)))))
  :rule-classes (:rewrite :linear))

;; And we prove that the norm of an inverse is the inverse of the norm.

(defthm norm-1/x
  (equal (norm (/ x)) (/ (norm x)))
  :hints (("Goal" :use ((:instance norm-product (a x) (b (/ x))))
	   :in-theory (disable norm-product))
	  ("Goal'" :cases ((not (acl2-numberp x)) (equal x 0)))))

;; Now, we show that the norm of the upper sum is at most 1.

(encapsulate
 ()

 ;; We start with a simple lemma that when norm(r)<=1 and norm(x)<c,
 ;; then norm(r*x)<=norm(c).

 (local
  (defthm lemma-1
    (implies (and (integerp counter)
		  (< (norm x) counter)
		  (<= (norm r) 1))
	     (<= (* (norm x) (norm r))
		 (norm counter)))
    :instructions
    (:promote
     (:claim (<= (* (norm x) (norm r)) (norm x)))
     (:claim (<= (norm x) (norm counter))
	     :hints (("Goal" :use ((:instance norm-preserves-<=-for-reals
					      (x (norm x))
					      (y counter))))))
     :prove)))

 ;; And now we prove the basic theorem we need.

 (defthm taylor-exp-term-2u-<=-1
   (<= (norm (taylor-exp-term-2u x counter)) 1)))

;; Next, we'll prove that the upper sums are in fact small, and since
;; the lower sums are limited, that means their product itself is
;; small.  I.e., we will establish that x^n/n! is small when x is
;; limited and n is large.

;; First, we need some simple lemmas, like 0 is not i-large.

(defthm not-large-0
  (not (i-large 0))
  :hints (("Goal" :in-theory (enable i-large))))

;; Another is that if x is limited and y is large, x/y is i-small.

(defthm /-large-*-limited-is-small-1
  (implies (and (i-limited x)
		(i-large y))
	   (i-small (* x (/ y))))
  :hints (("Goal" :use ((:instance small*limited->small (x (/ y)) (y x)))
	   :in-theory (disable small*limited->small))))

;; The same theorem with x inverted.

(defthm /-large-*-limited-is-small-2
  (implies (and (i-limited y)
		(i-large x))

	   (i-small (* (/ x) y)))
  :hints (("Goal" :use ((:instance small*limited->small (x (/ x)) (y y)))
	   :in-theory (disable small*limited->small))))

;; We know that the upper sums are limited (since their norm is at
;; most 1).

(defthm taylor-exp-term-2u-limited
  (i-limited (taylor-exp-term-2u x counter))
  :hints (("Goal" :use ((:instance large-if->-large
				   (x (norm (taylor-exp-term-2u x counter)))
				   (y 1)))
	   :in-theory (enable-disable (abs) (large-if->-large)))))

;; With a little more work, we can get that the upper sums are in fact
;; small.  The way we do this is [x^n/n!] = x/n * [x^{n-1}/(n-1)!],
;; where we use [.] to indicate an upper sum.  The term x/n is small,
;; since x is limited and n large.  The second term has a norm at most
;; equal to 1, so it's limited.  And so their product is small!

(defthm taylor-exp-term-2u-small
  (implies (and (integerp counter)
		(<= 0 counter)
		(i-large counter)
		(i-limited x))
	   (i-small (taylor-exp-term-2u x counter)))
  :hints (("Goal"
	   :expand (taylor-exp-term-2u x counter)
	   :do-not-induct t)
	  ("Subgoal 2"
	   :use ((:instance small*limited->small
			    (x (* (/ counter) x))
			    (y (taylor-exp-term-2u x (+ -1 counter)))))
	   :in-theory (disable small*limited->small))
	  ("Subgoal 1"
	   :use ((:instance large-if->-large
			    (x counter)
			    (y (norm x))))
	   :in-theory (enable-disable (abs) (large-if->-large)))))

;; Repeating the argument above, only this time with the product of
;; the lower and upper sums, we get that x^n/n! is also small.  We are
;; using the new, recurrence-based definition of x^n/n!

(defthm taylor-exp-term-2-small
  (implies (and (integerp counter)
		(<= 0 counter)
		(i-large counter)
		(i-limited x))
	   (i-small (taylor-exp-term-2 x counter))))

;; And so, the original x^n/n! definition also results in a small
;; number.

(defthm taylor-exp-term-small
  (implies (and (integerp counter)
		(<= 0 counter)
		(i-large counter)
		(i-limited x))
	   (i-small (taylor-exp-term x counter)))
  :hints (("Goal" :use ((:instance taylor-exp-term-2-small))
	   :in-theory '(taylor-exp-term-2-=-taylor-exp-term))))

;;; Now we turn our attention a little to a different problem.  We
;;; show how a geometric sequence can be generated from specific
;;; values of a_1 and r.

;; Here's the definition.

(defun geometric-sequence-generator (nterms a1 ratio)
  (if (zp nterms)
      nil
    (cons a1
	  (geometric-sequence-generator (1- nterms)
					(* a1 ratio)
					ratio))))

;; We show that the resulting sequence is in fact geometric.

(encapsulate
 ()

 ;; First, if we only want a sequence of 1 element, then the result
 ;; really is a geometric sequence.

 (local
  (defthm lemma-1
    (implies (acl2-numberp x)
	     (geometric-sequence-p (geometric-sequence-generator 1 x a)
				   a))
    :hints (("Goal" :expand ((geometric-sequence-generator 1 x a))))))

 ;; Second, we show what the first term of a generated geometric
 ;; sequence looks like.

 (local
  (defthm lemma-2
    (implies (consp (geometric-sequence-generator nterms x a))
	     (equal (car (geometric-sequence-generator nterms x a)) x))))

 ;; And now, it is a simple inductive argument for ACL2 to get the
 ;; desired result.

 (defthm geometric-sequence-generator-is-geometric
   (implies (and (not (zp nterms))
		 (acl2-numberp x))
	    (geometric-sequence-p
	     (geometric-sequence-generator nterms x a)
	     a)))

 )

;; Now, we show that the sum of the norm of a geometric sequence with
;; real ratio 0<r<1 and limited starting value a_1 is also limited.
;; If the starting value a_1 is small, then the sum is also small.

(encapsulate
 ()

 ;; The following is needed for v2-6 in order to get lemma-1 proved.
 (local (in-theory (enable exponents-add-unrestricted)))

 ;; First, we show that r^n<=1 when r<1.

 (local
  (defthm lemma-1
    (implies (and (realp factor)
		  (<= 0 factor)
		  (< factor 1)
		  (integerp n)
		  (<= 0 n))
	     (<= (abs (expt factor n)) 1))
    :hints (("Goal" :in-theory (enable abs expt)))))

 ;; This implies that r^n is limited (since it's at most 1).

 (local
  (defthm lemma-2
    (implies (and (realp factor)
		  (<= 0 factor)
		  (< factor 1)
		  (integerp n)
		  (<= 0 n))
	     (i-limited (expt factor n)))
    :hints (("Goal" :use ((:instance large-if->-large
				     (x (expt factor n))
				     (y 1)))
	     :in-theory (disable large-if->-large)))))

 ;; Now, we add one more constraint on r -- it can't be close to 1.
 ;; For these values of r (0<r<1 and r not close to 1) we know that
 ;; 1/(1-r) is limited.

 (local
  (defthm lemma-3
    (implies (and (realp factor)
		  (<= 0 factor)
		  (< factor 1)
		  (not (i-close 1 factor)))
	     (i-limited (/ (- 1 factor))))
    :hints (("Goal" :in-theory (enable i-close i-small i-large)))))

 ;; And so we can show that the sumlist-norm of such a geometric
 ;; sequence is limited when its first argument is limited....

 (defthm sumlist-norm-geometric-sequence-limited
   (implies (and (geometric-sequence-p seq factor)
		 (acl2-numberp (car seq))
		 (i-limited (car seq))
		 (realp factor)
		 (<= 0 factor)
		 (< factor 1)
		 (not (i-close 1 factor)))
	    (i-limited (sumlist-norm seq))))

 ;; ...and it's small when its first argument is small.

 (defthm sumlist-norm-geometric-sequence-small
   (implies (and (geometric-sequence-p seq factor)
		 (acl2-numberp (car seq))
		 (i-small (car seq))
		 (realp factor)
		 (<= 0 factor)
		 (< factor 1)
		 (not (i-close 1 factor)))
	    (i-small (sumlist-norm seq))))
 )

;; Next, we define an ordering relation on sequences.  Basically the
;; sequence {a_n} <= {b_n} if and only if norm(a_i)<=norm(b_i) for all
;; i in the sequence.

(defun seq-norm-<= (x y)
  (if (consp x)
      (and (consp y)
	   (<= (norm (car x)) (norm (car y)))
	   (seq-norm-<= (cdr x) (cdr y)))
    t))

;; So it follows immediately that if {a_n} <= {b_n} the sum of the
;; norms of {a_n} is at most equal to the sumlist-norm of the {b_n}.

(defthm seq-norm-<=-sumlist-norm
  (implies (seq-norm-<= x y)
	   (<= (sumlist-norm x)
	       (sumlist-norm y))))

;; The following is an important theorem!  The comparison test allows
;; us to decide that {a_n} is convergent (i.e., its sum is limited)
;; when {b_n} converges and {a_n} <= {b_n}.

(defthm comparison-test
  (implies (and (seq-norm-<= x y)
		(i-limited (sumlist-norm y)))
	   (i-limited (sumlist-norm x))))

;; A similar theorem lets us conclude that the sum of {a_n} is small.

(defthm comparison-test-small
  (implies (and (seq-norm-<= x y)
		(i-small (sumlist-norm y)))
	   (i-small (sumlist-norm x))))

;; Now, we write an expression for the first element of the remainder
;; of a Taylor approximation for e^x.

(local
 (defthm car-taylor-exp-list
  (implies (and (integerp nterms)
		(<= 2 nterms)
		(integerp counter)
		(<= 0 counter))
	   (equal (car (taylor-exp-list (- nterms 1)
					(+ counter 1)
					x))
		  (* (car (taylor-exp-list nterms counter x))
		     (/ x (+ 1 counter)))))
  :INSTRUCTIONS
  #| See the comment above about v2-6; this change is simllar to the one there.
  (:PROMOTE (:DV 1)
	    (:DV 1)
	    :X (:DV 1)
	    (:= T)
	    :UP :UP :S :NX
	    :TOP (:CASESPLIT (NOT (ACL2-NUMBERP X)))
	    :PROVE :S (:CASESPLIT (= 0 X))
	    :S :S (:DV 1)
	    (:DV 2)
	    (:DV 1)
	    :X :UP :S :TOP (:DV 1)
	    (:DV 1)
	    :X-DUMB
	    (:= (* (+ 1 COUNTER) (FACTORIAL COUNTER)))
	    :UP
	    :TOP (:GENERALIZE ((+ 1 COUNTER) C1))
	    :PROVE)
  |#
  (:PROMOTE (:DV 1)
            (:DV 1)
            :X (:DV 1)
            :UP :UP :S :NX
            :TOP (:CASESPLIT (NOT (ACL2-NUMBERP X)))
            :PROVE :S (:CASESPLIT (= 0 X))
            :S :S (:DV 1)
            (:DV 2)
            (:DV 1)
            :X :UP :S :TOP (:DV 1)
            (:DV 1)
            :X-DUMB
            (:= (* (+ 1 COUNTER) (FACTORIAL COUNTER)))
            :UP
            :TOP (:GENERALIZE ((+ 1 COUNTER) C1))
            :PROVE)))

;; This justifies an alternate definition for the Taylor expansion,
;; using a recurrence relation.

(defun taylor-exp-list-2 (nterms prev i x)
  (if (or (zp nterms)
	  (not (integerp i))
	  (< i 0))
      nil
    (cons prev
	  (taylor-exp-list-2 (1- nterms)
			     (* prev (/ x (+ 1 i)))
			     (+ 1 i)
			     x))))

;; We will find terms of the form 1/(n+1)! so we tell ACL2 to convert
;; those into 1/n! * 1/(1+n).

(defthm /-factorial-1+n
  (implies (and (integerp n)
		(<= 0 n))
	   (equal (/ (factorial (+ 1 n)))
		  (* (/ (factorial n))
		     (/ (+ 1 n)))))
  :hints (("Goal" :cases ((= n 0) (= n 1) (< 1 n)))
	  ("Subgoal 1" :expand ((factorial (+ 1 n)))
	   :in-theory (disable distributivity))))

;; Now, we will prove that our new definition of the Taylor sin list
;; is equal to the old definition.

(encapsulate
 ()

 ;; First, we show ACL2 how to compute a list of one element using the
 ;; old definition.

 (local
  (defthm lemma-1
    (equal (taylor-exp-list 1 counter x)
	   (if (and (integerp counter)
		    (<= 0 counter))
	       (cons (* (expt x counter)
			(/ (factorial counter)))
		     nil)
	     nil))
    :hints (("Goal" :expand (taylor-exp-list 1 counter x)))))

 ;; Then, we take that same one-element list, but compute it using the
 ;; new definition.

 (local
  (defthm lemma-2
    (equal (taylor-exp-list-2 1 prev counter x)
	   (if (and (integerp counter)
		    (<= 0 counter))
	       (cons prev nil)
	     nil))
    :hints (("Goal" :expand (taylor-exp-list-2 1 prev counter x)))))

 ;; Next -- with a lot of sad work -- ACL2 can establish that the two
 ;; definitions are equal.

 (defthm taylor-exp-list-2-=-taylor-exp-list
   (equal (taylor-exp-list-2 nterms
			     (car (taylor-exp-list nterms counter x))
			     counter x)
	  (taylor-exp-list nterms counter x))

; Modified April 2016 by Matt K. after the addition of a type-set bit for {1},
; however without confirming that this was the cause of the failure.
; Originally 32 :INSTRUCTIONS were provided, instead of :HINTS, so it isn't
; surprising that heuristic changes to ACL2 caused a problem.

   :hints (("Goal" :induct t :do-not '(generalize))
           ("Subgoal *1/2" :cases ((= NTERMS 1))))))

(in-theory (disable taylor-exp-list-2-=-taylor-exp-list))

;; Now we prove a major lemma.  The Taylor expansion for sine is
;; bounded above by a geometric series!

(encapsulate
 ()

 ;; First, some silly algebra results.

 (local
  (defthm lemma-1
    (implies (and (<= x y)
		  (realp x)
		  (realp y)
		  (realp z)
		  (<= 0 z))
	     (<= (* z x)
		 (* z y)))))

 ;; Another simple algebra result.

 (local
  (defthm subgoal-*1/5-lemma
    (implies (and (realp counter)
		  (<= 1 counter))
	     (<= (norm (/ (+ 1 counter)))
		 (norm (/ counter))))
    :hints (("Goal" :use ((:instance norm-preserves-<=-for-reals
				     (x (/ (+ 1 counter)))
				     (y (/ counter))))
	     :in-theory (disable norm-preserves-<=-for-reals)))))

 ;; And here is a *trivial* consequence.  if norm(x)*norm(1/(1+c)) <=
 ;; norm(f), then norm(x)*norm(1/(2+c)) <= norm(f).  Trivial to you
 ;; and me, but not so trivial to ACL2 ;^)

 (local
  (defthm subgoal-*1/5
    (implies (and (integerp counter)
		  (<= 0 counter)
		  (<= (* (norm x) (norm (/ (+ 1 counter))))
		      (norm factor)))
	     (<= (* (norm x) (norm (/ (+ 1 1 counter))))
		 (norm factor)))
    :hints (("Goal"
	     :use ((:instance subgoal-*1/5-lemma
			      (counter (+ 1 counter)))
		   (:instance lemma-1
			      (x (norm (/ (+ 1 1 counter))))
			      (y (norm (/ (+ 1 counter))))
			      (z (norm x))))
	     :in-theory '(norm-non-negative-real) ))))


 ;; Now, we simply allow both sides of a <= to be multiplied by a
 ;; (norm prev) trem.

 (local
  (defthm subgoal-*1/2-lemma
    (implies (<= (* (norm (/ (+ 1 counter))) (norm x)) (norm factor))
	     (<= (* (norm prev) (norm x) (norm (/ (+ 1 counter))))
		 (* (norm prev) (norm factor))))
    :hints (("Goal" :use ((:instance lemma-1
				     (x (* (norm (/ (+ 1 counter))) (norm x)))
				     (y (norm factor))
				     (z (norm prev))))
	     :in-theory (disable lemma-1)))))

 ;; Actually, this lemma is probably not needed anymore.  It says that
 ;; norm(p*x*1/(1+c)) <= norm(p)*norm(x)*norm(1/(1+c)) -- but with the
 ;; theorem norm-product, we know those are in fact equal.  This could
 ;; be a hold-over from an old (weaker) norm axiomatization.

 (local
  (defthm subgoal-*1/2-lemma-2
    (<= (norm (* prev x (/ (+ 1 counter))))
	(* (norm prev) (norm x) (norm (/ (+ 1 counter)))))
    :hints (("Goal" :use ((:instance norm-product
				      (a prev)
				      (b (* x (/ (+ 1 counter)))))
			   (:instance norm-product
				      (a x)
				      (b (/ (+ 1 counter))))
			   (:instance lemma-1
				      (z (norm prev))
				      (x (norm (* x (/ (+ 1 counter)))))
				      (y (* (norm x) (norm (/ (+ 1 counter)))))))
	     :in-theory '(norm-non-negative-real)))
	     :rule-classes (:linear :rewrite)))

 ;; Now, if norm(p)<=norm(y) and norm(x)*norm(1/(1+c)) <= norm(f), we
 ;; conclude that norm(p*x/(1+c)) <= norm(y*f).

 (local
  (defthm subgoal-*1/2
    (implies (and (<= (* (norm x) (norm (/ (+ 1 counter)))) (norm factor))
		  (<= (norm prev) (norm y))
		  (realp factor))
	     (<= (norm (* prev x (/ (+ 1 counter))))
		 (norm (* y factor))))
    :hints (("Goal"
	     :use ((:instance subgoal-*1/2-lemma)
		   (:instance subgoal-*1/2-lemma-2)
		   (:instance lemma-1
			      (z (norm factor))
			      (x (norm prev))
			      (y (norm y))))
	     :in-theory '(norm-non-negative-real
			  norm-product
			  commutativity-of-*)))))

 (local (in-theory (disable norm-1/x)))

 ;; And that allows us to show that the Taylor expansion of e^x is
 ;; bounded above by a geometric sequence.

 (defthm taylor-exp-list-2-seq-<=geom-sequence-generator
   (implies (and (<= (norm prev) (norm a1))
		 (integerp i)
		 (<= 0 i)
		 (realp ratio)
		 (<= (norm (/ x (+ 1 i))) (norm ratio)))
	    (seq-norm-<= (taylor-exp-list-2 nterms
					    prev
					    i
					    x)
			 (geometric-sequence-generator
			  nterms
			  a1
			  ratio)))
   :hints (("Subgoal *1/5"
	    :by (:instance subgoal-*1/5
			   (counter i)
			   (factor ratio)))
	   ("Subgoal *1/2"
	    :by (:instance subgoal-*1/2
			   (y a1)
			   (factor ratio)))))
 )

;; Now we will show that the geometric sequence we generate from a
;; Taylor expansion is limited.  First, we prove a simple expansion
;; rule that lets ACL2 take the car of a geometric sequence term.

(local
 (defthm car-geometric-sequence-generator
   (equal (car (geometric-sequence-generator nterms x factor))
	  (if (zp nterms)
	      nil
	    x))
   :hints (("Subgoal *1/3''"
	    :expand ((geometric-sequence-generator 1 x factor))))))

;; And now, we can prove that as long as we choose a limited a_1
;; and a positive real ratio 0<r<<1 (where x<<y means x<y and x and y
;; are not close), we end up with a limited sumlist-norm.

(defthm limited-geometric-sequence-generator
  (implies (and (not (zp nterms))
		(acl2-numberp x)
		(i-limited x)
		(realp a)
		(<= 0 a)
		(< a 1)
		(not (i-close 1 a)))
	   (i-limited (sumlist-norm (geometric-sequence-generator nterms x a))))
  :hints (("Goal"
	   :use ((:instance sumlist-norm-geometric-sequence-limited
			    (seq (geometric-sequence-generator nterms x a))
			    (factor a))))))

;; Similarly, if a_1 is small, we end up with a small sumlist-norm.

(defthm small-geometric-sequence-generator
  (implies (and (not (zp nterms))
		(acl2-numberp x)
		(i-small x)
		(realp a)
		(<= 0 a)
		(< a 1)
		(not (i-close 1 a)))
	   (i-small (sumlist-norm (geometric-sequence-generator nterms x a))))
  :hints (("Goal"
	   :use ((:instance sumlist-norm-geometric-sequence-small
			    (seq (geometric-sequence-generator nterms x a))
			    (factor a))))))


;; Now, if a sumlist-norm is limited, so is the sumlist!

(defthm limited-sumlist-if-limited-sumlist-norm
  (implies (i-limited (sumlist-norm x))
	   (i-limited (sumlist x)))
  :hints (("Goal"
	   :use ((:instance large-if->-large
			    (x (norm (sumlist x)))
			    (y (sumlist-norm x))))
	   :in-theory (disable large-if->-large))))

;; Likewise, if a sumlist-norm is mall, so is the sumlist!

(defthm small-sumlist-if-small-sumlist-norm
  (implies (i-small (sumlist-norm x))
	   (i-small (sumlist x)))
  :hints (("Goal"
	   :use ((:instance small-if-<-small
			    (x (sumlist-norm x))
			    (y (norm (sumlist x)))))
	   :in-theory (disable small-if-<-small))))

;; So now, we can prove that the sum of the second half of the Taylor
;; sine sequence must be limited -- and it's small if x is small.

(encapsulate
 ()

 ;; First, some simple algebraic rules concerning
 ;; norm(x)/next-integer(norm(x)) -- this must be real, non-negative,
 ;; and less than 1.

 (local
  (defthm lemma-1
    (and (realp (/ (norm x) (next-integer (norm x))))
	 (<= 0 (/ (norm x) (next-integer (norm x))))
	 (< (/ (norm x) (next-integer (norm x))) 1))))

 ;; Since next-integer(next-integer(norm x)) > norm(x)+1, the
 ;; following lemma holds.

 (local
  (defthm lemma-2
    (< (/ (next-integer (next-integer (norm x))))
       (- 1
	  (/ (norm x)
	     (next-integer (next-integer (norm x))))))))

 ;; Moreover, if x is limited, so is next-integer(next-integer(norm x))
 ;; and so the inverse of that term is not small.

 (local
  (defthm lemma-5
    (implies (i-limited x)
	     (not (i-small (/ (next-integer (next-integer (norm x)))))))
    :hints (("Goal" :use ((:instance i-small-udivide
				     (x (/ (next-integer (next-integer (norm x)))))))
	     :in-theory (disable i-small-udivide)))))

 ;; From the previous two theorems, it follows that
 ;; 1-norm(x)/next-integer(next-integer(norm(x)) is not small -- this
 ;; means that norm(x)/next-integer(next-integer(norm(x)) can be used
 ;; as a ratio for our geometric sequence (since it is non-negative,
 ;; obviously less than 1, and not close to 1.)

 (local
  (defthm lemma-6
    (implies (i-limited x)
	     (not (i-small (- 1
			      (/ (norm x)
				 (next-integer (next-integer (norm x))))))))
    :hints (("Goal" :use ((:instance lemma-2)
			  (:instance lemma-5)
			  (:instance small-if-<-small
				     (x (- 1
					   (/ (norm x)
					      (next-integer (next-integer (norm x))))))
				     (y (/ (next-integer (next-integer (norm x)))))))
	     :in-theory (disable lemma-2 lemma-5 small-if-<-small)))))

 ;; To make it official, we now use i-close(1,r) instead of i-small(1-r)

 (local
  (defthm lemma-8
    (implies (i-limited x)
	     (not (i-close 1
			   (/ (norm x)
			      (next-integer (next-integer (norm x)))))))
    :hints (("Goal" :use ((:instance lemma-6)
			  (:instance ismall-iclose
				     (x 1)
				     (y (/ (norm x)
					   (next-integer (next-integer (norm x)))))))
	     :in-theory nil))))

 ;; And so now, we have all the pieces we need to prove that the sum
 ;; of the norms of a Taylor expansion is limited -- as lont as we
 ;; start the sum far enough out.  Note, we're still using the
 ;; recurrence-based definition of the Taylor expansion.

 (defthm limited-sumlist-norm-taylor-exp-2
   (implies (and (not (zp nterms))
		 (integerp counter)
		 (<= 0 counter)
		 (i-limited counter)
		 (i-limited prev)
		 (i-limited x)
		 (<= (next-integer (norm x)) counter))
	    (i-limited (sumlist-norm (taylor-exp-list-2 nterms
							prev
							counter
							x))))
   :hints (("Goal"
	    :use ((:instance comparison-test
			     (x (taylor-exp-list-2 nterms
						   prev
						   counter
						   x))
			     (y (geometric-sequence-generator nterms
							      prev
							      (/ (norm x)
								 (next-integer
								  (next-integer
								   (norm x))))
							      )))
		  (:instance taylor-exp-list-2-seq-<=geom-sequence-generator
			     (a1 prev)
			     (i counter)
			     (ratio (/ (norm x)
				       (next-integer
					(next-integer
					 (norm x)))))))
	    :in-theory (disable comparison-test
				taylor-exp-list-2-seq-<=geom-sequence-generator)
	    :do-not-induct t)))

 ;; Now, we try to convert the proof to the first definition of the
 ;; Taylor sequence.  First, we get a term for the first element of
 ;; such a sequence.

 (local
  (defthm lemma-10
    (equal (car (taylor-exp-list nterms counter x))
	   (if (or (zp nterms)
		   (not (integerp counter))
		   (< counter 0))
	       nil
	     (taylor-exp-term x counter)))
    :hints (("Goal"
	     :expand ((taylor-exp-list nterms counter X))))))

 ;; Now, we show that this term is a limited number.

 (local
  (defthm lemma-11
    (implies (and (integerp nterms)
		  (< 0 nterms)
		  (integerp counter)
		  (<= 0 counter)
		  (i-limited x)
		  (i-limited counter)
		  (<= 0 counter))
	     (and (acl2-numberp (car (taylor-exp-list nterms counter x)))
		  (i-limited (car (taylor-exp-list nterms counter x)))))
    :hints (("Goal"
	     :in-theory (disable taylor-exp-term)))
    ))

 (local (in-theory (disable taylor-exp-list
			    limited-sumlist-norm-taylor-exp-2)))

 ;; Now we can prove the desired theorem, adding some extra hypothesis
 ;; to allow the theorem prover to use some of the rules above.

 (local
  (defthm taylor-exp-list-limited-after-counter-bigger-than-x-lemma
    (implies (and (not (zp nterms))
		  (integerp counter)
		  (<= 0 counter)
		  (i-limited counter)
		  (i-limited x)
		  (<= (next-integer (norm x)) counter))
	     (i-limited (sumlist-norm (taylor-exp-list nterms counter x))))
    :hints (("Goal"
	     :use ((:instance limited-sumlist-norm-taylor-exp-2
			      (prev (car (taylor-exp-list nterms counter x)))))
	     :in-theory (enable taylor-exp-list-2-=-taylor-exp-list)))))

 ;; By case analysis, those extra rules are unnecessary, so we get a
 ;; nice statement of the theorem!

 (defthm taylor-exp-list-limited-norm-after-counter-bigger-than-x
   (implies (and (i-limited counter)
		 (i-limited x)
		 (<= (next-integer (norm x)) counter))
	    (i-limited (sumlist-norm (taylor-exp-list nterms counter x))))
   :hints (("Goal"
	    :cases ((and (not (zp nterms))
			 (integerp counter)
			 (<= 0 counter))))
	   ("Subgoal 2"
	    :expand ((taylor-exp-list nterms counter x)))))

 ;; This implies in particular that the sum of the elements of the
 ;; Taylor sequence is limited.

 (defthm taylor-exp-list-limited-after-counter-bigger-than-x
   (implies (and (i-limited counter)
		 (i-limited x)
		 (<= (next-integer (norm x)) counter))
	    (i-limited (sumlist (taylor-exp-list nterms counter x)))))

 ;; Next, we'll show that the term is small for a small x.  We start
 ;; with the result for the geometric sequence that is generated.

 (local
  (defthm lemma-12
    (implies (and (not (zp nterms))
		  (i-small prev)
		  (i-limited x))
	     (i-small (sumlist
		       (geometric-sequence-generator nterms
						     prev
						     (/ (norm x)
							(next-integer (next-integer (norm x))))))))
    :hints (("Goal"
	     :use ((:instance sumlist-norm-geometric-sequence-small
			      (seq (geometric-sequence-generator nterms
								 prev
								 (/ (norm x)
								    (next-integer (next-integer (norm x))))))
			      (factor (/ (norm x)
					 (next-integer (next-integer (norm x)))))))
	     :in-theory (disable sumlist-norm-geometric-sequence-small)))))

 ;; That lemma allows us to conclude that the sumlist-norm of the
 ;; Taylor sin list is small, using the second definition of the
 ;; Taylor expansion.

 (defthm small-sumlist-norm-taylor-exp-2
   (implies (and (not (zp nterms))
		 (integerp counter)
		 (<= 0 counter)
		 (i-small prev)
		 (i-limited x)
		 (<= (next-integer (norm x)) counter))
	    (i-small (sumlist-norm (taylor-exp-list-2 nterms
						      prev
						      counter
						      x))))
   :hints (("Goal"
	    :use ((:instance comparison-test-small
			     (x (taylor-exp-list-2 nterms
						   prev
						   counter
						   x))
			     (y (geometric-sequence-generator nterms
							      prev
							      (/ (norm x)
								 (next-integer
								  (next-integer
								   (norm x))))
							      )))
		  (:instance taylor-exp-list-2-seq-<=geom-sequence-generator
			     (a1 prev)
			     (i counter)
			     (ratio (/ (norm x)
				       (next-integer
					(next-integer
					 (norm x)))))))
	    :in-theory (disable comparison-test-small
				taylor-exp-list-2-seq-<=geom-sequence-generator)
	    :do-not-induct t)))

 ;; To convert this result to the first definition of Taylor sign, we
 ;; proceed as before.  First, the first element of the Taylor
 ;; expansion must be small.

 (local
  (defthm lemma-13
    (implies (and (integerp nterms)
		  (< 0 nterms)
		  (integerp counter)
		  (<= 0 counter)
		  (i-limited x)
		  (i-large counter)
		  (<= 0 counter))
	     (and (acl2-numberp (car (taylor-exp-list nterms counter x)))
		  (i-small (car (taylor-exp-list nterms counter x)))))
    :hints (("Goal" :in-theory (disable taylor-exp-term)))))

 ;; Second, the actual definition of the Taylor term is small -- this
 ;; is needed if the rewriter decides to open up the definition.

 (local
  (defthm taylor-exp-term-small-corollary
    (implies (and (integerp counter)
		  (<= 0 counter)
		  (i-large counter)
		  (i-limited x))
	     (i-small (* (/ (factorial counter))
			 (expt x counter))))
    :hints (("Goal"
	     :use ((:instance taylor-exp-term-small))
	     :in-theory (disable taylor-exp-term-small)))))

 ;; Next, a simple lemma that if counter is large and x limited, then
 ;; next-integer(norm(x)) <= counter (since the first expression is
 ;; limited and the second large.

 (local
  (defthm lemma-14
    (implies (and (realp counter)
		  (<= 0 counter)
		  (i-large counter)
		  (i-limited x))
	     (<= (next-integer (norm x)) counter))
    :hints (("Goal"
	     :use ((:instance large->-non-large
			      (x counter)
			      (y (next-integer (norm x)))))
	     :in-theory (enable-disable (abs) (large->-non-large))))))

 ;; And so we can prove that the second part of the sumlist-norm of
 ;; the Taylor expansion of e^x is small for small values of x.

 (defthm taylor-exp-list-norm-small-for-large-counter
   (implies (and (not (zp nterms))
		 (integerp counter)
		 (<= 0 counter)
		 (i-large counter)
		 (i-limited x))
	    (i-small (sumlist-norm (taylor-exp-list nterms counter x))))
   :hints (("Goal"
	    :use ((:instance small-sumlist-norm-taylor-exp-2
			     (prev (car (taylor-exp-list nterms counter x)))))
	    :in-theory (enable-disable
			(taylor-exp-list-2-=-taylor-exp-list)
			(small-sumlist-norm-taylor-exp-2
			 taylor-exp-list)))))

 ;; And similarly, the result holds for the sum of the Taylor
 ;; expansion.

 (defthm taylor-exp-list-small-for-large-counter
   (implies (and (not (zp nterms))
		 (integerp counter)
		 (<= 0 counter)
		 (i-large counter)
		 (i-limited x))
	    (i-small (sumlist (taylor-exp-list nterms counter x)))))

 )

;; So now, we try to prove that the entire Taylor expansion of e^x is
;; limited.

(encapsulate
 ()

 ;; First of all, i-large-integer is large, so it is > than
 ;; next-integer(norm(x)) for limited x.

 (local
  (defthm next-integer-norm-<-i-large-integer
    (implies (i-limited x)
	     (not (< (i-large-integer)
		     (next-integer (norm x)))))
    :hints (("Goal"
	     :use ((:instance large->-non-large
			      (x (i-large-integer))
			      (y (next-integer (norm x)))))
	     :in-theory (disable large->-non-large)))
    :rule-classes (:rewrite :linear)))

 ;; Moreover, if x is large, so is 1+x.

 (local
  (defthm not-limited-1+large
    (implies (and (i-large x)
		  (realp x))
	     (i-large (+ 1 x)))
    :hints (("Goal"
	     :use ((:instance large-if->-large
			      (x x)
			      (y (+ 1 x))))
	     :in-theory (disable large-if->-large)))))

 ;; In particular, 1+i-large-integer is NOT limited.

 (local
  (defthm not-limited-1+large-integer
    (i-large (+ 1 (i-large-integer)))
    :hints (("Goal" :use ((:instance not-limited-1+large
				     (x (i-large-integer))))
	     :in-theory (disable not-limited-1+large)))))

 ;; And neither is i-large-integer-2

 (local
  (defthm large-large-integer---2
    (i-large (- (i-large-integer) 2))))

 ;; Which means, of course, that 2 < i-large-integer.

 (local
  (defthm 2-<-large-integer
    (< 2 (i-large-integer))
    :hints (("Goal"
	     :use ((:instance large->-non-large
			      (x (i-large-integer))
			      (y 2)))
	     :in-theory (disable large->-non-large)))
    :rule-classes (:linear :rewrite)))

 ;; In fact, i-large-integer-2 is a positive and large.

 (local
  (defthm positive-large-integer---2
    (< 0 (- (i-large-integer) 2))))

 ;; And that means |i-large-integer-2| = i-large-integer-2.

 (local
  (defthm abs-large-integer---2
    (equal (abs (+ (i-large-integer) -2))
	   (+ (i-large-integer) -2))
    :hints (("Goal" :in-theory (enable abs)))))

 ;; If the next-integer(x) == i-large-integer, then we can conlude
 ;; that x is large (in fact, it's equal to i-large-integer - 1).

 (local
  (defthm large-next-integer-large-integer
    (implies (and (realp x)
		  (<= 0 x)
		  (equal (next-integer x)
			 (i-large-integer)))
	     (i-large x))
    :hints (("Goal"
	     :use ((:instance large-if->-large
			      (x (- (i-large-integer) 2))
			      (y x)))
	     :in-theory (disable large-if->-large)))))

 ;; From that, if next-integer(norm(x)) = i-large-integer, x is large.

 (local
  (defthm large-next-integer-norm-large-integer
    (implies (and (acl2-numberp x)
		  (equal (next-integer (norm x))
			 (i-large-integer)))
	     (i-large x))
    :hints (("Goal"
	     :use ((:instance large-next-integer-large-integer
			      (x (norm x))))
	     :in-theory (disable large-next-integer-large-integer)))))

 ;; The same theorem, but using (not (limited ...)) instead of (large ...)

 (local
  (defthm not-limited-next-integer-norm-large-integer
    (implies (and (acl2-numberp x)
		  (equal (next-integer (norm x))
			 (i-large-integer)))
	     (i-large x))
    :hints (("Goal"
	     :use ((:instance large-next-integer-norm-large-integer))
	     :in-theory (disable large-next-integer-norm-large-integer)))))

 ;; Now if x is limited, next-integer(next-intger(x)) < i-large-integer!

 (local
  (defthm next-integer-next-integer-norm-<-i-large-integer
    (implies (i-limited x)
	     (not (< (i-large-integer)
		     (next-integer (next-integer (norm x))))))
    :hints (("Goal"
	     :use ((:instance large->-non-large
			      (x (i-large-integer))
			      (y (next-integer (next-integer (norm x))))))
	     :in-theory (disable large->-non-large)))
    :rule-classes (:rewrite :linear)))

 ;; Now we show how we'll split a Taylor sequence into a lower half
 ;; and an upper half.  The lower half has the first
 ;; next-integer(next-integer(norm(x))) terms, and the upper half has
 ;; the rest.

 (defthm taylor-exp-list-split-for-limited
   (implies (and (i-limited x)
		 (integerp counter)
		 (<= 0 counter))
	    (equal (taylor-exp-list (i-large-integer)
				    counter
				    x)
		   (append (taylor-exp-list
			    (next-integer
			     (next-integer (norm x)))
			    counter
			    x)
			   (taylor-exp-list
			    (- (i-large-integer)
			       (next-integer
				(next-integer (norm x))))
			    (+ counter
			       (next-integer
				(next-integer (norm x))))
			    x))))
   :hints (("Goal"
	    :use ((:instance taylor-exp-list-split
			     (n1 (next-integer (next-integer (norm x))))
			     (n2 (- (i-large-integer)
				    (next-integer (next-integer (norm x)))))))
	    :in-theory (disable taylor-exp-list-split))))

 ;; Therefore, we can conclude that the Taylor sumlist is limited.

 (defthm taylor-exp-list-limited
   (implies (i-limited x)
	    (i-limited
	     (sumlist
	      (taylor-exp-list (i-large-integer) 0 x)))))

 ;; Moreover, the sumlist-norm is limited up to a limited counter.

 (defthm taylor-exp-list-norm-limited-up-to-limited-counter
   (implies (and (i-limited nterms)
		 (integerp counter)
		 (i-limited counter)
		 (i-limited x))
	    (i-limited (sumlist-norm (taylor-exp-list nterms counter x))))
   :hints (("Goal" :in-theory (enable limited-integers-are-standard)))
   )

 ;; And so the Taylor sumlist-norm is also limited.

 (defthm taylor-exp-list-norm-limited
   (implies (i-limited x)
	    (i-limited
	     (sumlist-norm
	      (taylor-exp-list (i-large-integer) 0 x)))))

 )

(in-theory (disable taylor-exp-list-split-for-limited))

;; Since the Taylor sine list is limited, we can finally define the
;; function e^x -- it is simply the standard part of an i-large Taylor
;; expansion.

(defun-std acl2-exp (x)
  (standard-part
   (sumlist (taylor-exp-list (i-large-integer) 0 (fix x)))))

;; But do we *really* have the e^x function?  Suppose we choose a
;; different i-large number instead of i-large-integer?  To see that
;; it doesn't matter, we prove the following lemma -- the Taylor
;; partial norm sums S_M and S_N are close when M is large and N>M.

(local
 (defthm exp-convergent-norm-lemma
   (implies (and (i-limited x)
		 (integerp nterms1)
		 (<= 0 nterms1)
		 (i-large nterms1)
		 (integerp num)
		 (< 0 num))
	    (i-close (sumlist-norm (taylor-exp-list nterms1 0 x))
		     (sumlist-norm (taylor-exp-list (+ nterms1 num) 0 x))))
   :hints (("Goal" :do-not-induct t
	    :in-theory (enable i-close)))))

;; So in particular, when M is large, its partial sum is equal to that
;; of the i-large-integer partial sum.

(defthm exp-convergent-norm-lemma-2
  (implies (and (i-limited x)
		(integerp nterms1)
		(<= 0 nterms1)
		(i-large nterms1))
	   (i-close (sumlist-norm (taylor-exp-list nterms1 0 x))
		    (sumlist-norm (taylor-exp-list (i-large-integer) 0 x))))
  :hints (("Goal" :do-not-induct t
	   :cases ((< nterms1 (i-large-integer))
		   (= nterms1 (i-large-integer))
		   (< (i-large-integer) nterms1)))
	  ("Subgoal 3"
	   :use ((:instance exp-convergent-norm-lemma
			    (num (- (i-large-integer) nterms1))))
	   :in-theory (disable exp-convergent-norm-lemma))
	  ("Subgoal 2"
	   :use ((:instance i-close-reflexive
			    (x (SUMLIST-NORM (TAYLOR-EXP-LIST NTERMS1 0 X)))))
	   :in-theory (disable i-close-reflexive))
	  ("Subgoal 1"
	   :use ((:instance exp-convergent-norm-lemma
			    (num (- nterms1 (i-large-integer)))
			    (nterms1 (i-large-integer)))
		 (:instance i-close-symmetric
			    (x (SUMLIST-NORM
				(TAYLOR-EXP-LIST (i-large-integer) 0 X)))
			    (y (SUMLIST-NORM (TAYLOR-EXP-LIST NTERMS1 0 X))))
		 )
	   :in-theory (disable exp-convergent-norm-lemma
			       i-close-symmetric))))

;; And so, the Taylor sine list norm is convergent, as the partial
;; sums are close for all large M, N.

(defthm exp-convergent-norm
  (implies (and (i-limited x)
		(integerp nterms1)
		(<= 0 nterms1)
		(i-large nterms1)
		(integerp nterms2)
		(<= 0 nterms2)
		(i-large nterms2))
	   (i-close (sumlist-norm (taylor-exp-list nterms1 0 x))
		    (sumlist-norm (taylor-exp-list nterms2 0 x))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance i-close-transitive
			    (x (sumlist-norm (taylor-exp-list nterms1 0 x)))
			    (y (sumlist-norm (taylor-exp-list (i-large-integer) 0 x)))
			    (z (sumlist-norm (taylor-exp-list nterms2 0 x))))))
	  ("Goal'''"
	   :use ((:instance i-close-symmetric
			    (x (SUMLIST-NORM (TAYLOR-EXP-LIST NTERMS2 0 X)))
			    (y (SUMLIST-NORM (TAYLOR-EXP-LIST (I-LARGE-INTEGER) 0 X)))))
	   :in-theory (disable i-close-symmetric))))


;; Now the same argument with sumlist instead of sumlist-norm....
;; First, if M is large and N>M, we get that the partial sums S_M and
;; S_N are close.

(local
 (defthm exp-convergent-lemma
   (implies (and (i-limited x)
		 (integerp nterms1)
		 (<= 0 nterms1)
		 (i-large nterms1)
		 (integerp num)
		 (< 0 num))
	    (i-close (sumlist (taylor-exp-list nterms1 0 x))
		     (sumlist (taylor-exp-list (+ nterms1 num) 0 x))))
   :hints (("Goal" :do-not-induct t
	    :in-theory (enable i-close)))))

;; So in particular, if M is large S_M is close to the partial sum
;; using i-large-integer.

(defthm exp-convergent-lemma-2
  (implies (and (i-limited x)
		(integerp nterms1)
		(<= 0 nterms1)
		(i-large nterms1))
	   (i-close (sumlist (taylor-exp-list nterms1 0 x))
		    (sumlist (taylor-exp-list (i-large-integer) 0 x))))
  :hints (("Goal" :do-not-induct t
	   :cases ((< nterms1 (i-large-integer))
		   (= nterms1 (i-large-integer))
		   (< (i-large-integer) nterms1)))
	  ("Subgoal 3"
	   :use ((:instance exp-convergent-lemma
			    (num (- (i-large-integer) nterms1))))
	   :in-theory (disable exp-convergent-lemma))
	  ("Subgoal 2"
	   :use ((:instance i-close-reflexive
			    (x (SUMLIST (TAYLOR-EXP-LIST NTERMS1 0 X)))))
	   :in-theory (disable i-close-reflexive))
	  ("Subgoal 1"
	   :use ((:instance exp-convergent-lemma
			    (num (- nterms1 (i-large-integer)))
			    (nterms1 (i-large-integer)))
		 (:instance i-close-symmetric
			    (x (SUMLIST
				(TAYLOR-EXP-LIST (i-large-integer) 0 X)))
			    (y (SUMLIST (TAYLOR-EXP-LIST NTERMS1 0 X))))
		 )
	   :in-theory (disable exp-convergent-lemma
			       i-close-symmetric))))

;; And so no matter what large counters we pick, the partial sums are
;; close to each other.

(defthm exp-convergent
  (implies (and (i-limited x)
		(integerp M) (<= 0 M) (i-large M)
		(integerp N) (<= 0 N) (i-large N))
	   (i-close (sumlist (taylor-exp-list M 0 x))
		    (sumlist (taylor-exp-list N 0 x))))
  :hints (("Goal" :do-not-induct t
	   :use ((:instance i-close-transitive
			    (x (sumlist (taylor-exp-list M 0 x)))
			    (y (sumlist (taylor-exp-list (i-large-integer) 0 x)))
			    (z (sumlist (taylor-exp-list N 0 x))))))
	  ("Goal'''"
	   :use ((:instance i-close-symmetric
			    (x (sumlist (taylor-exp-list N 0 x)))
			    (y (sumlist (taylor-exp-list (i-large-integer) 0 x)))))
	   :in-theory (disable i-close-symmetric))))



