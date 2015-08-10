;  Book           grcd
;  Contributed by Matyas Sustik
;  Date created   2000-05-06
;  $Id: grcd.lisp,v 1.16 2001/09/05 19:18:24 matyas Exp $
;
;  Special thanks to Robert Bellarmine Krug and Matt Kaufmann for their
;  insight and help in simplifying the proofs.
;
;  Robert B.K. helped me through with the basics of ACL2 use, best of
;  all he made me understand to use disable!
;
;  Matt K. pointed out several unnecessary hypothesis and not well
;  formed rewrite rules in the very first version of this book (where
;  the rules have changed so much those comments were removed with the
;  rules but the philosophy behind them is still present) he also
;  helped with the use of local and encapsulate in order the book to
;  certify.

(in-package "ACL2")
(include-book "int-division")
(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(defmacro np (x)
  (list 'and (list 'integerp x) (list '<= 0 x)))

(defmacro pintp (x)
  (list 'and (list 'integerp x) (list '< 0 x)))

; We define the Euclidean algoritm for natural numbers, but we return
; not only the greatest common divisor but the coefficients of the
; linear combination which produces the gcd from the arguments.  We
; also return the quotients.
;
; Then the definition is extended for all the integers.  The reason
; that we want gcd defined for all integers is to be able to easily
; prove: (a; b) = (a; b + a*c).  It is cumbersome to deal with the c <
; 0, b + a*c > 0 case which makes a possible induction argument
; complicated.
;
; Care must be taken to get (Euclid-alg-nat a b) and (Euclid-alg-nat b
; a) to have the same coefficients.  Note that the linear combination
; is not unique.

(defun Euclid-alg-nat (a b)
  (declare (xargs  :measure (if (and (np a)
                                     (np b))
                                (cons (+ a 1) (+ b 1))
                              0)))
  (if (and (np a) (np b))
      (cond ((equal a b) (mv a 1 0 1 1)) ; has to be the first for (0 0).
            ((equal b 0) (mv a 1 0 1 0))
            ((equal a 0) (mv b 0 1 0 1))
            ((< b a) (mv-let (g x y u v) (Euclid-alg-nat b a)
                             (mv g y x v u)))
            (t (mv-let (g x y u v) (Euclid-alg-nat a (- b a))
                       (mv g (- x y) y u (+ u v)))))
    (mv 0 0 0 0 0)))

(defun Euclid-alg (a b)
  (if (and (integerp a) (integerp b))
      (cond ((and (<= 0 a) (<= 0 b))
             (Euclid-alg-nat a b))
            ((and (> 0 a) (<= 0 b))
             (mv-let (g x y u v) (Euclid-alg-nat (- a) b)
                     (mv g (- x) y (- u) v)))
            ((and (<= 0 a) (> 0 b))
             (mv-let (g x y u v) (Euclid-alg-nat a (- b))
                     (mv g x (- y) u (- v))))
            (t
             (mv-let (g x y u v) (Euclid-alg-nat (- a) (- b))
                     (mv g (- x) (- y) (- u) (- v)))))
    (mv 0 0 0 0 0)))

(local
 (defthm Euclid-alg-nat-gives-gcd
   (implies (and (np a)
		 (np b))
	    (mv-let (g x y u v) (Euclid-alg-nat a b)
		    (and (equal (* g u) a)
			 (equal (* g v) b)
			 (equal (+ (* x a) (* y b)) g))))))

; MattK: The following may allow the previous rules to be applied
; automatically more often, since (mv-nth 0 ...) will not be expanded
; to (car ...).  To see what's going on, try :pr
; Euclid-alg-nat-gives-gcdq.  Anyhow, some terms of the form (car ...)
; below now is mv-nth.
(local (in-theory (disable mv-nth)))

; This basically says that (car (Euclid-alg a b)) is the greatest among
; divisors.
(local
 (defthm Euclid-alg-nat-commutes-with-*
   (implies (and (np a)
		 (np b)
		 (pintp c))
	    (equal (Euclid-alg-nat (* a c) (* b c))
		   (mv-let (g x y u v) (Euclid-alg-nat a b)
			   (mv (* g c) x y u v))))))

; The use of :corollary was suggested by Robert B.K.
(local
 (defthm Euclid-alg-nat-type
   (implies (and (np a)
		 (np b))
	    (mv-let (g x y u v) (Euclid-alg-nat a b)
		    (and (np g)
			 (integerp x)
			 (integerp y)
			 (np u)
			 (np v))))
   :rule-classes ((:type-prescription
		   :corollary
		   (np (mv-nth 0 (Euclid-alg-nat a b))))
		  (:type-prescription
		   :corollary
		   (integerp (mv-nth 1 (Euclid-alg-nat a b))))
		  (:type-prescription
		   :corollary
		   (integerp (mv-nth 2 (Euclid-alg-nat a b))))
		  (:type-prescription
		   :corollary
		   (np (mv-nth 3 (Euclid-alg-nat a b))))
		  (:type-prescription
		   :corollary
		   (np (mv-nth 4 (Euclid-alg-nat a b)))))))

; Matt K. suggested this rule to be a :type-prescription rule.
(local
 (defthm Euclid-alg-nat-0-0
   (implies (and (np a)
		 (np b)
		 (or (< 0 a)
		     (< 0 b)))
	    (and (integerp (mv-nth 0 (Euclid-alg-nat a b)))
                 (< 0 (mv-nth 0 (Euclid-alg-nat a b)))))
   :rule-classes :type-prescription))

(local
 (defun ind-int (n)
   (if (integerp n)
	 (if (< 0 n)
	     (ind-int (+ -1 n))
	   t)
     t)))

(local
 (defthm Euclid-alg-nat-spec-1-a
   (implies (np a)
	    (equal (Euclid-alg-nat 1 a)
		   (mv 1 1 0 1 a)))
   :hints (("Goal"
	    :induct (ind-int a))
	   ("Subgoal *1/2''"
	    :expand (Euclid-alg-nat a 1)))))

; This cannot be a rewrite rule.  ACL2 would not find a loop stopper
; for this complex expression.
; MattK: So, we supply our own loop stopper.  See the documentation on
; :rewrite in topic rule-classes, which points to the documentation
; for loop-stopper.
(local
 (defthm Euclid-alg-nat-is-commutative
   (implies (and (np a)
		 (np b)
		 (or (< a b)
		     (< b a)))
	    (equal (Euclid-alg-nat a b)
		   (mv-let (g x y u v) (Euclid-alg-nat b a)
			   (mv g y x v u))))
   :rule-classes
   ((:rewrite :loop-stopper ((a b))))))

; Access functions:
(defun grcd (a b)
  (mv-let (g x y u v)
	  (Euclid-alg a b)
	  (declare (ignore x y u v))
	  g))

(defun grcd-lin-1 (a b)
  (mv-let (g x y u v)
	  (Euclid-alg a b)
	  (declare (ignore g y u v))
	  x))

(defun grcd-lin-2 (a b)
  (mv-let (g x y u v)
	  (Euclid-alg a b)
	  (declare (ignore g x u v))
	  y))

(defun grcd-quotient-1 (a b)
  (mv-let (g x y u v)
	  (Euclid-alg a b)
	  (declare (ignore g x y v))
	  u))

(defun grcd-quotient-2 (a b)
  (mv-let (g x y u v)
	  (Euclid-alg a b)
	  (declare (ignore g x y u))
	  v))

(defthm grcd-type-int
  (np (grcd a b))
  :rule-classes :type-prescription)

; MattK: It seems reasonable to generate a case split in subsequent theorems
; when we try to apply this lemma but we cannot eliminate the case that b=0;
; presumably that extra case will be easy to prove.
(defthm grcd-positive
  (implies (and (integerp a)
		(integerp b)
		(case-split (not (and (equal 0 a)
				      (equal 0 b)))))
	   (pintp (grcd a b)))
  :rule-classes :type-prescription)

(defthm grcd-lin-1-type
  (integerp (grcd-lin-1 a b))
  :rule-classes :type-prescription)

(defthm grcd-lin-2-type
  (integerp (grcd-lin-2 a b))
  :rule-classes :type-prescription)

(defthm grcd-quotient-1-type
  (integerp (grcd-quotient-1 a b))
  :rule-classes :type-prescription)

(defthm grcd-quotient-2-type
  (integerp (grcd-quotient-2 a b))
  :rule-classes :type-prescription)

; MattK: I prefer an unconditional rule here.  (And in the next two
; theorems.)
(defthm grcd-spec-a-0
  (equal (grcd a 0)
         (abs (ifix a))))

(defthm grcd-spec-a-a
  (equal (grcd a a)
         (abs (ifix a))))

(defthm grcd-spec-a-1
  (equal (grcd 1 a)
	 (if (integerp a)
	     1
	   0)))

(in-theory (disable Euclid-alg-nat))

; Thanks to Matt K. to point out how to split into cases in the proof.
(defthm grcd-commutativity
  (implies (and (integerp a)
		(integerp b))
	   (equal (grcd a b)
		  (grcd b a)))
  :hints (("Goal"
           :cases
           ((and (<= a 0) (<= b 0) (< (- a) (- b)))
            (and (<= a 0) (<= b 0) (< (- b) (- a)))
            (and (<= a 0) (<= 0 b) (< (- a) b))
            (and (<= a 0) (<= 0 b) (< b (- a)))
            (and (<= 0 a) (<= b 0) (< a (- b)))
            (and (<= 0 a) (<= b 0) (< (- b) a))
            (and (<= 0 a) (<= 0 b) (< a b))
            (and (<= 0 a) (<= 0 b) (< b a))))))

(local (in-theory (disable Euclid-alg-nat-gives-gcd)))

(local
 (defthm Euclid-alg-nat-gives-gcd-alternate
   (implies (and (np a)
		 (np b))
            (equal (mv-nth 0 (Euclid-alg-nat a b))
                   (+ (* (mv-nth 1 (Euclid-alg-nat a b)) a)
                      (* (mv-nth 2 (Euclid-alg-nat a b)) b))))
   :hints (("Goal" :use Euclid-alg-nat-gives-gcd))))

(defthm grcd-is-linear-combination
  (equal (grcd a b)
         (+ (* a (grcd-lin-1 a b)) (* b (grcd-lin-2 a b)))))

(local (in-theory (disable Euclid-alg-nat-gives-gcd-alternate)))

(local (in-theory (disable Euclid-alg-nat-commutes-with-*)))

(defthm grcd-commutes-with-*
  (implies (and (integerp a)
		(integerp b)
		(np c))
	   (equal (grcd (* a c) (* b c))
		  (* (grcd a b) c)))
  :hints (("Goal"
	   :use (Euclid-alg-nat-commutes-with-*
                 (:instance Euclid-alg-nat-commutes-with-*
			    (a (- a))
			    (b (- b)))
                 (:instance Euclid-alg-nat-commutes-with-*
			    (b (- b)))
                 (:instance Euclid-alg-nat-commutes-with-*
			    (b (- b)))
                 (:instance Euclid-alg-nat-commutes-with-*
			    (a (- a)))))))

; MattK:  On a hunch, I switched which of the following two lemmas to keep
; enabled for the proof of grcd-divides-op-1-lemma.  Lucky me.
(local (in-theory (enable Euclid-alg-nat-gives-gcd)))
(local (in-theory (disable Euclid-alg-nat-gives-gcd-alternate)))

(defthm grcd-divides-op-1-lemma
  (implies (and (integerp a)
		(integerp b))
	   (equal (* (grcd a b) (grcd-quotient-1 a b)) a)))

(defthm grcd-divides-op-2-lemma
  (implies (and (integerp a)
		(integerp b))
	   (equal (* (grcd a b) (grcd-quotient-2 a b)) b)))

; We have all the theorems about the access functions so we can disable
; them.
(in-theory (disable grcd))
(in-theory (disable grcd-lin-1))
(in-theory (disable grcd-lin-2))
(in-theory (disable grcd-quotient-1))
(in-theory (disable grcd-quotient-2))

(defthm grcd-quotient-1-not-zero
  (implies (and (integerp a)
		(integerp b)
		(equal 0 (grcd-quotient-1 a b)))
	   (equal (equal 0 (grcd-quotient-1 a b))
		  (equal 0 a)))
  :hints (("Goal"
	   :in-theory (disable grcd-divides-op-1-lemma)
	   :use grcd-divides-op-1-lemma)))

(defthm grcd-quotient-2-not-zero
  (implies (and (integerp a)
		(integerp b)
		(equal 0 (grcd-quotient-2 a b)))
	   (equal (equal 0 (grcd-quotient-2 a b))
		  (equal 0 b)))
  :hints (("Goal"
	   :in-theory (disable grcd-divides-op-2-lemma)
	   :use grcd-divides-op-2-lemma)))

(defthm common-divisor-divides-grcd
  (implies (and (divides d a)
		(divides d b))
	   (divides d (grcd a b))))

; This is a useful lemma but not frequently needed.
(in-theory (disable grcd-is-linear-combination))

(local
 (defthm grcd-quotients-give-a-/-b-lemma
   (implies (and (integerp a)
		 (integerp b)
		 (not (equal 0 b)))
	    (equal (/ (* (grcd a b) (grcd-quotient-1 a b))
		      (* (grcd a b) (grcd-quotient-2 a b)))
		   (/ a b)))
   :rule-classes nil
   :hints (("Goal"
	    :in-theory (disable associativity-of-*
				distributivity-of-/-over-*
				/-cancellation-on-left)))))

(defthm grcd-quotients-gives-a-/-b
  (implies (and (integerp a)
		(integerp b)
		(not (equal 0 b)))
	   (equal (/ (grcd-quotient-1 a b) (grcd-quotient-2 a b))
		  (/ a b)))
  :hints (("Goal"
	   :use grcd-quotients-give-a-/-b-lemma)))

(local
 (defthm grcd-quotients-are-relative-prime-lemma-1
   (implies (and (integerp a)
		 (integerp b))
	    (equal (grcd a b)
		   (grcd (* (grcd-quotient-1 a b) (grcd a b))
			 (* (grcd-quotient-2 a b) (grcd a b)))))
   :rule-classes nil))

(local
 (defthm grcd-quotients-are-relative-prime-lemma-2
   (implies (and (integerp a)
		 (integerp b))
	    (equal (grcd (* (grcd-quotient-1 a b) (grcd a b))
			 (* (grcd-quotient-2 a b) (grcd a b)))
		   (* (grcd a b) (grcd (grcd-quotient-1 a b)
				       (grcd-quotient-2 a b)))))
   :rule-classes nil
   :hints (("Goal"
	    :use ((:instance grcd-commutes-with-*
			     (a (grcd-quotient-1 a b))
			     (b (grcd-quotient-2 a b))
			     (c (grcd a b))))))))

(defthm grcd-quotients-are-relative-primes
  (implies (and (integerp a)
		(integerp b))
	   (equal (grcd (grcd-quotient-1 a b)
			(grcd-quotient-2 a b))
		  1))
  :hints (("Goal"
	   :use (grcd-quotients-are-relative-prime-lemma-1
		 grcd-quotients-are-relative-prime-lemma-2))))

(defthm grcd-quotient-1-description
  (implies (and (integerp a)
		(integerp b))
	   (equal (integer-quotient (grcd a b) a)
		  (grcd-quotient-1 a b)))
  :hints (("Goal"
	   :use ((:instance integer-quotient-*-cancellation
			    (a (grcd a b))
			    (q (grcd-quotient-1 a b)))))))

(defthm grcd-quotient-2-description
  (implies (and (integerp a)
		(integerp b))
	   (equal (integer-quotient (grcd a b) b)
		  (grcd-quotient-2 a b)))
  :hints (("Goal"
	   :use ((:instance integer-quotient-*-cancellation
			    (a (grcd a b))
			    (q (grcd-quotient-2 a b)))))))

(in-theory (enable divides-integer-quotient-equivalence))

(defthm grcd-divides-op-1
  (implies (and (integerp a)
		(integerp b))
	   (divides (grcd a b) a)))

(defthm grcd-divides-op-2
  (implies (and (integerp a)
		(integerp b))
	   (divides (grcd a b) b)))

(in-theory (disable divides-integer-quotient-equivalence))

; MattK: Might as well make this a :rewrite rule.
(defthm grcd-addition-lemma-1
  (implies (and (integerp a)
		(integerp b)
		(integerp c))
	   (divides (grcd a b)
		    (grcd a (+ b (* a c))))))

; MattK: Might as well make this a :rewrite rule.
(defthm grcd-addition-lemma-2
  (implies (and (integerp a)
		(integerp b)
		(integerp c))
	   (divides (grcd a (+ b (* a c)))
		    (grcd a b)))
  :hints (("Goal"
	   :use ((:instance grcd-addition-lemma-1
			    (b (+ b (* a c)))
			    (c (- c)))))))

; Note that this is not proved with an induction on c.
(defthm grcd-addition-lemma
  (implies (and (integerp a)
		(integerp b)
		(integerp c))
	   (equal (grcd a (+ b (* a c)))
		  (grcd a b)))
  :hints (("Goal"
	   :use
           ((:instance equality-from-division
                       (a (grcd a (+ b (* a c))))
                       (b (grcd a b)))))))

(defthm grcd-a-b-divides-a-bc
  (implies (and (integerp a)
		(integerp b)
		(integerp c))
	   (divides (grcd a b)
		    (grcd a (* b c)))))

; The following 6 lemmas lead up to the proof of:
; (a; c) = 1  =>  (a; b) = (a; b*c).
; The major steps are separated in the lemmas:
; (a; c) = 1  =>  1 = a*x + c*z
; multiply with b: b = b*a*x + b*c*z
; (a; b) = (a; b*a*x + b*c*z) = (a ; b*c*z)
; From the grcd-a-b-divides-a-bc theorem we have:
; (a; b) divides (a; b*c) which in turn divides (a; b*c*z).
; using the divider-< lemmas we are done.
(local
 (defthm grcd-multiplication-lemma-1
   (implies (and (integerp a)
		 (integerp b)
		 (integerp c)
		 (equal 1 (grcd a c)))
	    (equal (grcd a (* b c (grcd-lin-2 a c)))
		   (grcd a (+ (* b a (grcd-lin-1 a c))
			      (* b c (grcd-lin-2 a c))))))
   :hints (("Goal"
	    :use ((:instance grcd-addition-lemma
			     (b (* b c (grcd-lin-2 a c)))
			     (c (* b (grcd-lin-1 a c)))))))))


; MattK; Might as well make the following a :rewrite rule.  I removed
; the hypothesis (integerp b), which involved the free variable b and
; thus could prevent the rule from firing.  Unfortunately, the proof
; of grcd-multiplication-lemma-4 failed when I made this a :rewrite
; rule, which is why it is now local to an encapsulate.
(local
 (encapsulate
  ()
  (local
   (defthm grcd-multiplication-lemma-2
     (implies (and (integerp a)
                   (integerp c)
                   (equal 1 (grcd a c)))
              (equal (+ (* a (grcd-lin-1 a c))
                        (* c (grcd-lin-2 a c)))
                     1))
     :hints (("Goal" :in-theory (enable grcd-is-linear-combination)))))

  (defthm grcd-multiplication-lemma-3
    (implies (and (integerp a)
                  (integerp b)
                  (integerp c)
                  (equal 1 (grcd a c)))
             (equal (* b (+ (* a (grcd-lin-1 a c))
                            (* c (grcd-lin-2 a c))))
                    b))
    :rule-classes nil)))

(local
 (defthm grcd-multiplication-lemma-4
   (implies (and (integerp a)
		 (integerp b)
		 (integerp c)
		 (equal 1 (grcd a c)))
	    (equal (+ (* b a (grcd-lin-1 a c))
		      (* b c (grcd-lin-2 a c)))
		   b))
   :hints (("Goal"
	    :use grcd-multiplication-lemma-3))))

(local
 (defthm grcd-multiplication-lemma-5
   (implies (and (integerp a)
		 (integerp b)
		 (integerp c)
		 (equal 1 (grcd a c)))
	    (equal (grcd a (+ (* b a (grcd-lin-1 a c))
			      (* b c (grcd-lin-2 a c))))
		   (grcd a b)))
   :rule-classes nil
   :hints (("Goal"
	    :use grcd-multiplication-lemma-4))))

(local
 (defthm grcd-multiplication-lemma-6
   (implies (and (integerp a)
		 (integerp b)
		 (integerp c)
		 (equal 1 (grcd a c)))
	    (equal (grcd a (* b c (grcd-lin-2 a c)))
		   (grcd a b)))
   :rule-classes nil
   :hints (("Goal"
	    :use grcd-multiplication-lemma-5))))

(in-theory (disable common-divisor-divides-grcd))

(defthm grcd-multiplication-with-relative-prime
  (implies (and (integerp a)
		(integerp b)
		(integerp c)
		(equal 1 (grcd a c)))
	   (equal (grcd a (* b c))
		  (grcd a b)))
  :hints (("Goal"
	   :use
           ((:instance grcd-a-b-divides-a-bc
                       (b (* b c))
                       (c (grcd-lin-2 a c)))
	    grcd-multiplication-lemma-6
	    (:instance equality-from-division
		       (a (grcd a b))
		       (b (grcd a (* b c))))))))

(in-theory (enable divides-integer-quotient-equivalence))

; The following may be useful theorems but are not needed for the
; Fibonacci theorem in fibonacci.lisp.  They can be used to prove the
; existence of lowest terms for rationals.

(defthm grcd-*-cancellation
  (implies (and (equal b (* a (integer-quotient a b)))
		(np a)
		(integerp b))
	   (equal (grcd a b) a))
  :hints (("Goal"
	   :use (:instance grcd-commutes-with-*
			   (a 1)
			   (b (integer-quotient a b))
			   (c a)))))

(defthm grcd-divides-connection-lemma-1
  (implies (and (np a)
		(integerp b))
	   (implies (divides a b)
		    (equal (grcd a b) a)))
  :hints (("Goal'''"
	   :use grcd-*-cancellation)))

(in-theory (disable divides-integer-quotient-equivalence))

(defthm grcd-divides-connection-lemma-2
  (implies (and (np a)
		(integerp b))
	   (implies (equal (grcd a b) a)
		    (divides a b)))
  :hints (("Goal'''"
	   :use grcd-divides-op-2)))

(defthm grcd-divides-connection
  (implies (and (np a)
		(integerp b))
	   (equal (divides a b)
		  (equal (grcd a b) a))))

(in-theory (disable grcd-*-cancellation))
(in-theory (disable grcd-divides-connection-lemma-1))
(in-theory (disable grcd-divides-connection-lemma-2))

(defthm divide-with-relative-prime-lemma-1
  (implies (and (np a)
		(integerp b)
		(integerp c)
		(divides a (* b c))
		(equal (grcd a c) 1))
	   (equal (grcd a (* b c)) a))
  :rule-classes nil)

(defthm divide-with-relative-prime-lemma-2
  (implies (and (np a)
		(integerp b)
		(integerp c)
		(divides a (* b c))
		(equal (grcd a c) 1))
	   (equal (grcd a b) a))
  :rule-classes nil
  :hints (("Goal"
	   :use divide-with-relative-prime-lemma-1)))

(defthm divide-with-relative-prime
  (implies (and (np a)
		(integerp b)
		(integerp c)
		(divides a (* b c))
		(equal (grcd a c) 1))
	   (divides a b))
  :hints (("Goal"
	   :use divide-with-relative-prime-lemma-2)))
