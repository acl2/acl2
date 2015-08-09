;;;***************************************************************
;;;An ACL2 Proof of the Chinese Remainder Theorem

;;;David M. Russinoff
;;;April, 1999
;;;***************************************************************

(in-package "ACL2")

(local (include-book "crt"))

;;Recursive definition of greatest common divisor:

(defun g-c-d (x y)
  (declare (xargs :measure (nfix (+ x y))))
  (if (zp x)
      y
    (if (zp y)
	x
      (if (<= x y)
	  (g-c-d x (- y x))
	(g-c-d (- x y) y)))))

;;Two naturals are relatively prime if their gcd is 1:

(defun rel-prime (x y)
  (= (g-c-d x y) 1))

;;X is relatively prime to each member of L:

(defun rel-prime-all (x l)
  (if (endp l)
      t
    (and (rel-prime x (car l))
	 (rel-prime-all x (cdr l)))))

;;Recognizer for lists of pairwise relatively prime moduli:

(defun rel-prime-moduli (l)
  (if (endp l)
      t
    (and (integerp (car l))
	 (>= (car l) 2)
	 (rel-prime-all (car l) (cdr l))
	 (rel-prime-moduli (cdr l)))))

;;Congruence modulo M:

(defun congruent (x y m)
  (= (rem x m) (rem y m)))

;;X is congruent to Ai mod Mi for i=1,...,k, where (A1 ... Ak) is a
;;list of naturals and (M1 ... Mk) is a list of moduli:

(defun congruent-all (x a m)
  (declare (xargs :measure (:? m)))
  (if (endp m)
      t
    (and (congruent x (car a) (car m))
	 (congruent-all x (cdr a) (cdr m)))))

;;Recognizer for lists of naturals:

(defun natp-all (l)
  (if (endp l)
      t
    (and (natp (car l))
	 (natp-all (cdr l)))))

;;The Chinese Remainder Theorem states that if M1,...,Mk are pairwise
;;relatively prime moduli and A1,...,Ak are naturals, then there exists
;;a natural X such that X is congruent to Ai mod Mi for i=1,...,k.
;;Thus, our goal is to define a function CRT that computes such an X,
;;and to prove the following:

;;(defthm chinese-remainder-theorem
;;    (implies (and (natp-all a)
;;		    (rel-prime-moduli m)
;;		    (= (len a) (len m)))
;;	       (and (natp (crt a m))
;;		    (congruent-all (crt a m) a m))))

;;First, we express the gcd of X and Y as a linear combination of X and Y:

(mutual-recursion

 (defun r (x y)
   (declare (xargs :measure (nfix (+ x y))))
   (if (zp x)
       0
     (if (zp y)
	 1
       (if (<= x y)
	   (- (r x (- y x)) (s x (- y x)))
	 (r (- x y) y)))))

 (defun s (x y)
   (declare (xargs :measure (nfix (+ x y))))
   (if (zp x)
       1
     (if (zp y)
	 0
       (if (<= x y)
	   (s x (- y x))
	 (- (s (- x y) y) (r (- x y) y))))))
 )

(defthm r-s-lemma
    (implies (and (natp x)
		  (natp y))
	     (= (+ (* (r x y) x)
		   (* (s x y) y))
		(g-c-d x y)))
  :rule-classes ())

;;Thus, if X and Y are relatively prime, then RX+SY = 1.  More generally,
;;if X is relatively prime to each member of a list L, and P is the product
;;of the members of L, then we can find naturals C and D such that CX+DP = 1.
;;The reason for this, of course, is that X and P are relatively prime,
;;which follows from the divisibility properties of the gcd and Euclid's
;;Theorem (if p|ab where p is prime, then p|a or p|b).  Rather than to
;;prove all of this, however, we take a more direct route to the desired
;;result.

;;Let L = (Y . L') and let P' be the product of the members of L'.  Suppose
;;we have A,B, C', and D' such that

;;    RX + SY = C'X + D'P' = 1.

;;We must find C and D such that

;;    CX + DP = 1,

;;where P = YP'.  But since

;;    (SD')P = (SY)(D'P') = (1 - RX)(1 - C'X) = 1 - (R + C' - AC'X)X,

;;we have the solution

;;    C = R + C' - RC'X   and   D = SD'.

;;This leads to the following definitions and lemma:

(defun c (x l)
  (if (endp l)
      0
    (- (+ (r x (car l))
	  (c x (cdr l)))
       (* (r x (car l))
	  (c x (cdr l))
	  x))))

(defun d (x l)
  (if (endp l)
      1
    (* (s x (car l))
       (d x (cdr l)))))

(defun prod (l)
  (if (endp l)
      1
    (* (car l) (prod (cdr l)))))

(defthm c-d-lemma
    (implies (and (natp x)
		  (natp-all l)
		  (rel-prime-all x l))
	     (= (+ (* (c x l) x)
		   (* (d x l) (prod l)))
		1))
  :rule-classes ())

;;Now, if X and the members of L form a set of pairwise relatively
;;prime moduli, then we can construct a natural that is congrent
;;to 1 mod X and congruent to 0 mod each member of L, namely,

;;    (DP)^2 = (1 - CX)^2:

(defun one-mod (x l) (* (d x l) (prod l) (d x l) (prod l)))

(defthm one-mod-nat
    (implies (and (natp x)
		  (> x 1)
		  (natp-all l)
		  (rel-prime-all x l))
	     (natp (one-mod x l)))
  :rule-classes ())

(defthm rem-one-mod-1
    (implies (and (natp x)
		  (> x 1)
		  (natp-all l)
		  (rel-prime-all x l))
	     (= (rem (one-mod x l) x) 1))
  :rule-classes ())

(defthm rem-one-mod-0
    (implies (and (natp x)
		  (> x 1)
		  (rel-prime-moduli l)
		  (rel-prime-all x l)
		  (member y l))
	     (= (rem (one-mod x l) y) 0))
  :rule-classes ())

;;The definition of CRT is now straightforward:

(defun crt1 (a m l)
  (if (endp a)
      0
    (+ (* (car a) (one-mod (car m) (remove (car m) l)))
       (crt1 (cdr a) (cdr m) l))))

(defun crt (a m) (crt1 a m m))

;;A key lemma states that if M is a sublist of a list of pairwise
;;relatively prime moduli L, and A is a list of naturals of the same
;;length as M, and X is a member of L but not of M, then (CRT1 A M L)
;;is congruent to 0 mod X:

(defun sublistp (m l)
  (if (endp m)
      t
    (and (member (car m) l)
	 (sublistp (cdr m) l))))

(defthm rem-crt1
    (implies (and (natp-all a)
		  (rel-prime-moduli m)
		  (= (len a) (len m))
		  (rel-prime-moduli l)
		  (sublistp m l)
		  (member x l)
		  (not (member x m)))
	     (and (natp (crt1 a m l))
		  (= (rem (crt1 a m l) x) 0)))
  :rule-classes ())

;;Using the above lemma, we can prove the following generalization
;;of the Chinese Remainder Theorem:

(defun distinctp (l)
  (if (endp l)
      t
    (and (not (member (car l) (cdr l)))
	 (distinctp (cdr l)))))

(defthm crt1-thm
    (implies (and (natp-all a)
		  (rel-prime-moduli m)
		  (= (len a) (len m))
		  (rel-prime-moduli l)
		  (sublistp m l))
	     (congruent-all (crt1 a m l) a m))
  :rule-classes ())

;;The desired theorem follows easily:

(defthm chinese-remainder-theorem
    (implies (and (natp-all a)
		  (rel-prime-moduli m)
		  (= (len a) (len m)))
	     (and (natp (crt a m))
		  (congruent-all (crt a m) a m)))
  :rule-classes ())
