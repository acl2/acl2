; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(include-book "ground-zero")

(local (include-book "logior-proofs"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))
;(set-inhibit-warnings) ; restore theory warnings (optional)


;split?
(defthm logior-with-non-integer-arg
  (implies (not (integerp i))
           (and (equal (logior i j)
                       (ifix j))
                (equal (logior j i)
                       (ifix j)))))

(defthm logior-0
  (implies (case-split (integerp j))
           (equal (logior 0 j)
                  j)))

(defthm logior-commutative
  (equal (logior j i)
         (logior i j)))

(defthm logior-associative
  (equal (logior (logior i j) k)
         (logior i (logior j k))))

(defthm logior-commutative-2
  (equal (logior j i k)
         (logior i j k)))

(defthm logior-combine-constants
  (implies (syntaxp (and (quotep i)
                         (quotep j)))
           (equal (logior i j k)
                  (logior (logior i j) k))))

(defthm logior-with-an-arg-of-minus-one
  (implies (case-split (integerp i))
           (equal (logior -1 i) -1)))

;BOZO dup!
;figure this out
(defthm logior-non-negative-integerp
  (implies (and (<= 0 i)
                (<= 0 j))
           (and (integerp (logior i j))
                (<= 0 (logior i j))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-non-negative-integerp-type
  (implies (and (<= 0 i)
                (<= 0 j))
           (and (integerp (logior i j))
                (<= 0 (logior i j))))
  :rule-classes ( :type-prescription))

(defthm logior-non-negative
  (and (implies (and (<= 0 i)
                     (<= 0 j))
                (<= 0 (logior i j)))))

(defthm logior-equal-0
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (equal (logior i j) 0)
                  (and (equal i 0) (equal j 0)))))

(defthm logior-even
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (integerp (* 1/2 (logior i j)))
                  (and (integerp (* 1/2 i))
                       (integerp (* 1/2 j))))))

(defthm logior-negative-1
  (implies (and (< i 0)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (and (integerp (logior i j))
                (< (logior i j) 0)))
  :rule-classes (:rewrite :type-prescription))

(defthm logior-negative-2
  (implies (and (< j 0)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (and (integerp (logior i j))
                (< (logior i j) 0)))
  :rule-classes (:rewrite :type-prescription))

(defthm logior-negative-3
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (< (logior i j) 0)
                  (or (< i 0)
                      (< j 0)))))

(defthm logior-non-positive
  (implies (and (<= i 0)
                (<= j 0)
                )
           (<= (logior i j) 0)))

(defthm logior-self
  (implies (case-split (integerp i))
           (equal (logior i i) i)))

;bad name?
(defthm logior-simp-1
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (logior (* 2 i) (* 2 j))
                  (* 2 (logior i j)))))

(defthm logior-positive
  (implies (and (< 0 i)
                (< 0 j)
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (and (integerp (logior i j))
                (< 0 (logior i j))))
  :rule-classes (:rewrite :type-prescription))

(defthm logior-positive-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (< 0 (logior i j))
                  (and (<= 0 i)
                       (<= 0 j)
                       (or (< 0 i)
                           (< 0 j))))))

(defthm logior-negative-5
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (< -1 (logior i j))
                  (AND (< -1 I) (< -1 J))
                  )))

(defthm logior-i-lognot-i
  (implies (case-split (integerp i))
           (equal (logior i (lognot i))
                  -1)))

;move? odd...
(defthm fl-expression-rewrites-to-last-bit
  (implies (integerp i)
           (equal (+ I (* -2 (FL (* 1/2 I))))
                  (if (evenp i)
                      0
                    1))))

(defthm fl-logior-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (fl (* 1/2 (logior i j)))
                  (logior (fl (/ i 2)) (fl (/ j 2))))))

(defthm floor-logior-by-2
    (implies (and (case-split (integerp i))
		  (case-split (integerp j)))
	     (equal (floor (logior i j) 2)
                    (logior (floor i 2) (floor j 2)))))

(defthm mod-logior-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (mod (logior i j) 2)
                  (logior (mod i 2) (mod j 2)))))

(defthmd logior-def
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (logior i j)
                  (+ (* 2 (logior (fl (* 1/2 i)) (fl (* 1/2 j))))
                     (logior (mod i 2) (mod j 2)))))
  :rule-classes ((:definition :controller-alist ((acl2::binary-logior t t)))))



;make into a better form for rewriting?
;gen to make conclusion the cat of the high bits of x (none if x is a bvecp) with a vector of ones?
;BOZO reverse hyp order
;see  lshiftamt-low-4
(defthm logior-ones
    (implies (and (natp n) ;gen?
		  (bvecp x n))
	     (equal (logior x (1- (expt 2 n)))
		    (1- (expt 2 n))))
  :rule-classes ())

;rename
(defthm logior-1-x
  (implies (bvecp x 1)
           (equal (logior 1 x) 1)))




;n is a free var
;BOZO rename
;consider :linear?
(defthm or-dist-a
  (implies (and (< i (expt 2 n))
                (< j (expt 2 n))
                )
           (< (logior i j) (expt 2 n)))
  :rule-classes ((:rewrite :match-free :all)))

(defthm logior-bvecp
  (implies (and (bvecp x n)
                (bvecp y n))
           (bvecp (logior x y) n)))

;gen?
;whoa.  this is a lower bound
;unfortunate to have to disable those rules..
(defthm logior-bnd
  (implies (and (integerp x)
                (>= x 0)
                (integerp y)
                (>= y 0))
           (<= x (logior x y)))
  :rule-classes ())


;generalize to or of disjoint ranges?
(defthm OR-DIST-B
    (implies (and (< y (expt 2 n))
                  (integerp x) (>= x 0)
		  (integerp y) (>= y 0)
		  (integerp n) (>= n 0)
		  )
	     (= (logior (* (expt 2 n) x) y)
		(+ (* (expt 2 n) x) y)))
  :rule-classes ())

;BOZO rename!
;consider making rewrite?
(defthm or-dist-c
  (implies (and (integerp x) (>= x 0)
                (integerp y) (>= y 0)
                (integerp n) (>= n 0))
           (= (logior (* (expt 2 n) x)
                      (* (expt 2 n) y))
              (* (expt 2 n) (logior x y))))
  :rule-classes ())

(defthmd mod-logior
  (implies (and (integerp x) (>= x 0)
                (integerp y) (>= y 0)
                (integerp n) (>= n 0)
                )
           (equal (mod (logior x y) (expt 2 n))
                  (logior (mod x (expt 2 n)) (mod y (expt 2 n))))))

