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

(in-package "RTL")

;BOZO Everything in this book should be redundant...

(set-match-free-default :all)

;Contains bvecp lemmas about the RTL primitives.
;Also contains type lemmas (non-negative integer, natp, etc.)

(defun fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(local (include-book "../../arithmetic/expo"))

(defun expo-measure (x)
;  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((not (rationalp x)) 0)
	((< x 0) '(2 . 0))
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defnd expo (x)
  (declare (xargs :measure (:? x)
                  :verify-guards nil))
  (mbe
   :logic
   (cond ((or (not (rationalp x)) (equal x 0)) 0)
         ((< x 0) (expo (- x)))
         ((< x 1) (1- (expo (* 2 x))))
         ((< x 2) 0)
         (t (1+ (expo (/ x 2)))))
   :exec
   (if (rationalp x)
       (let* ((n (abs (numerator x)))
              (d (denominator x))
              (ln (integer-length n))
              (ld (integer-length d))
              (l (- ln ld)))
         (if (>= ln ld)
             (if (>= (ash n (- l)) d) l (1- l))
           (if (> ln 1)
               (if (> n (ash d l)) l (1- l))
             (- (integer-length (1- d))))))
     0)))

;should this be here?  should it be enabled?
(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(local (include-book "bits"))
(local (include-book "setbits"))
(local (include-book "setbitn"))
(local (include-book "encode"))
(local (include-book "decode"))
(local (include-book "logs"))
(local (include-book "lnot"))
(local (include-book "bitn"))
(local (include-book "shft"))
(local (include-book "cat"))
(local (include-book "logand"))
(local (include-book "merge")) ;would like to remove this
(local (include-book "mulcat"))
(local (include-book "land0"))
(local (include-book "lior0"))
(local (include-book "lxor0"))
(local (include-book "cat"))

(include-book "rtl")

;; logand

(defthm logand-integer-type-prescription
  (integerp (logand i j))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-non-negative-integer-type-prescription
  (implies (or (<= 0 i)
               (<= 0 j))
           (and (<= 0 (logand i j))
                (integerp (logand i j))))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-non-negative
  (implies (or (<= 0 x)
               (<= 0 y)
               )
           (<= 0 (logand x y))))

(defthm bvecp-logand-alternate
  (implies (and (integerp n)
                (<= 0 n)
                (bvecp x n)
                (bvecp y n))
           (bvecp (logand x y) n))
  :hints (("Goal" :in-theory (enable bvecp))))


;; logior

(defthm logior-integer-type-prescription
  (integerp (logior i j))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-non-negative-integer-type-prescription
  (implies (and (<= 0 i)
                (<= 0 j))
           (and (<= 0 (logior i j))
                (integerp (logior i j))))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-non-negative
  (implies (and (<= 0 i)
                (<= 0 j)
                )
           (<= 0 (logior i j))))

(defthm bvecp-logior-alternate
  (implies (and (integerp n)
                (<= 0 n)
                (bvecp x n)
                (bvecp y n))
           (bvecp (logior x y) n)))

;; logxor
;!!fix this to have lemmas like logand,logior above
(defthm natp-logxor-alternate-2
    (implies (and (integerp x) (<= 0 x)
		  (integerp y) (<= 0 y))
	     (and (integerp (logxor x y))
		  (<= 0 (logxor x y))))
  :rule-classes (:rewrite :type-prescription))

(defthm bvecp-logxor-alternate
  (implies (and (integerp n)
                (<= 0 n)
                (bvecp x n)
                (bvecp y n))
           (bvecp (logxor x y) n)))

;if1

(defthm bvecp-if1
  (equal (bvecp (if1 x y z) n)
         (if1 x (bvecp y n) (bvecp z n))))


;; mod-

;finish this section (will have to change comp2-inv?)

#|
(defthm mod--nonnegative-integer-type
  (and (integerp (mod- l n x))
       (<= 0 (mod- l n x)))
  :hints (("Goal" :in-theory (enable mod-)))
  :rule-classes (:type-prescription)
  )

;this rule is no better than mod--nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription mod-)))
|#

#| mod- is now a macro!
(defthm mod--bvecp
  (implies (and (bvecp x n)
                (bvecp y n)
                (integerp n)
                (>= n 0))
           (bvecp (mod- x y n) n))
  :hints (("Goal" :in-theory (enable bvecp mod- comp2-inv))))
|#






(DEFTHM UNKNOWN-upper-bound
  (< (UNKNOWN KEY SIZE N) (expt 2 size))
  :HINTS
  (("Goal" :use bvecp-unknown
    :IN-THEORY (set-difference-theories
                (ENABLE BVECP)
                '(bvecp-unknown))))
  :RULE-CLASSES
  (:REWRITE (:linear :trigger-terms ((UNKNOWN KEY SIZE N)))))
