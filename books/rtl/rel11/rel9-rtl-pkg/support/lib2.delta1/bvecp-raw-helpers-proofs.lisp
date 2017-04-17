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

;; (set-enforce-redundancy t)

;Contains bvecp lemmas about the RTL primitives.
;Also contains type lemmas (non-negative integer, natp, etc.)

(include-book "rtl")

(include-book "bits")
(include-book "float")

(local (include-book "logn"))

(local (include-book "../../arithmetic/top"))

(set-match-free-default :all)

(defun fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))


(defun expo-measure (x)
;  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((not (rationalp x)) 0)
	((< x 0) '(2 . 0))
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defun expo (x)
  (declare (xargs :guard t
                  :measure (:? x)
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

;; bits

(defthm bits-nonnegative-integerp-type
  (and (<= 0 (bits x i j))
       (integerp (bits x i j)))
  :rule-classes (:type-prescription))

;this rule is no better than bits-nonnegative-integer and might be worse
(in-theory (disable (:type-prescription bits)))

(defthm bits-bvecp
   (implies (and (<= (+ 1 i (- j)) k)
                 (case-split (integerp k))
                 )
            (bvecp (bits x i j) k)))


;; setbits

(defthm setbits-nonnegative-integer-type
  (and (integerp (setbits x w i j y))
       (<= 0 (setbits x w i j y)))
  :rule-classes (:type-prescription)
  )

;this rule is no better than setbits-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription setbits)))

(defthm setbits-bvecp
  (implies (and (<= w k)
                (case-split (integerp k))
                )
           (bvecp (setbits x w i j y) k))
  :hints (("Goal" :use ((:instance bvecp-monotone
                                   (x (setbits x w i j y))
                                   (m k)
                                   (n w)))
           :cases ((not (natp w))))
          ("Subgoal 1" :in-theory (e/d (bvecp cat) ()))))





;; setbitn

(defthm setbitn-nonnegative-integer-type
  (and (integerp (setbitn x w n y))
       (<= 0 (setbitn x w n y)))
  :rule-classes (:type-prescription)
  )

;this rule is no better than setbits-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription setbitn)))

(defthm setbitn-bvecp
  (implies (and (<= w k)
                (case-split (integerp k)))
           (bvecp (setbitn x w n y) k))
  :hints (("Goal" :use ((:instance bvecp-monotone
                                   (x (setbitn x w n y))
                                   (m k)
                                   (n w)))
           :cases ((not (natp w))))
          ("Subgoal 1" :in-theory (e/d (bvecp cat) ()))))


;; log<

(defthm log<-nonnegative-integer-type
  (and (integerp (log< x y))
       (<= 0 (log< x y)))
  :rule-classes (:type-prescription))

;this rule is no better than log<-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log<)))

(defthm log<-bvecp
  (bvecp (log< x y) 1))


;; log<=

(defthm log<=-nonnegative-integer-type
  (and (integerp (log<= x y))
       (<= 0 (log<= x y)))
  :rule-classes (:type-prescription))

;this rule is no better than log<=-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log<=)))

(defthm log<=-bvecp
  (bvecp (log<= x y) 1))



;; log>

(defthm log>-nonnegative-integer-type
  (and (integerp (log> x y))
       (<= 0 (log> x y)))
  :rule-classes (:type-prescription))

;this rule is no better than log>-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log>)))

(defthm log>-bvecp
  (bvecp (log> x y) 1))



;; log>=

(defthm log>=-nonnegative-integer-type
  (and (integerp (log>= x y))
       (<= 0 (log>= x y)))
  :rule-classes (:type-prescription))

;this rule is no better than log>=-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log>=)))

(defthm log>=-bvecp
  (bvecp (log>= x y) 1))



;; log=

(defthm log=-nonnegative-integer-type
  (and (integerp (log= x y))
       (<= 0 (log= x y)))
  :rule-classes (:type-prescription))

;this rule is no better than log=-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log=)))

(defthm log=-bvecp
  (bvecp (log= x y) 1))



;; log<>

(defthm log<>-nonnegative-integer-type
  (and (integerp (log<> x y))
       (<= 0 (log<> x y)))
  :rule-classes (:type-prescription))

;this rule is no better than log<>-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription log<>)))

(defthm log<>-bvecp
  (bvecp (log<> x y) 1))



;; logand1

(defthm logand1-nonnegative-integer-type
  (and (integerp (logand1 x y))
       (<= 0 (logand1 x y)))
  :rule-classes (:type-prescription))

;this rule is no better than logand1-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription logand1)))

(defthm logand1-bvecp
  (bvecp (logand1 x y) 1))



;; logior1

(defthm logior1-nonnegative-integer-type
  (and (integerp (logior1 x))
       (<= 0 (logior1 x)))
  :rule-classes (:type-prescription))

;this rule is no better than logior1-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription logior1)))

(defthm logior1-bvecp
  (bvecp (logior1 x) 1))



;; logxor1

(defthm logxor1-nonnegative-integer-type
  (and (integerp (logxor1 x))
       (<= 0 (logxor1 x)))
  :rule-classes (:type-prescription))

;this rule is no better than logxor1-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription logxor1)))

(defthm logxor1-bvecp
  (bvecp (logxor1 x) 1))



;; lnot

(defthm lnot-nonnegative-integer-type
  (and (integerp (lnot x n))
       (<= 0 (lnot x n)))
  :rule-classes ((:type-prescription :typed-term (lnot x n)))
  :hints (("Goal" :in-theory (e/d (lnot) ()))))

;lnot-nonnegative-integer-type is strictly better, and we don't need both
(in-theory (disable (:type-prescription lnot)))

(defthm lnot-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lnot x n) k))
  :hints (("Goal" :in-theory (e/d (bvecp lnot) ())
           :cases ((not (and (integerp n)
                             (bvecp (bits x (+ -1 n) 0) n)))))))


;; bitn

(defthm bitn-nonnegative-integer
  (and (integerp (bitn x n))
       (<= 0 (bitn x n)))
  :rule-classes ( :type-prescription))

;this rule is no better than bitn-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription bitn)))

(defthm bitn-bvecp
  (implies (and (<= 1 k)
                (case-split (integerp k)))
           (bvecp (bitn x n) k)))

;; shft

(defthm shft-nonnegative-integer-type
  (and (integerp (shft x s l))
       (<= 0 (shft x s l)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (e/d (shft) ()))))

;(:type-prescription shft) is no better than shft-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription shft)))

(defthm shft-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (shft x s n) k)))

;; cat

(defthm cat-nonnegative-integer-type
  (and (integerp (CAT X m Y N))
       (<= 0 (CAT X m Y N)))
  :rule-classes (:type-prescription))

(in-theory (disable (:type-prescription cat-nonnegative-integer-type)))

(defthm cat-bvecp
  (implies (and (<= (+ m n) k)
                (case-split (integerp k)))
           (bvecp (cat x m y n) k)))


;; logand
(local (include-book "../support/logand"))

(defthm logand-integer-type-prescription
  (integerp (logand i j))
  :rule-classes (:type-prescription))

(defthm logand-non-negative-integer-type-prescription
  (implies (or (<= 0 i)
               (<= 0 j))
           (and (<= 0 (logand i j))
                (integerp (logand i j))))
  :rule-classes (:type-prescription))

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
           (bvecp (logand x y) n)))


;; logior
(local (include-book "../support/logior"))

(defthm logior-integer-type-prescription
  (integerp (logior i j))
  :rule-classes (:type-prescription))

(defthm logior-non-negative-integer-type-prescription
  (implies (and (<= 0 i)
                (<= 0 j))
           (and (<= 0 (logior i j))
                (integerp (logior i j))))
  :rule-classes (:type-prescription))

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


;; mulcat

(defund mulcat (l n x)

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat, which can't
; be changed because of the guard of bits.

  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat (mulcat l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond ((eql n 1)
                     (bits x (1- l) 0))
                    ((and (integerp n) (> n 0))
                     (cat (mulcat l (1- n) x)
                          (* l (1- n))
                          x
                          l))
                    (t 0))))

(defthm mulcat-nonnegative-integer-type
  (and (integerp (mulcat l n x))
       (<= 0 (mulcat l n x)))
  :rule-classes (:type-prescription))

;this rule is no better than mulcat-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription mulcat-nonnegative-integer-type)))

(defthm mulcat-bvecp
  (implies (and (>= p (* l n))
                (case-split (integerp p))
                (case-split (natp l)))
           (bvecp (mulcat l n x) p)))


;; mod-

;finish this section (will have to change comp2-inv?)

#|
(defthm mod--nonnegative-integer-type
  (and (integerp (mod- l n x))
       (<= 0 (mod- l n x)))
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
           (bvecp (mod- x y n) n)))
|#

;; encode

(defthm encode-nonnegative-integer-type
  (and (integerp (encode x n))
       (<= 0 (encode x n)))
  :rule-classes (:type-prescription))

;this rule is no better than encode-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription encode)))

(local (include-book "../support/encode"))

(defthm encode-bvecp-old
  (implies (and (<= (+ 1 (expo n)) k)
                (case-split (integerp k)))
           (bvecp (encode x n) k)))


;; decode

(local (include-book "../support/decode"))

(defthm decode-nonnegative-integer-type
  (and (integerp (decode x n))
       (<= 0 (decode x n)))
  :rule-classes (:type-prescription))

;this rule is no better than decode-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription decode)))

(defthm decode-bvecp
  (implies (and (<= n k)
                (case-split (integerp k))
                )
           (bvecp (decode x n) k)))




(DEFTHM UNKNOWN-upper-bound
  (< (UNKNOWN KEY SIZE N) (expt 2 size))
  :RULE-CLASSES
  (:REWRITE (:linear :trigger-terms ((UNKNOWN KEY SIZE N)))))


; land

(defthm land-nonnegative-integer-type
  (and (integerp (land x y n))
       (<= 0 (land x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription land) is no better than land-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-land)))

;drop this if we plan to keep natp enabled?
(defthm land-natp
  (natp (land x y n)))

(defthm land-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (land x y n) k)))

;; lior


(defthm lior-nonnegative-integer-type
  (and (integerp (lior x y n))
       (<= 0 (lior x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription lior) is no better than lior-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-lior)))

;drop this if we plan to keep natp enabled?
(defthm lior-natp
  (natp (lior x y n)))

(defthm lior-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lior x y n) k)))

;; lxor


(defthm lxor-nonnegative-integer-type
  (and (integerp (lxor x y n))
       (<= 0 (lxor x y n)))
  :rule-classes (:type-prescription))

;(:type-prescription lxor) is no better than lxor-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription binary-lxor)))

;drop this if we plan to keep natp enabled?
(defthm lxor-natp
  (natp (lxor x y n)))

(defthm lxor-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lxor x y n) k)))

;; cat


(defthm cat-nonnegative-integer-type
  (and (integerp (CAT X m Y N))
       (<= 0 (CAT X m Y N)))
  :rule-classes (:type-prescription)
  )

;this rule is no better than cat-nonnegative-integer-type and might be worse
(in-theory (disable (:type-prescription binary-cat)))

;just a rewrite rule
(defthm cat-natp
  (natp (cat x m y n))
  :hints (("Goal" :use ((:instance cat-nonnegative-integer-type)))))

(defthm cat-bvecp
  (implies (and (<= (+ m n) k)
                (case-split (integerp k)))
           (bvecp (cat x m y n) k)))

;would like to remove some of this stuff

;;;;;;;;;;;;;;;;;;; other helpful lemmas

(defthm nonneg-+
  (implies (and (<= 0 x)
                (<= 0 y))
           (<= 0 (+ x y))))

(defthm integerp-+
  (implies (and (integerp x)
                (integerp y))
           (integerp (+ x y))))

#|
;should be a forward-chaining rule?
(defthm bvecp-implies-natp
  (implies (bvecp x k)
           (and (integerp x)
                (>= x 0))))

;free var
;should be a forward-chaining rule?
(defthm bvecp-implies-rationalp
  (implies (bvecp x k)
           (rationalp x)))
|#

;why do we have this?
(defthm unknown-upper-bound
  (< (unknown key size n) (expt 2 size))
  :rule-classes
  (:rewrite (:linear :trigger-terms ((unknown key size n)))))

;(local (in-theory (enable floor-fl)))

;These next two are for the bus unit bvecp lemmas:

;could use (local (in-theory (enable expt-compare-with-double)))
;remove?

(defthm bits-does-nothing-hack
  (implies (and (< x (expt 2 i))
                (integerp x)
                (<= 0 x)
                (integerp i)
                (<= 0 i))
           (equal (BITS (* 2 x) i 0)
                  (* 2 x)))
  :hints (("Goal" :in-theory (enable expt-2-reduce-leading-constant
                                     bits))))

;remove?
(defthm bits-does-nothing-hack-2
  (implies (and (< x (expt 2 i))
                (integerp x)
                (<= 0 x)
                (integerp i)
                (<= 0 i))
           (equal (bits (+ 1 (* 2 x)) i 0)
                  (+ 1 (* 2 x))))
  :hints (("Goal" :in-theory (enable expt-2-reduce-leading-constant
                                     bits))))


;is this one too expensive?
(defthm bvecp-def
  (implies (and (< x (expt 2 k))
                (integerp x)
                (<= 0 x)
                )
           (bvecp x k))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil nil)))
  :hints (("Goal" :in-theory (e/d (bvecp) ()))))


; The two events following the next local include-book were added by Matt
; K. June 2004: Some proofs require calls of expt to be evaluated, but some
; calls are just too large (2^2^n for large n).  So we use the following hack,
; which allows calls of 2^n for n<130 to be evaluated even when the
; executable-counterpart of expt is disabled.  The use of 130 is somewhat
; arbitrary, chosen in the hope that it suffices for relieving of hyps related
; to widths of bit vectors


(defun expt-exec (r i)
  (declare (xargs :guard
                  (and (acl2-numberp r)
                       (integerp i)
                       (not (and (eql r 0) (< i 0))))))
  (mbe :logic (hide (expt r i)) ; hide may avoid potential loop
       :exec (expt r i)))

(defthm expt-2-evaluator
  (implies (syntaxp (and (quotep n)
                         (natp (cadr n))
                         (< (cadr n) 130)
                         ))
           (equal (expt 2 n)
                  (expt-exec 2 n))))


;remove these?


;;;;;;;;;;;;;;;;;;; We can probably eliminate the following if the translator
;;;;;;;;;;;;;;;;;;; would always use 0 instead of nil when case/casex
;;;;;;;;;;;;;;;;;;; statements have no default.

;maybe leave this one?

#|
(defthm bvecp-1-values
  (implies (and (bvecp x 1)
                (not (equal x 0)))
           (equal (equal x 1) t)))

(defthm bvecp-2-values
  (implies (and (bvecp x 2)
                (not (equal x 2))
                (not (equal x 1))
                (not (equal x 0)))
           (equal (equal x 3) t)))

(defthm bvecp-3-values
  (implies (and (bvecp x 3)
                (not (equal x 6))
                (not (equal x 5))
                (not (equal x 4))
                (not (equal x 3))
                (not (equal x 2))
                (not (equal x 1))
                (not (equal x 0)))
           (equal (equal x 7) t)))

(defthm bvecp-4-values
  (implies (and (bvecp x 4)
                (not (equal x 14))
                (not (equal x 13))
                (not (equal x 12))
                (not (equal x 11))
                (not (equal x 10))
                (not (equal x 9))
                (not (equal x 8))
                (not (equal x 7))
                (not (equal x 6))
                (not (equal x 5))
                (not (equal x 4))
                (not (equal x 3))
                (not (equal x 2))
                (not (equal x 1))
                (not (equal x 0)))
           (equal (equal x 15) t)))

(defthm bvecp-5-values
  (implies (and (bvecp x 5)
                (not (equal x 30))
                (not (equal x 29))
                (not (equal x 28))
                (not (equal x 27))
                (not (equal x 26))
                (not (equal x 25))
                (not (equal x 24))
                (not (equal x 23))
                (not (equal x 22))
                (not (equal x 21))
                (not (equal x 20))
                (not (equal x 19))
                (not (equal x 18))
                (not (equal x 17))
                (not (equal x 16))
                (not (equal x 15))
                (not (equal x 14))
                (not (equal x 13))
                (not (equal x 12))
                (not (equal x 11))
                (not (equal x 14))
                (not (equal x 13))
                (not (equal x 12))
                (not (equal x 11))
                (not (equal x 10))
                (not (equal x 9))
                (not (equal x 8))
                (not (equal x 7))
                (not (equal x 6))
                (not (equal x 5))
                (not (equal x 4))
                (not (equal x 3))
                (not (equal x 2))
                (not (equal x 1))
                (not (equal x 0)))
           (equal (equal x 31) t)))
|#

#|
;can remove these two?
(defthm natp-*
  (implies (and (integerp x)
                (>= x 0)
                (integerp y)
                (>= y 0))
           (and (integerp (* x y))
                (>= (* x y) 0))))

(defthm natp-+
  (implies (and (integerp x)
                (>= x 0)
                (integerp y)
                (>= y 0))
           (and (integerp (+ x y))
                (>= (+ x y) 0))))
|#

#|
;drop?
(defthm bits-bvecp-fw
  (implies (equal n (- (1+ i) j))
           (bvecp (bits x i j) n))
  :rule-classes
  ((:forward-chaining :trigger-terms ((bits x i j)))))
|#

