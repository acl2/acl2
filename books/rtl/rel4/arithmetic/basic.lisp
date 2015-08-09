;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "ACL2")

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(include-book "fp2")
(local (include-book "even-odd"))

;;; natp ;;;
;Currently, we plan to leave natp enabled...
(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defthm natp-compound-recognizer
  (equal (natp x)
         (and (integerp x)
              (<= 0 x)))
  :rule-classes :compound-recognizer)

; The fpaf3a proof of far-exp-low-lemma-1 in far.lisp requires the
; following to be a :rewrite rule, not just a :type-prescription rule.
; Let's make most or all of our :type-prescription rules into :rewrite
; rules as well.
(defthmd natp+
    (implies (and (natp x) (natp y))
	     (natp (+ x y))))

;move
(defthmd natp*
    (implies (and (natp x) (natp y))
	     (natp (* x y))))



;abs
;Currently, we plan to leave abs enabled, but here are some rules about it:

(defthm abs-nonnegative-acl2-numberp-type
  (implies (case-split (acl2-numberp x))
           (and (<= 0 (abs x))
                (acl2-numberp (abs x))))
  :rule-classes (:TYPE-PRESCRIPTION))

(defthm abs-nonnegative-rationalp-type
  (implies (case-split (rationalp x))
           (and (<= 0 (abs x))
                (rationalp (abs x))))
  :rule-classes (:TYPE-PRESCRIPTION))

(defthm abs-nonnegative-integerp-type
  (implies (integerp x)
           (and (<= 0 (abs x))
                (rationalp (abs x))))
  :rule-classes (:TYPE-PRESCRIPTION))

(defthm abs-nonnegative
  (<= 0 (abs x)))




(local (include-book "fl"))

(defthm fl-def-linear
  (implies (case-split (rationalp x))
           (and (<= (fl x) x)
                (< x (1+ (fl x)))))
  :rule-classes :linear)

;(in-theory (disable a13)) ;the same rule as fl-def-linear!

;bad? free var.
(defthm fl-monotone-linear
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y))
           (<= (fl x) (fl y)))
  :rule-classes :linear)

(defthm n<=fl-linear
    (implies (and (<= n x)
		  (rationalp x)
		  (integerp n))
	     (<= n (fl x)))
  :rule-classes :linear)


;may need to disable? <-- why did I write that? expensive backchaining?
(defthm fl+int-rewrite
    (implies (and (integerp n)
		  (rationalp x))
	     (equal (fl (+ x n)) (+ (fl x) n))))


;from fl.lisp
(defthm fl/int-rewrite
  (implies (and (integerp n)
                (<= 0 n) ;can't gen?
                (rationalp x))
           (equal (fl (/ (fl x) n))
                  (fl (/ x n))))
  :hints (("Goal" :use ((:instance fl/int-1)
			(:instance fl/int-2)))))


;needed?
(defthm fl-integer-type
  (integerp (fl x))
  :rule-classes (:type-prescription))

;this rule is no better than fl-integer-type and might be worse:
(in-theory (disable (:type-prescription fl)))

(defthm fl-int
    (implies (integerp x)
	     (equal (fl x) x)))

(encapsulate
 ()
 (local (include-book "fl"))
 (defthm fl-integerp
   (equal (equal (fl x) x)
          (integerp x))))

(defthm fl-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (<= n x)
		  (< x (1+ n)))
	     (equal (fl x) n))
  :rule-classes ())



(encapsulate
 ()
 (local (include-book "expt"))

 (defthm expt-2-positive-rational-type
   (and (rationalp (expt 2 i))
        (< 0 (expt 2 i)))
   :rule-classes (:rewrite (:type-prescription :typed-term (expt 2 i))))

 (defthm expt-2-positive-integer-type
   (implies (<= 0 i)
            (and (integerp (expt 2 i))
                 (< 0 (expt 2 i))))
   :rule-classes (:type-prescription))

;the rewrite rule counterpart to expt-2-positive-integer-type
 (defthm expt-2-integerp
   (implies (<= 0 i)
            (integerp (expt 2 i))))



; (in-theory (disable a14)) ;the rules above are better than this one for (expt 2 i)


 (defthm expt-2-type-linear
   (implies (<= 0 i)
            (<= 1 (expt 2 i)))
   :rule-classes ((:linear :trigger-terms ((expt 2 i)))))

 (defthmd expt-split
   (implies (and (integerp i)
                 (integerp j)
                 (case-split (acl2-numberp r)) ;(integerp r)
                 (case-split (not (equal r 0)))
                 )
            (equal (expt r (+ i j))
                   (* (expt r i)
                      (expt r j)))))

 (theory-invariant (incompatible (:rewrite expt-split)
                                 (:definition a15))
                   :key expt-split-invariant)

 (defthmd expt-weak-monotone
   (implies (and (integerp n)
                 (integerp m))
            (equal (<= (expt 2 n) (expt 2 m))
                   (<= n m))))

 (defthmd expt-weak-monotone-linear
   (implies (and (<= n m)
                 (case-split (integerp n))
                 (case-split (integerp m)))
            (<= (expt 2 n) (expt 2 m)))
  :rule-classes ((:linear :match-free :all)))

 (defthmd expt-strong-monotone
   (implies (and (integerp n)
                 (integerp m))
            (equal (< (expt 2 n) (expt 2 m))
                   (< n m))))
 (defthmd expt-strong-monotone-linear
   (implies (and (< n m)
                 (case-split (integerp n))
                 (case-split (integerp m))
                 )
            (< (expt 2 n) (expt 2 m)))
  :rule-classes ((:linear :match-free :all)))

 (defthmd a15
   (implies (and (rationalp i)
                 (not (equal i 0))
                 (integerp j1)
                 (integerp j2))
            (and (equal (* (expt i j1) (expt i j2))
                        (expt i (+ j1 j2)))
                 (equal (* (expt i j1) (* (expt i j2) x))
                        (* (expt i (+ j1 j2)) x))))

   )

 )

; The next two events were added by Matt K. June 2004: Some proofs require
; calls of expt to be evaluated, but some calls are just too large (2^2^n for
; large n).  So we use the following hack, which allows calls of 2^n for n<130
; to be evaluated even when the executable-counterpart of expt is disabled.
; The use of 130 is somewhat arbitrary, chosen in the hope that it suffices for
; relieving of hyps related to widths of bit vectors

(defun expt-exec (r i)
  (declare (xargs :guard
                  (and (acl2-numberp r)
                       (integerp i)
                       (not (and (eql r 0) (< i 0))))
                  :guard-hints (("Goal" :expand (hide (expt r i))))))
  (mbe :logic (hide (expt r i)) ; hide may avoid potential loop
       :exec (expt r i)))

(defthm expt-2-evaluator
  (implies (syntaxp (and (quotep n)
                         (natp (cadr n))
                         (< (cadr n) 130)
                         ))
           (equal (expt 2 n)
                  (expt-exec 2 n)))
  :hints (("Goal" :expand ((hide (expt 2 n))))))

;weakly?
;cases for other signs?
(defthm *-doubly-monotonic
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp a)
                (rationalp b)
                (<= 0 x)
                (<= 0 y)
                (<= 0 a)
                (<= 0 b)
                (<= x y)
                (<= a b))
           (<= (* x a) (* y b)))
  :rule-classes ())

(defund fl-half (x)
;  (declare (xargs :guard (real/rationalp x)))
  (1- (fl (/ (1+ x) 2))))


(defthm fl-half-lemma
    (implies (and (integerp x)
		  (not (integerp (/ x 2)))) ;if x is odd, ...
	     (= x (1+ (* 2 (fl-half x)))))
  :rule-classes ()
  :hints (("goal" :in-theory (e/d (fl-half) (fl-int))
           :use ((:instance x-or-x/2)
                 (:instance fl-int (x (/ (1+ x) 2)))))))



