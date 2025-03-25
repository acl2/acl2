; Copyright (C) 2024, Matt Kaufmann and J Strother Moore
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book illustrates the power of partial-encapsulate, showing how it is
; used in the implementation of floating-point operations in ACL2.

; Warning: This book takes advantage of a trust tag to produce a proof of nil!

(in-package "ACL2")

(include-book "tools/include-raw" :dir :system)

(partial-encapsulate
 (((constrained-to-fp *) => *
   :formals (x)
   :guard (rationalp x)))
 nil ; supporters
 (local (defun constrained-to-fp (x)
          (declare (ignore x))
          0))
 (defthm rationalp-constrained-to-fp
   (rationalp (constrained-to-fp x))
   :rule-classes :type-prescription)
 (defthm constrained-to-fp-idempotent
   (equal (constrained-to-fp (constrained-to-fp x))
          (constrained-to-fp x)))
 (defthm constrained-to-fp-minus
   (implies (and (rationalp x)
                 (equal (constrained-to-fp x) x))
            (equal (constrained-to-fp (- x))
                   (- x))))
 (defthm constrained-to-fp-default
   (implies (not (rationalp x))
            (equal (constrained-to-fp x) 0)))
 (defthm constrained-to-fp-0
   (equal (constrained-to-fp 0) 0))
 (defthm constrained-to-fp-monotonicity
   (implies (and (<= x y)
                 (rationalp x)
                 (rationalp y))
            (<= (constrained-to-fp x)
                (constrained-to-fp y)))
   :rule-classes (:linear :rewrite)))

(defun to-fp (x)
  (declare (xargs :guard (rationalp x)))
  (constrained-to-fp x))

(defun fpp (x)
  (declare (xargs :guard t))
  (and (rationalp x) (= (to-fp x) x)))

(partial-encapsulate
 (((constrained-fp-sqrt *) => *
   :formals (x)
   :guard (and (rationalp x)
               (<= 0 x))))
 nil ; supporters
 (local (defun constrained-fp-sqrt (x)
          (declare (ignore x))
          0))
 (defthm fpp-constrained-fp-sqrt-fn
   (fpp (constrained-fp-sqrt x))))

(defthm rationalp-constrained-fp-sqrt-fn
  (rationalp (constrained-fp-sqrt x))
  :hints (("Goal"
           :use fpp-constrained-fp-sqrt-fn
           :in-theory (disable fpp-constrained-fp-sqrt-fn)))
  :rule-classes :type-prescription)

(defun fp-sqrt (x)
  (declare (xargs :guard (and (rationalp x)
                              (<= 0 x))))
  (constrained-fp-sqrt x))

(partial-encapsulate
 (((fp-round *)
   => *
   :formals (x)
   :guard (rationalp x)))
 nil ; supporters
 (local (defun fp-round (x)
          (to-fp x)))
 (defthm rationalp-fp-round
   (rationalp (fp-round x))
   :rule-classes :type-prescription)
 (defthm fpp-fp-round (fpp (fp-round r)))
 (defthm fp-round-is-identity-for-fpp
   (implies (fpp r)
            (equal (fp-round r) r)))
 (defthm fp-round-monotonicity
   (implies (and (<= x y)
                 (rationalp x)
                 (rationalp y))
            (<= (fp-round x) (fp-round y)))
   :rule-classes (:linear :rewrite)))

(defthm fp-round-idempotent

; This follows from fp-round-is-identity-for-fpp together with fpp-fp-round.

  (equal (fp-round (fp-round x))
         (fp-round x)))

(defun fp+ (x y)
  (declare (xargs :guard (and (fpp x) (fpp y))))
  (fp-round (+ x y)))

(defttag :fp)

(include-raw "fp-raw.lsp")

(defttag nil)

(defmacro assert-thm (x)

; We check not only that x evaluates to a non-nil value but that x is provable,
; presumably by execution.  The latter is worth checking because not all
; top-level executions can be done during proofs, notably, when attachments are
; used.

  `(progn (assert-event ,x)
          (thm ,x)))

(assert-thm (equal (to-fp 1/4) 1/4))
(assert-thm (fpp 1/4))

; This happens to be true in all Lisps that can host ACL2:
(assert-thm (equal (to-fp 1/3)
                   6004799503160661/18014398509481984))
(assert-thm (let* ((fp (to-fp 1/3))
                   (diff (abs (- 1/3 fp))))
              (and (< 0 diff)
                   (< diff (expt 10 -10))))) ; 10^(-10) is somewhat arbitrary
(assert-thm (equal (to-fp 1/3)
                   (to-fp (to-fp 1/3))))
; Fails in GCL 2.6.14:
#+(or (not gcl) gcl-2.7.0+)
(assert-thm (not (fpp 1/3)))

; Rounding the exact square root of 4 is rounding 2, which is 2.
(assert-thm (equal (fp-sqrt 4) 2))

(assert-thm (< (abs (- (expt (fp-sqrt 5) 2) 5))
               (expt 10 -10)))

(assert-thm (equal (fp+ 1/4 5/4) 3/2))

(assert-thm (< (abs (- (fp+ (to-fp 1/3) (to-fp 2/3))
                       1)) ; difference might or might not be 0
               (expt 10 -10))) ; 10^(-10) is somewhat arbitrary

; Below are some proofs of nil.  Explanations are somewhat technical.

; The following proof of nil illustrates that *1* functions (see :DOC
; evaluation) need to coerce double-float results to rationals, something that
; is done in the ACL2 implementation of dfs.
(local
 (encapsulate
   ()
   (local (defun f1 (x)
            (declare (xargs :guard (rationalp x)))
            (to-fp x)))
   (local (defthm not-rationalp-f1-3
            (not (rationalp (f1 3)))
            :rule-classes nil))
   (local (defthm rationalp-f1-3
            (rationalp (f1 3))
            :hints (("Goal" :in-theory (disable (:e f1) (:e to-fp))))
            :rule-classes nil))
   (defthm nil-is-true-1
     nil
     :hints (("Goal" :use (not-rationalp-f1-3 rationalp-f1-3)))
     :rule-classes nil)))

; This proof of nil illustrates why ACL2 tracks dfs much as it tracks stobjs,
; so that for example a double-float isn't given as an argument to EQUAL.
; (Perhaps this issue could instead be handled by adding a double-float
; datatype to ACL2 and defining EQUAL to return nil if exactly one argument is
; a double-float, but the prover relies heavily on EQUAL being defined as true
; equality.  So then we might distinguish between ACL2::EQUAL and
; COMMON-LISP::EQUAL.  But that would probably present many opportunities for
; bugs and might well require major changes to the community books.)
(local
 (encapsulate
   ()
   (local (defun f2 ()
            (declare (xargs :guard t))
            (equal 1 (to-fp 1))))
   (local (defthm f2-false ; (to-fp 1) is 1.0 in raw Lisp, not the integer 1
            (not (f2))
            :rule-classes nil))
   (local (defthm f2-true ; logically, (to-fp 1) is 1
            (f2)
            :hints (("Goal" :in-theory (disable (:e f2))))
            :rule-classes nil))
   (defthm nil-is-true-2
     nil
     :hints (("Goal" :use (f2-false f2-true)))
     :rule-classes nil)))
