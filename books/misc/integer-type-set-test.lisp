; These events were initially contributed by Robert Krug and incorporated
; after ACL2 Version  3.2.1.  See the "Essay on Type-set Deductions for
; Integerp" in the ACL2 sources for a discussion of a change to ACL2 that
; allowed for the proofs of the theorems below, where they had previously
; failed.

(in-package "ACL2")

(encapsulate
 ((foo (x) t))
 (local (defun foo (x) x))

 (defthm foo-thm
   (implies x
            (foo x))))

; Make sure we use only type-reasoning to relieve foo-thm's
; hypothesis.

(set-backchain-limit 0)

(defthm lemma-1
 (implies (and (rationalp x)
               (integerp (* 1/2 x)))
          (foo (integerp x)))
 :rule-classes nil)

(defthm lemma-2
 (implies (and (rationalp x)
               (integerp (* 2 x)))
          (foo (integerp (* 4 x))))
 :rule-classes nil)

(defthm lemma-3
 (implies (and (rationalp x)
               (integerp (* 2 x)))
          (foo (integerp (+ -1 (* 4 x)))))
 :rule-classes nil)

(defthm lemma-4
 (implies (and (rationalp x)
               (integerp (+ 1 x)))
          (foo (integerp (+ 2 x))))
 :rule-classes nil)

(defthm lemma-5
 (implies (and (rationalp x)
               (integerp (+ 1 x)))
          (foo (integerp x)))
 :rule-classes nil)

(defthm lemma-6
 (implies (and (rationalp x)
               (integerp (+ -1/2 x)))
          (foo (integerp (+ 1/2 x))))
 :rule-classes nil)

(defthm lemma-7
 (implies (and (rationalp x)
               (integerp (* 2 x)))
          (foo (not (integerp (+ 1/2 (* 4 x))))))
 :rule-classes nil)

(defun not-integerp (x)
  (not (integerp x)))

(defthm not-integerp-implies-not-integerp
  (implies (not (integerp x))
           (not-integerp x)))

(in-theory (disable not-integerp))

(defthm lemma-8
 (implies (and (rationalp x)
               (integerp (+ 1/2 x)))
          (foo (not-integerp x)))
 :rule-classes nil)
