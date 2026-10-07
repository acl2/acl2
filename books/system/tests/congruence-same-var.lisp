; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

; This book is based on an example produced by Claude and passed along by Eric
; Smith.  It illustrates a soundness bug fixed before ACL2 Version 8.8.  The
; bug was in interpret-term-as-congruence-rule (defthm.lisp), which did not
; require the two variables in the hypothesis of a :congruence rule to be
; distinct.  A formula such as (implies (e x x) (equal (f x) (f x))) is
; trivially true.  It failed the check for a classic congruence rule, but was
; then accepted as a shallow patterned congruence rule, with the same effect as
; the genuine congruence (implies (e x y) (equal (f x) (f y))), which need not
; be true.  As shown below, this led to a proof of nil.  Such rules are now
; rejected.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; An arbitrary equivalence relation.
(defun e (x y)
  (equal (fix x) (fix y)))

(defequiv e)

; F does not respect E: (f '(1 . 2)) = 1, but (f 0) = 0.
(defun f (x)
  (if (consp x) 1 0))

; Previously this was accepted as a congruence rule stating that EQUAL is
; preserved by E in the argument of F.
(must-fail
 (defthm e-implies-equal-f-same-var
   (implies (e x x)
            (equal (f x) (f x)))
   :rule-classes :congruence))

; The formula itself is still a theorem; it just isn't a congruence rule.
(defthm e-implies-equal-f-same-var-as-theorem
  (implies (e x x)
           (equal (f x) (f x)))
  :rule-classes nil)

; Previously, given (e x 0), the congruence rule above allowed x to be
; rewritten to 0 within (f x), yielding (f 0) = 0.  So the following false
; formula (consider x = '(1 . 2)) was provable, and nil followed.  E is disabled
; so that the hypothesis is not expanded.
(must-fail
 (defthm f-when-e-0
   (implies (e x 0)
            (equal (f x) 0))
   :hints (("Goal" :in-theory (disable e)))
   :rule-classes nil))

(must-fail
 (defthm contradiction
   nil
   :hints (("Goal" :use (:instance f-when-e-0 (x '(1 . 2)))))
   :rule-classes nil))

; A genuine patterned congruence rule, with distinct variables, is still
; accepted.
(defun g (a x)
  (if (equal a 3) (fix x) x))

(defthm e-implies-equal-g-3
  (implies (e x y)
           (equal (g 3 x) (g 3 y)))
  :rule-classes :congruence)
