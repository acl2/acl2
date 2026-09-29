; Copyright (C) 2026, ember arlynx
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Regression test for GitHub issue #2055.

; A :linear rule with :trigger-terms whose conclusion produces no polynomial,
; such as (integerp (f x)), was admitted: chk-acceptable-linear-rule2
; (defthm.lisp) skipped the linearization of the conclusion, and with it the
; "No :LINEAR rule can be generated" check, whenever :trigger-terms was
; supplied.  The first use of such a rule in linear arithmetic then faulted the
; host Lisp: add-linear-lemma (rewrite.lisp) returned the marker :null-lst,
; which add-linear-lemma-finish uses to say "another try is coming", as the new
; pot-lst, and the next function to traverse it dereferenced a symbol as a
; list.  Both are fixed before ACL2 Version 8.8: the rule is refused at
; admission, as it always was without :trigger-terms, and :null-lst can no
; longer escape from add-linear-lemma.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun g (x)
  (nfix x))

; The proof of each theorem below is trivial.  What is tested is the
; rule-class check, which is made before the proof is attempted.

; A conclusion that produces no polynomial has always been refused without
; :trigger-terms ...
(must-fail
 (defthm integerp-g-plain
   (integerp (g x))
   :rule-classes :linear))

; ... and is now refused with :trigger-terms as well.  Before the fix this
; event was admitted and a subsequent (thm (< -1 (g a))) faulted the Lisp.
(must-fail
 (defthm integerp-g-trigger
   (integerp (g x))
   :rule-classes ((:linear :trigger-terms ((g x))))))

; NATP is not opened by expand-inequality-fncall, so (natp (g x)) produces no
; polynomial either; it is refused both ways.
(must-fail
 (defthm natp-g-plain
   (natp (g x))
   :rule-classes :linear))

(must-fail
 (defthm natp-g-trigger
   (natp (g x))
   :rule-classes ((:linear :trigger-terms ((g x))))))

; Each conjunct of the corollary generates its own rule, so one conjunct that
; produces no polynomial makes the whole event illegal, with or without
; :trigger-terms.  This is the form in which the issue was found.
(must-fail
 (defthm g-bounds-trigger
   (and (<= 0 (g x))
        (natp (g x)))
   :rule-classes ((:linear :trigger-terms ((g x))))))

; An inequality conclusion is accepted both ways.
(defthm g-nonneg-plain
  (<= 0 (g x))
  :rule-classes :linear)

(defthm g-nonneg-trigger
  (<= 0 (g x))
  :rule-classes ((:linear :trigger-terms ((g x)))))

; The workaround from the report: the type fact as a :type-prescription rule
; and the inequality as a :linear rule.
(defthm natp-g-tp
  (natp (g x))
  :rule-classes :type-prescription)

; The :trigger-terms rule is used.  With the definition and type-prescription
; of g, the rules above other than g-nonneg-trigger, and tau all disabled,
; linear arithmetic with g-nonneg-trigger is what proves this.
(in-theory (disable g (:type-prescription g) natp-g-tp g-nonneg-plain
                    (:executable-counterpart tau-system)))

(defthm g-above-minus-one
  (< -1 (g a))
  :rule-classes nil)
