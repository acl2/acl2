; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 52: tau-term's (MV-NTH 'i (fn a1 ... ak)) branch relieves a form-2
; signature rule's DEPENDENT HYPOTHESES against the wrong argument list.
;
; tau.lisp:11643 passes (fargs term) as the ACTUALS, where TERM is the MV-NTH
; call -- so the actuals are ('i (fn a1 ... ak)).  The sibling binding two lines
; above (tau.lisp:11635) correctly uses (fargs (fargn term 2)) for
; ACTUAL-TAU-LST.  A form-2 signature-rule's :VARS are FN's formals, and
; relieve-dependent-hyps (tau.lisp:11891) does (subcor-var formals actuals hyp),
; so formal #0 is bound to the QUOTED MV-NTH INDEX, formal #1 to the whole inner
; (fn ...) call, and formals #2 and beyond to NIL.
;
; Decisive measurement, with the rule at mv-nth index k and dependent hypothesis
; (< (+ v 0) k): at k=1 the instantiated hypothesis (< (+ '1 '0) '1) is FALSE and
; the rule correctly does not fire; at k=2 it is (< (+ '1 '0) '2), TRUE, and the
; rule fires unconditionally.  The hypothesis is being evaluated on the index.
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(tau-status :system t)

; (fn2 v) = (list (if (< (+ v 0) 1) 0 "oops")), so element 0 is an integer only
; when (< (+ v 0) 1).  The rule below is that true theorem.
(defun fn2 (v) (cons (if (< (+ v 0) 1) 0 "oops") nil))

(defthm fn2-sig
  (implies (< (+ v 0) 1)
           (integerp (mv-nth 0 (fn2 v))))
  :rule-classes :tau-system)

; THE DEFECT: the dependent hypothesis is relieved against '0 (the index)
; instead of V, so tau proves the unconditional formula.  At v = 5 the element
; is "oops".
(must-fail
 (defthm bad
   (integerp (mv-nth 0 (fn2 v)))
   :hints (("Goal" :in-theory (disable fn2 (:e fn2) mv-nth (:e mv-nth) (:t fn2))))
   :rule-classes nil))

; CONTROL: the conditional form must stay usable after the fix.
(defthm honest-use
  (implies (< (+ v 0) 1) (integerp (mv-nth 0 (fn2 v))))
  :hints (("Goal" :in-theory (disable fn2 (:e fn2) mv-nth (:e mv-nth) (:t fn2))))
  :rule-classes nil)
