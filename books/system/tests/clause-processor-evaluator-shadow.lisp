; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 48: destructure-clause-processor-rule (defthm.lisp:7703) destructures a
; :clause-processor correctness theorem with TWO NESTED case-match forms that each
; bind the pattern variable EV:
;
;   (case-match term
;     (('IMPLIES hyp (ev ('DISJOIN clause) alist))      <- ev := CONCLUSION's function
;       ...
;       (case-match hyps
;         (((ev ('CONJOIN-CLAUSES cl-result) &))        <- ev := HYPOTHESIS's function
;
; case-match ties repeated pattern variables only WITHIN one pattern; across two
; forms each emits a fresh let, so the inner binding lexically shadows the outer.
; Every mv return passes the INNER ev, so that is what chk-evaluator and
; chk-evaluator-use-in-rule validate.  The function applied to (DISJOIN clause) in
; the CONCLUSION is never validated at all -- not as an evaluator, not even for
; symbolp.  It may therefore be an arbitrary 2-argument function, e.g. one that is
; identically T, which makes the "correctness theorem" a tautology while the clause
; processor is installed as VERIFIED and may return any clause list, including NIL
; (= "goal proved").
;
; :META is NOT affected: interpret-term-as-meta-rule (defthm.lisp:5235) puts both
; evaluator occurrences in ONE pattern, so case-match emits an equality test.
;
; FIX: tie the two occurrences.  Note remove-meta-extract-global-hyps is passed the
; OUTER ev while the hypothesis is matched against the inner one -- tying them makes
; that moot, but a partial fix adding only a symbolp check would leave it.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defevaluator evl evl-lst ((binary-+ x y)))
(defun fake-ev (x a) (declare (ignore x a) (xargs :guard t)) t)   ; identically T
(defun my-cp (cl) (declare (ignore cl) (xargs :guard t)) nil)     ; discharges everything

; THE DEFECT: fake-ev sits in the CONCLUSION and is never checked.
(must-fail
 (local (defthm bogus-cp
          (implies (evl (conjoin-clauses (my-cp cl)) a)
                   (fake-ev (disjoin cl) a))
          :rule-classes :clause-processor)))

; CONTROL 1 -- the same bogus function in the HYPOTHESIS position IS checked, and
; must stay rejected: "FAKE-EV, playing the role of an evaluator ... does not pass
; the test for an evaluator."  This pins the asymmetry rather than assuming it.
(must-fail
 (local (defthm swapped-cp
          (implies (fake-ev (conjoin-clauses (my-cp cl)) a)
                   (evl (disjoin cl) a))
          :rule-classes :clause-processor)))

; CONTROL 2 -- an HONEST clause processor must still be admissible after the fix,
; so the repair does not simply reject the rule class.  The identity processor is
; trivially correct.
(defun id-cp (cl) (declare (xargs :guard t)) (list cl))
(defthm honest-cp
  (implies (evl (conjoin-clauses (id-cp cl)) a)
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)
