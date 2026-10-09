; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 51: CNF-DNF's NOT case (tau.lisp:8755) flips CNFP as well as SIGN:
;     ((eq (ffn-symb term) 'NOT) (cnf-dnf (not sign) (fargn term 1) (not cnfp)))
; The contract is "the result, read under CNFP, is equivalent to SIGN/TERM".
; Flipping CNFP breaks it: the callee builds its answer for the OTHER reading
; while the caller reads under its own CNFP.  For the AND/OR branches this error
; cancels with the combinator bug of Finding 50, which is why the NOT case looks
; consistent.  For the FQUOTEP branch (tau.lisp:8744-8753), which encodes
; TRUE/FALSE from CNFP ALONE, the two errors do NOT cancel: a TRUE subformula is
; read as FALSE and vice versa.
;
; Measured: (cnf-dnf t '(NOT (IF (PP1 V) 'T 'NIL)) nil) = (((NOT (PP1 V))) NIL)
; -- the second disjunct is the EMPTY hypothesis list, i.e. "no hypotheses
; needed", which is a weakening.  split-on-conjoined-disjunctions-in-hyps-of-pairs
; then stores the UNCONDITIONAL signature rule (INTEGERP (FF1 V)) alongside the
; conditional one that was proved.
;
; DISTINCT FROM FINDING 50, and this matters for the fix: repairing only the
; combinator choice (tau.lisp:8769-8791) leaves this; repairing only the NOT flip
; leaves Finding 50.  Every weakening found by exhaustive search over
; propositional IF/NOT terms of depth <= 2 requires a literal 'T or 'NIL in an IF
; branch -- exactly what the AND/OR/IMPLIES macros expand to.
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour.  RED while the defect is
; present, GREEN when cnf-dnf is fixed.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(tau-status :system t)

(defun pp1 (v) (if (consp v) t nil))
(defun ff1 (v) (if (consp v) "oops" 0))

; A TRUE theorem: if v is not a cons then (ff1 v) is 0, an integer.
(defthm ff1-sig
  (implies (not (if (pp1 v) t nil))
           (integerp (ff1 v)))
  :rule-classes :tau-system)

; THE DEFECT: tau stores the hypothesis-free version too, so it proves this
; false formula alone.  (ff1 '(1)) = "oops", which is not an integer.
(must-fail
 (defthm bad
   (integerp (ff1 v))
   :hints (("Goal" :in-theory (disable pp1 ff1 (:e pp1) (:e ff1) (:t ff1))))
   :rule-classes nil))

; CONTROL: the conditional form that WAS proved must remain usable, so the fix
; cannot be "stop mining hypotheses through NOT".
(defthm honest-use
  (implies (not (if (pp1 v) t nil)) (integerp (ff1 v)))
  :hints (("Goal" :in-theory (disable pp1 ff1 (:e pp1) (:e ff1) (:t ff1))))
  :rule-classes nil)
