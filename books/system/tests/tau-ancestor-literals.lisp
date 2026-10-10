; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 53: remove-ancestor-literals-from-pairs drops hypotheses it is not
; entitled to drop.  FOUR PLAIN DEFUNS -- no rule class, no hint beyond
; in-theory, no :tau-system corollary.  Any user running with
; (tau-status :system t) can hit this by accident, which makes it the most
; reachable finding in this register.
;
; tau.lisp:9351 (subsumes-but-for-one-negation) has the clause
;     ((member-equal (car hyps2) ancestor-lits)
;      (subsumes-but-for-one-negation hyps1 (cdr hyps2) ancestor-lits))
; and tau.lisp:9597 (remove-ancestor-literals-from-pairs1) does
;     (set-difference-equal (car pair2) new-ancestor-lits).
; The soundness argument above them (Observation 2) requires, for every
; INHERITED lit' in ancestor-lits, an already-collected pair' whose remaining
; hypotheses are a subset of the current pair2's hypotheses.  The claim "subset
; is transitive" fails: what is actually checked at each step is
;     hyps(new-pair_i) \ {lit_i} subset-of hyps(pair_{i+1})
; and lit_i itself, which pair'_{i-1} still needs, need not be in
; hyps(pair_{i+1}).  So an inherited ancestor is removed with no justification.
;
; Measured directly on the system function:
;   (convert-term-to-pairs '(IF (IF (DD V) (AA V) (IF (AA V) 'T (BB V))) (FOO V) 'T)
;                          (ens state) (w state))
;   = ((((DD V) (AA V)) FOO V) (((AA V)) FOO V) (((BB V)) FOO V))
; The third pair claims (BB V) --> (FOO V) with BOTH (DD V) and (NOT (AA V))
; dropped.  The term only guarantees (FOO V) under (AA V) or under
; (not (DD V)) & (not (AA V)) & (BB V).
;
; Reached from a plain DEFUN because tau-visit-defuns1 (tau.lisp:9787) routes
; every monadic-Boolean non-big-switch definition through tau-subrs (:9701) into
; convert-term-to-pairs (:9638).
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(tau-status :system t)

(defun aa (v) (if (equal (car v) 1) t nil))
(defun bb (v) (if (equal (cadr v) 2) t nil))
(defun dd (v) (if (equal (caddr v) 3) t nil))
(defun fn (v) (if (dd v) (aa v) (if (aa v) t (bb v))))

; THE DEFECT: tau records (BB v) --> (FN v) in bb's pos-implicants, which is
; false at v = '(0 2 3): (bb v)=T, (dd v)=T, (aa v)=NIL, so (fn v)=NIL.
(must-fail
 (defthm bad
   (implies (bb x) (fn x))
   :hints (("Goal" :in-theory (disable aa bb dd fn (:e aa) (:e bb) (:e dd) (:e fn))))
   :rule-classes nil))

; CONTROL: the implication that IS valid must stay provable, so the fix cannot
; be "stop deriving implicants from definition bodies".
(defthm honest-use
  (implies (aa x) (fn x))
  :hints (("Goal" :in-theory (disable aa bb dd fn (:e aa) (:e bb) (:e dd) (:e fn))))
  :rule-classes nil)
