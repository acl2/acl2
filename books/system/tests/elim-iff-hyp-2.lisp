; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.

; SOUNDNESS BUG: the Sept-2026 :ELIM soundness fix is bypassable via
; ENCAPSULATE pass 2 (and equally via INCLUDE-BOOK).
;
; chk-acceptable-rules (defthm.lisp:9985) discards every rule-class
; acceptability check except :META/:CLAUSE-PROCESSOR/:CONGRUENCE when
; (ld-skip-proofsp state) is 'include-book or 'include-book-with-locals, i.e.
; at include-book time AND in pass 2 of ENCAPSULATE.  chk-acceptable-elim-rule
; (defthm.lisp:5607) is therefore never run in pass 2, yet add-elim-rule
; (defthm.lisp:5723) installs the rule unconditionally.
;
; chk-acceptable-elim-rule's check
;   (every-occurrence-equiv-hittablep-in-clausep equiv rhs hyps-list nil wrld)
; is WORLD-DEPENDENT: it consults the 'congruences properties of the world.
; Here it holds in pass 1 only because of a LOCAL (defcong iff iff (p x) 1)
; proved about the local WITNESS for the constrained function P.  The exported
; constraint on P is vacuous, so the congruence is false of P in general --
; but the :ELIM rule is installed anyway.
;
; apply-instantiated-elim-rule (other-processes.lisp:899) then does a BLIND
;   (subst-var-lst generalized-lhs rhs generalized-cl-with-hyps)
; over the clause that has the rule's negated hypotheses adjoined, replacing X
; by the IFF-equal term (TOBOOL HD) inside (P X).  That step is exactly what
; the new hittability check was added to prevent.
;
; Net effect: the prover hands us the congruence
;   (implies (p x) (p (tobool x)))
; for a P whose only constraint is vacuous.  Functionally instantiate P and
; derive NIL.

(in-package "ACL2")

(defun h (x) x)
(defun tobool (x) (if x t x))

; H must stay closed so that (H X) survives as a destructor term; TOBOOL must
; stay closed so the goal clause is not case-split before ELIM runs.
(in-theory (disable h (:executable-counterpart h)
                    tobool (:executable-counterpart tobool)))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(encapsulate
  (((p *) => *))

  (local (defun p (x) (if x t nil)))

  ; LOCAL: makes the occurrence of X in the rule's hypothesis (P X)
  ; IFF-hittable -- in pass 1 only.  Not exported, so P is not known to be
  ; IFF-congruent in the resulting world.
  (local (defcong iff iff (p x) 1))

  ; Pass 1: chk-acceptable-elim-rule runs and ACCEPTS, because
  ;   (every-occurrence-equiv-hittablep-in-clausep 'iff 'x '((p x)) nil wrld)
  ; is true given the local :congruence rule.
  ; Pass 2: the check is skipped entirely; add-elim-rule installs
  ;   :hyps ((P X)) :equiv IFF :lhs (TOBOOL (H X)) :rhs X
  ; under the 'eliminate-destructors-rules property of H.
  ;
  ; The formula itself is a theorem for ANY P: (iff (tobool (h x)) x) is
  ; valid, so the exported constraint on P is vacuous.
  (defthm bad-elim
    (implies (p x) (iff (tobool (h x)) x))
    :rule-classes :elim
    :hints (("Goal" :in-theory (enable h tobool)))))
)

; Commented out by Matt Kaufmann (as the rest of the file is irrelevant after
; the bug fix):

#|
; Closes the "pathological" case clause that ELIM splits off, namely
;   (P X) \/ (NOT (P (H X))) \/ (P (TOBOOL (H X))).
; Valid for every P because H is the identity.
(defthm p-h-fc
  (implies (p (h x)) (p x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable h))))

; ELIM adjoins the negated hypothesis (NOT (P X)) to the clause, generalizes
; (H X) to HD, and then blindly replaces X by (TOBOOL HD), turning
;   ((NOT (P X)) (NOT (P HD)) (P (TOBOOL HD)))
; into the tautology
;   ((NOT (P (TOBOOL HD))) (NOT (P HD)) (P (TOBOOL HD))).
; So this "theorem" is proved even though it does not follow from P's
; (vacuous) constraint.  Rules used: (:ELIM BAD-ELIM) (:FORWARD-CHAINING P-H-FC).
(defthm bad-thm
  (implies (p (h x)) (p (tobool (h x))))
  :rule-classes nil)

; P := (lambda (y) (equal y 3)) satisfies P's constraint (the conclusion of
; BAD-ELIM is valid), but falsifies BAD-THM at x = 3:
;   (h 3) = 3, so (p (h 3)) holds, while (tobool (h 3)) = T and (equal T 3) is
;   false.
(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance (:functional-instance bad-thm
                                                  (p (lambda (y) (equal y 3))))
                            (x 3)))
           :in-theory (enable h tobool))))
|#
