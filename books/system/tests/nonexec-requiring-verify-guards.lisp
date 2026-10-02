; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; PROOF OF NIL.  Certifies from scratch on f79f828568.  No ttag, no skip-proofs,
; no defaxiom, no include-book.
;
; Finding 12, remaining half -- GUARD PROMOTION for :non-executable defuns.
; The Sept 2026 change at defuns.lisp:7147 ((eq (cadr val) :logic) ->
; (not (eq (cadr val) :program))) closed the MEASURE half.  This half is
; untouched, and it is NOT a missing comparison in non-identical-defp -- it is a
; MISSING COND CLAUSE in redundant-or-reclassifying-defunp.
;
;   The ORDINARY branch guards guard-promotion, defuns.lisp:7167-7187:
;       ((eq (cadr val) defun-mode)
;        (cond ((and (eq symbol-class :common-lisp-compliant)
;                    (eq (symbol-class name wrld) :ideal))
;               'verify-guards)               ; the v2-7 check
;              ... (t 'redundant)))
;
;   The :NON-EXECUTABLE branch, defuns.lisp:7265-7290, has only three subcases
;   and OMITS that clause, falling through to 'redundant at :7285.
;
; So a non-executable defun that REQUESTS guard verification is declared
; :REDUNDANT in pass 1 against an :ideal local one, and encapsulate pass 2 stores
; symbol-class :COMMON-LISP-COMPLIANT with no guard proof.  (:guard-theorem f)
; then yields a guard theorem that was never proved.
;
; SUGGESTED FIX: insert the promotion clause between defuns.lisp:7284 and 7285:
;       ((and (eq symbol-class :common-lisp-compliant)
;             (eq (symbol-class name wrld) :ideal))
;        'verify-guards)
;
; FOUR ROUTES reach that branch; a fix keyed on any one of them would miss the
; others, so all four are included:
;   (a) explicit (xargs :non-executable t :verify-guards t)
;   (b) the DEFUN-NX macro
;   (c) ambient (set-verify-guards-eagerness 2), with NO :verify-guards xarg
;   (d) MUTUAL-RECURSION of non-executable defuns
; THIS FILE IS ROUTE (a) explicit (xargs :non-executable t :verify-guards t).

(in-package "ACL2")

; The :non-executable branch of redundant-or-reclassifying-defunp
; (defuns.lisp ~7262) omits the ":ideal -> :common-lisp-compliant" promotion
; guard present in the ordinary branch (defuns.lisp ~7160).  So the second
; defun below is declared redundant in pass 1 even though it requests guard
; verification, and pass 2 of the ENCAPSULATE stores symbol-class
; :COMMON-LISP-COMPLIANT for F with no guard proof at all.

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(encapsulate
  ()
  (local (defun f (x)
           (declare (xargs :non-executable t :guard t :verify-guards nil))
           (prog2$ (throw-nonexec-error 'f (list x))
                   (car x))))
  (defun f (x)
    (declare (xargs :non-executable t :guard t :verify-guards t))
    (prog2$ (throw-nonexec-error 'f (list x))
            (car x))))
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm bad
  (or (consp x) (equal x nil))
  :rule-classes nil
  :hints (("Goal" :use (:guard-theorem f))))
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use (:instance bad (x 0)))))
)
