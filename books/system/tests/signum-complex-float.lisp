; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.  Claude produced it, for signum, upon prompting from Eric after
; similar fixes were already made to ACL2 for code-char, coerce and expt.

; S-108: signum of a complex rational returns a complex float in raw Lisp.
; ACL2 Soundness Review, issue S-108.  Proves nil on ACL2 master 227bafe2d1
; (which contains commit 79fb1487b5) with SBCL and CCL; no trust tags.
;
; SIGNUM is imported from COMMON-LISP, so its raw definition is Common Lisp's:
; (signum #c(1 1)) is the complex float #C(0.70710677 0.70710677), whose real
; part is not rational.  As in S-108-abs-complex-float.lisp, a computed hint
; hands it to the prover as the instance of a true lemma.
(in-package "ACL2")

(defun weird-complexp (v)
  (declare (xargs :guard t))
  (and (complex-rationalp v) (not (rationalp (realpart v)))))

(defthm not-weird-complex ; the real part of a complex rational is rational
  (not (weird-complexp x))
  :rule-classes nil)

(defun mk-hint ()
  (declare (xargs :mode :program))
  (list :use (list (list :instance 'not-weird-complex
                         (list 'x (list 'quote (signum #c(1 1))))))))

; Added by Matt Kaufmann after the bug fix:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This Must-fail wrapper added by Matt Kaufmann after bug fix:
(defthm bad nil
  :hints ((and (equal id *initial-clause-id*) (mk-hint)))
  :rule-classes nil)
)

; Commented out by Matt Kaufmann after the bug fix:
; (value-triple (cw "~%NIL-PROVED~%"))
