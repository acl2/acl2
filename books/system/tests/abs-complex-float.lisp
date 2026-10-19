; This book, modified only as noted below and to accommodate ACL2(r), was
; produced by Claude and passed along by Eric Smith.  It illustrates a
; soundness bug fixed before ACL2 Version 8.8.  Claude produced it, for abs,
; upon prompting from Eric after similar fixes were already made to ACL2 for
; code-char, coerce and expt.

; S-108: abs of a complex rational returns a float in raw Lisp.
; ACL2 Soundness Review, issue S-108.  Proves nil on ACL2 master 227bafe2d1
; (which contains commit 79fb1487b5) with SBCL and CCL; no trust tags.
;
; ABS is imported from COMMON-LISP, so its raw definition is Common Lisp's:
; (abs #c(1 1)) is the float 1.4142135.  Its guard requires a real argument, but
; raw code of a :program-mode function does not check guards.  A computed hint
; (one of the channels of S-16) hands the float to the prover as the instance
; of a true lemma; evaluation then refutes the instance.
(in-package "ACL2")

(defun weird-nump (v)
  (declare (xargs :guard t))
  (and (acl2-numberp v) (not (real/rationalp v)) (not (complex/complex-rationalp v))))

(defthm not-weird ; every ACL2 number is real/rational or complex/complex-rational
  (not (weird-nump x))
  :rule-classes nil)

(defun mk-hint ()
  (declare (xargs :mode :program))
  (list :use (list (list :instance 'not-weird
                         (list 'x (list 'quote (abs #c(1 1))))))))

; Added by Matt Kaufmann after the bug fix:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This Must-fail wrapper added by Matt Kaufmann after bug fix:
(defthm bad nil
  :hints ((and (equal id *initial-clause-id*) (mk-hint)))
  :rule-classes nil)
)

; Commented out by Matt Kaufmann after the bug fix:
; (value-triple (cw "~%NIL-PROVED~%"))
