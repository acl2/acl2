; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-232 (lead F1-168, stage-2 batch G85): the raw doppelganger of apply$-userfn never checks that args is a true list;
; for a string, length works and safety-0 raw take reads the string's words as elements.  Proves nil and certifies,
; no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.  Control: a list in place of the string, and L1 fails.
;
; G85 (lead F1-168.A): proof of NIL.  Certifiable book, no trust tags.
;
; When the prover evaluates (APPLY$ 'F ARGS) for a warranted F, the raw
; attachment DOPPELGANGER-APPLY$-USERFN (apply-raw.lisp) calls
; RAW-APPLY-FOR-BADGED-FN, which computes (LENGTH ARGS) and, when that differs
; from F's arity, (TAKE ARITY ARGS).  Nothing checks that ARGS is a true list.
; LENGTH accepts a string, and the raw TAKE, compiled at safety 0, runs
; (POP L) on the string, so CAR reads a word of the string object as if it
; were a cons: on SBCL the string's length, on CCL (for a string of NUL
; characters) the fixnum 0.  So the prover rewrites (APPLY$ 'F *S*) to a
; non-NIL value, while F's warrant says (APPLY$ 'F *S*) = (F (CAR *S*)) =
; (F NIL) = NIL.  Hence (NOT (APPLY$-WARRANT-F)); but the warrant is
; satisfiable, as the functional instance below shows.
;
; Tried: (certify-book "G85-apply-string-args-take") and (ld ...) on SBCL and
; CCL, at master 947ff84343, 15e42ee881 and 21aaad6.

(in-package "ACL2")
(include-book "projects/apply/base" :dir :system)

(defun f (x) (declare (xargs :guard t)) x)
(defwarrant f)

; A string of four NUL characters.
(defconst *s* (coerce (list (code-char 0) (code-char 0) (code-char 0) (code-char 0))
                      'string))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
; FALSE: proved by evaluating (APPLY$ 'F *S*) in raw Lisp.
(defthm l1
  (implies (apply$-warrant-f) (apply$ 'f *s*))
  :hints (("Goal" :in-theory (enable (:e apply$))))
  :rule-classes nil)
)

; True: by the warrant, (apply$ 'f *s*) = (f (car *s*)) = nil.
(defthm l2
  (implies (apply$-warrant-f) (equal (apply$ 'f *s*) nil))
  :rule-classes nil)

; The following were commented out by Matt K. since the event l1 above now
; fails.
#|
(defthm not-warrant-f
  (not (apply$-warrant-f))
  :hints (("Goal" :use (l1 l2) :in-theory (theory 'minimal-theory)))
  :rule-classes nil)

; A model in which the warrant of F holds.
(defun badge-userfn-m (fn)
  (if (eq fn 'f) '(apply$-badge 1 1 . t) nil))

(defun apply$-userfn-m (fn args)
  (if (eq fn 'f) (f (car args)) nil))

(defthm nil-proved
  nil
  :hints (("Goal" :use ((:functional-instance not-warrant-f
                         (apply$-warrant-f (lambda () t))
                         (apply$-warrant-f-witness (lambda () nil))
                         (badge-userfn badge-userfn-m)
                         (apply$-userfn apply$-userfn-m)))))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
