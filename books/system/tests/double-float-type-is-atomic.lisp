; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.  The point is that in ACL2, the double-float type declaration
; must not be nested or non-atomic, as it gets very special handling.  The
; first sentence below apparently references earlier examples from Claude, not
; included here.

; Same root cause as a1 (df-type-p, translate.lisp:20979-21002, has no NOT
; case), but here it needs no apply$, no lambda object, no metafunction and no
; *aokp*: a plain DEFUN with the type specifier (NOT (NOT DOUBLE-FLOAT)).
;
;  * get-guards/translate-declaration-to-guard-gen turn the TYPE spec into the
;    guard conjunct (NOT (NOT (DFP X))), and raw Lisp DFP (float-a.lisp:581-588)
;    answers T for any ordinary rational exactly representable as a double, so
;    (dfp 3) = T and the *1* guard check passes for the INTEGER 3.
;  * the raw Lisp DEFUN keeps (DECLARE (TYPE (NOT (NOT DOUBLE-FLOAT)) X)),
;    which SBCL normalizes to DOUBLE-FLOAT and uses at (safety 0) (speed 3)
;    to constant-fold (INTEGERP X) to NIL.
;  * df-type-p answers NIL for (NOT (NOT DOUBLE-FLOAT)), so neither
;    remove-double-float-types nor extend-known-dfs-with-declared-df-types
;    notices that a double-float type has been declared.
;
; So (H 3) is NIL by the definitional axiom but T by evaluation.

(in-package "ACL2")

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defun h (x)
  (declare (type (not (not double-float)) x))
  (not (integerp x)))
)

; The rest, commented out by Matt K., is no longer relevant after the bug fix.
#|
; By the definitional axiom: (h 3) = (not (integerp 3)) = nil.
(defthm h-3-is-nil
  (equal (h 3) nil)
  :hints (("Goal" :in-theory (disable (:executable-counterpart h))))
  :rule-classes nil)

; By evaluation (the miscompiled raw Lisp definition): (h 3) = t.
(defthm h-3-is-t
  (equal (h 3) t)
  :rule-classes nil)

(defthm nil-proved
  nil
  :hints (("Goal" :use (h-3-is-nil h-3-is-t)))
  :rule-classes nil)
|#
