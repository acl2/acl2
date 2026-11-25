; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-355 (stage-2 batch G360, lead F8-341.A). CCL only: inside an FLET that binds the name of a global $INLINE function and
; declares that local binding INLINE, CCL's compiler inlines the GLOBAL
; function's body instead of the local one.  ACL2 translates the FLET as a
; LAMBDA over the local body, so evaluation (raw code of a guard-verified
; function) disagrees with the definition.  No trust tags.
; Proves nil by ld and certifies (include-book + (thm nil :hints (("Goal" :use
; bad))) succeeds) on CCL at dc0f042c42 and 16dbd4bd56; SBCL compiles the local
; body and the proof fails.  Without the (declare (inline foo$inline)) the
; local body is used.  Variants (same wrong value on CCL): the global
; FOO$INLINE was undone with ubt! before G was defined, or it was only LOCAL in
; an earlier encapsulate (so it is not in the world at all).
(in-package "ACL2")

(defun-inline foo (x)
  (declare (xargs :guard t))
  (cons 'global x))

(defun g (x)
  (declare (xargs :guard t))
  (flet ((foo$inline (y) (cons 'local y)))
    (declare (inline foo$inline))
    (foo$inline x)))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
; Logically (g 1) = (LOCAL . 1); CCL's compiled code returns (GLOBAL . 1).
(defthm g-1-by-evaluation
  (equal (g 1) '(global . 1))
  :rule-classes nil)
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defthm bad
  nil
  :hints (("Goal" :use g-1-by-evaluation
                 :in-theory (disable (:e g))))
  :rule-classes nil)

(value-triple (and (getpropc 'bad 'theorem nil (w state))
                   (cw "~%NIL-PROVED~%")))
|#
