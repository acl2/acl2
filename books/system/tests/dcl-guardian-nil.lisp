; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; Soundness bug: ACL2's DCL-GUARDIAN drops ALL type-declaration proof
; obligations for a LET whose FIRST type declaration is of the form
; (TYPE (OR T ...) var), yet raw Lisp keeps every declaration.
; See translate.lisp, defun DCL-GUARDIAN.

(in-package "ACL2")

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defun f (x)
  (declare (xargs :guard (rationalp x)))
  (let ((a x) (b x))
    (declare (type (or t integer) a)   ; <-- silences the guardian for the LET
             (type (integer 0 100) b)  ; <-- never proved, but trusted by SBCL
             (ignorable a))
    (< b 500)))
)

; The rest, commented out by Matt K., is no longer relevant after the bug fix.
#|
; Logically (f 1000) = (< 1000 500) = NIL.
(defthmd f-1000-is-nil
  (equal (f 1000) nil)
  :hints (("Goal" :in-theory (disable (:e f)))))

; But the executable counterpart returns T, because SBCL compiled the raw
; body under the (false) declaration (TYPE (INTEGER 0 100) B) and folded
; (< B 500) to T.
(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use f-1000-is-nil
                  :in-theory (union-theories '((:e f)) (theory 'minimal-theory)))))
|#
