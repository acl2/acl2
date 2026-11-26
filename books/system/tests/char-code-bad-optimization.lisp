; This book and comments, modified only as noted below by Matt Kaufmann, were
; produced by Claude and passed along by Eric Smith and Stephen Westfold.  This
; book illustrates a soundness bug in some versions of SBCL, fixed by an ACL2
; workaround before ACL2 Version 8.8.  Note that the unmodified book certified
; with ACL2 built on SBCL on a Mac arm64 on 11/26/2026, before installing "AI
; fix 7".

(in-package "ACL2")

(defun f (x y)
  (declare (xargs :guard (and (characterp x) (integerp y) (<= 10 y) (<= y 20))))
  (let ((y (the (integer 10 20) y)))
    (if (eql (char-code x) y)
        nil
      (and (<= 10 (char-code x)) (<= (char-code x) 20)))))

(defthm f-true (equal (f (code-char 12) 11) t)
  :hints (("Goal" :in-theory (disable (:e f)))))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm f-by-evaluation (equal (f (code-char 12) 11) nil)
  :hints (("Goal" :in-theory '((:e f)))))
)

; The following was commented out by Matt K. since the event just above now
; fails.
#|
(defthm nil-proved nil :rule-classes nil
  :hints (("Goal" :use (f-true f-by-evaluation) :in-theory nil)))
|#
