; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; G199 (lead F2-3000): with-debug is a user-callable macro with raw code
; (defuns.lisp).  Its logic definition ignores the format string and arguments
; (declare (ignore string args)), so translate never sees them, while its raw
; definition splices them into (format str ,string ,@args) under
; (when *debug-on* ...).  That branch never runs, but any Lisp form can be put
; there, and a LOAD-TIME-VALUE form is evaluated when the defun is compiled (and
; when the book's compiled file is loaded), so a book runs arbitrary raw Lisp
; without a trust tag.  Here it replaces the raw definition of g.
; Control: G199-with-debug-untranslated-args-control.lisp (no h) fails.
(in-package "ACL2")

(defun g (x)
  (declare (xargs :guard t))
  x)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K. since pass2 now fails.
(defun h (x)
  (declare (xargs :guard t))
  (with-debug x "~a"
    (common-lisp::load-time-value
     (common-lisp::progn
      (common-lisp::setf (common-lisp::symbol-function 'g)
                         (common-lisp::lambda (y) (declare (ignore y)) 0))
      nil))))
)

(must-fail ; This must-fail wrapper was added by Matt K. since pass2 now fails.
(defthm g-1-is-0
  (equal (g 1) 0)
  :rule-classes nil)
)

(defthm g-1-is-1
  (equal (g 1) 1)
  :hints (("Goal" :in-theory (disable (:e g))))
  :rule-classes nil)

(must-fail ; This must-fail wrapper was added by Matt K. since pass2 now fails.
(defthm bad nil
  :hints (("Goal" :use (g-1-is-0 g-1-is-1)))
  :rule-classes nil)
)

