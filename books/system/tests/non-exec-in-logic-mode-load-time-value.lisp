; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-290: code under NON-EXEC is translated as for a theorem but still compiled as raw Lisp, so the in-logic-mode form check is skipped.
;
; G190 candidate (soundness): under NON-EXEC, a definition body is translated
; as for a theorem (stobjs-out t) but still compiled as raw Lisp, so a form that
; translate never checks reaches the compiler; LOAD-TIME-VALUE runs it while
; the definition is compiled (and again whenever the compiled file is loaded).
;
; translate11 translates the argument of non-exec with stobjs-out t
; (translate.lisp, return-last case, throw-nonexec-error-p1), and its
; in-logic-mode case checks the form only when stobjs-out is not t, so the form
; below is never translated.  The raw definition of PWN is
; (prog2$ (throw-nonexec-error ...) (in-logic-mode <form> state '())), whose raw
; expansion contains (value <form>); compiling it evaluates the load-time-value
; form, here a raw SETF of the symbol-function of G.  Ground evaluation of (G 0)
; then gives 2 while the definition says 1.
;
; Proves nil (plain ld and certify-book, no trust tags) on SBCL and CCL at
; 16dbd4bd56 (acl2-new6) and 21aaad6 (acl2-sbcl, acl2-ccl).
; Control: without the non-exec wrapper, translate refuses PWN ("the attempt to
; translate its first argument failed") and G-IS-2 fails.
; Second route, same root cause: G190-non-exec-return-last-load-time-value.lisp
; (return-last's key is checked against return-last-table only when stobjs-out
; is not t).  Stage-2 batch G190, lead F2-890.
(in-package "ACL2")
(defun g (x) (declare (xargs :guard t) (ignore x)) 1)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K. since pass2 now fails.
(defun pwn (state)
  (declare (xargs :stobjs state :mode :program))
  (non-exec
   (in-logic-mode
    (load-time-value
     (setf (symbol-function 'g) (lambda (x) (declare (ignore x)) 2)))
    state '())))
)

; The following comment was made by Matt K. since the defun just above now
; fails.
#|
(defthm g-is-2 (equal (g 0) 2) :rule-classes nil)
(defthm nil-proved nil
  :hints (("Goal" :use g-is-2 :in-theory (disable (:e g))))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#

; Added by Matt K.: Check corresponding logic-mode use of defun-nx.  This
; defun-nx didn't cause (symbol-function 'g) to change like the earlier defun
; (above) of pwn, but this defun-nx fails after the bug fix, and that seems
; safest and reasonable.
(must-fail
(defun-nx pwn (state)
  (declare (xargs :stobjs state))
  (in-logic-mode
   (load-time-value
    (setf (symbol-function 'g) (lambda (x) (declare (ignore x)) 2)))
   state '()))
)
