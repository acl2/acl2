; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-290, second route: under NON-EXEC the return-last-table key check is skipped as well.
;
; G190 candidate (soundness), second route for
; G190-non-exec-in-logic-mode-load-time-value.lisp: under NON-EXEC the body is
; translated with stobjs-out t, where translate11 treats return-last as an
; ordinary function and skips the check that a quoted first argument is a key
; of return-last-table.  The raw return-last macro turns
; (return-last 'k a b) into (k a b) for any fboundp k, so
; (return-last 'load-time-value <term> nil) is compiled as LOAD-TIME-VALUE and
; (return-last 'apply 'eval '(<form>)) as (apply 'eval '(<form>)): any raw Lisp
; form runs while PWN is compiled.  Here it redefines the raw code of G.
;
; Proves nil (plain ld and certify-book, no trust tags) on SBCL and CCL at
; 16dbd4bd56 (acl2-new6) and 21aaad6 (acl2-sbcl, acl2-ccl).
; Control: without non-exec, translate refuses PWN ("LOAD-TIME-VALUE is not
; associated in the table RETURN-LAST-TABLE") and G-IS-2 fails.
; (CCL requires the second argument of load-time-value to be a literal T or
; NIL, hence the NIL.)  Stage-2 batch G190, lead F2-890.
(in-package "ACL2")
(defun g (x) (declare (xargs :guard t) (ignore x)) 1)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K. since pass2 now fails.
(defun pwn ()
  (declare (xargs :mode :program))
  (non-exec
   (return-last 'load-time-value
                (return-last 'apply 'eval
                             '((setf (symbol-function 'g)
                                     (lambda (x) (declare (ignore x)) 2))))
                nil)))
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
