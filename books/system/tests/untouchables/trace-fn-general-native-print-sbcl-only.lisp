; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-38 route (lead F1-4307, stage-2 batch G48), SBCL only: trace$ with :native passes a
; :print form to the host TRACE, which runs it as raw Lisp.  Proves nil, no trust tags:
; SBCL at 21aaad6 and 9a589490e6.
;
; G48: S-38 payload via :native (SBCL): trace$-fn-general skips the trust-tag
; check for :native too, and SBCL evaluates the host TRACE :print form as raw Lisp.
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun g () (declare (xargs :guard t)) 5)
(defthm g-is-5 (equal (g) 5) :rule-classes nil)
(defun f (x) (declare (xargs :guard t)) x)
(must-fail
(make-event
 (er-progn (trace$-fn-general ; fails: untouchable function
            '(f :native t
                #+sbcl :print #-sbcl :entry
                (progn (setf (symbol-function 'g) (lambda () 6)) 0))
            'top state)
           (value '(value-triple :traced))))
)

; The following are commented out since the event just above now fails.
#|
(make-event (prog2$ (f 1) '(value-triple :called)))
(make-event `(defthm g-is-other (equal (g) ',(g)) :rule-classes nil))
(defthm nil-proved nil :hints (("Goal" :use (g-is-5 g-is-other))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
