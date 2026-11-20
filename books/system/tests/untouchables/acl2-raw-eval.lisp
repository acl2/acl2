; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-37: acl2-raw-eval is not untouchable; its raw definition is EVAL
; ACL2 Soundness Review, issue S-37.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; EV1 candidate (soundness): ACL2-RAW-EVAL (other-events.lisp) is a :program
; function that is NOT untouchable.  Its raw Lisp definition simply calls EVAL
; on the given form (wrapped by acl2-raw-eval-form-to-eval), so any raw Lisp
; form can be evaluated from the loop or a book without a trust tag or raw mode.
; Here it redefines the raw Lisp function F to return 6 while the logic says 5.
; Certifies as a book with cert.pl (no ttag; the .cert records no ttags) and the
; final DEFTHM proves NIL.  Verified at master 21aaad6 on SBCL 2.6.1 and
; CCL 1.13, top level and certified/included.
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun f () (declare (xargs :guard t)) 5)
(defthm f-is-5 (equal (f) 5) :rule-classes nil)
(must-fail
(make-event
 (er-progn (acl2-raw-eval '(defun f () 6) state) ; fails: untouchable function
           (value '(value-triple :redefined))))
)

; The following are commented out since the event just above now fails.
#|
(make-event `(defthm f-is-other (equal (f) ',(f)) :rule-classes nil))
(defthm bad nil :hints (("Goal" :use (f-is-5 f-is-other))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
