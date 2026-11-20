; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-38: trace$-fn-general installs :def trace specs without the trust-tag check
; ACL2 Soundness Review, issue S-38.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; EV1 candidate (soundness): TRACE$-FN-GENERAL is a touchable :program function.
; TRACE$-FN (the function behind TRACE$) refuses the :DEF, :NATIVE and
; :MULTIPLICITY options unless a trust tag is active, but that check is made
; only in TRACE$-FN; its subroutine TRACE$-FN-GENERAL installs any trace spec.
; With :DEF the raw Lisp definition of F is replaced by a different body.
; Verified at master 21aaad6: proves NIL at top level and in a book certified
; with cert.pl (no ttag) on SBCL 2.6.1 and CCL 1.13.
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun f () (declare (xargs :guard t)) 5)
(defthm f-is-5 (equal (f) 5) :rule-classes nil)
(must-fail
(make-event
 ; The call below fails: untouchable function
 (er-progn (trace$-fn-general '(f :def (f () 6)) 'top state)
           (value '(value-triple :traced))))
)

; The following are commented out since the event just above now fails.
#|
(make-event `(defthm f-is-other (equal (f) ',(f)) :rule-classes nil))
(defthm bad nil :hints (("Goal" :use (f-is-5 f-is-other))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
