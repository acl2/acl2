; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-26: ev-fncall-meta is not untouchable and calls raw functions without guard or live-stobj checks
; ACL2 Soundness Review, issue S-26.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; GENF5 candidate (soundness): EV-FNCALL-META is not untouchable.  For a
; :common-lisp-compliant fn (here the stobj primitive
; UPDATE-FLD), ev-fncall-meta takes the
; ev-fncall! path, which APPLYs the RAW Lisp function to args without any
; guard or live-stobj check.  Passing a quoted list constant (the value of
; *c*, shared with the raw symbol-value) as the 'stobj' destructively smashes
; the constant's value; afterwards (cg) evaluates differently from the logic.
; Certifies as a book (cert.pl, no ttag).  Verified SBCL 2.6.1 (cg -> 7)
; and CCL 1.13 (cg -> 0).
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defstobj st fld)
(defconst *c* 5)
(defun cg () (declare (xargs :guard t)) *c*)
(defthm cg-is-5 (equal (cg) 5) :rule-classes nil)
(must-fail
; The call below fails: untouchable function
(make-event (mv-let (erp val st2) (ev-fncall-meta 'update-fld (list 7 '*c*) state)
              (declare (ignore erp val st2)) (value '(value-triple :done))))
)

; The following are commented out since the event just above now fails.
#|
(make-event `(defthm cg-is-other (equal (cg) ',(cg)) :rule-classes nil))
(defthm bad nil :hints (("Goal" :use (cg-is-5 cg-is-other))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
