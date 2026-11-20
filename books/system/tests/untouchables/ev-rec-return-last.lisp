; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-24: ev-rec-return-last is not untouchable and lets raw code call an arbitrary function
; ACL2 Soundness Review, issue S-24.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; GENF5 candidate (soundness): ev-rec-return-last is not untouchable (unlike
; ev-rec etc.), and in raw Lisp it evals `(,fn ,arg2-val ...)` for an arbitrary
; symbol fn.  With fn = SET we bind the raw special *safe-mode-verified-p* to a
; non-nil value, so ec-call1-raw then runs raw Lisp code (zp -3) = nil instead
; of the *1* function.  Certifies as a book (cert.pl, no ttag) and proves NIL.
; Verified on master 21aaad6, SBCL 2.6.1 (top-level variant also on CCL 1.13).
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun g (x) (declare (xargs :verify-guards nil)) (zp x))
(defun f (x) (declare (xargs :guard t)) (ec-call (g x)))
(defthm f-logic (equal (f -3) t) :hints (("Goal" :in-theory (disable (:e f)))) :rule-classes nil)
(must-fail
(make-event
 (mv-let (erp val lat)
   ; The call below fails: untouchable function
   (ev-rec-return-last 'set ''*safe-mode-verified-p* 'zzz-unbound nil (w state) nil 1000 nil nil nil nil t)
   (declare (ignore erp val lat))
   (value '(value-triple :set))))
)

; The following are commented out since the event just above now fails.
#|
(defthm f-exec (equal (f -3) nil) :rule-classes nil)
(defthm bad nil :hints (("Goal" :use (f-logic f-exec))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
