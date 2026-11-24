; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-12: State global boot-strap-flg is touchable, so (assign boot-strap-flg t) allows redefining o<
; ACL2 Soundness Review, issue S-12.  Proves nil at the top level on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; Note: The make-event wrapper below was added (inside the must-fail
; wrapper) because the original form is not an event, and hence would not be
; legal in a book.
(must-fail
(make-event
 (er-progn
  (assign boot-strap-flg t) ; fails: untouchable variable
  (value '(value-triple :ok))))
)

; The following are commented out since the event just above now fails.
#|
(defun o< (x y) (declare (ignore x y)) t)
(assign boot-strap-flg nil)
(defun f (x)
  (declare (xargs :measure (acl2-count x)))
  (if (consp x) (+ 1 (f x)) 0))
(defthm bad nil :rule-classes nil
  :hints (("Goal" :use ((:instance f (x (cons a b))))
                  :in-theory (disable f (:e f)))))

(value-triple (cw "~%NIL-PROVED~%"))
|#
