; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-12: Same flag lets defattach :skip-checks run without a trust tag (top level)
; ACL2 Soundness Review, issue S-12.  Proves nil on ACL2 master 21aaad6
; (2026-10-15) with SBCL and CCL 1.13; no trust tags.  run-examples.sh prints
; STILL PROVES NIL while the bug is present.
;
; SG1 candidate (soundness): second mechanism behind the touchable state
; global boot-strap-flg (issue S-12).  process-defattach-args
; (other-events.lisp, ~31111) allows :SKIP-CHECKS T without an active trust
; tag when (f-get-global 'boot-strap-flg state) is true.  So, at the top
; level, (assign boot-strap-flg t) lets a user attach to H a function that
; violates H's constraint, with no proof obligation and nothing recorded
; (ttags-seen, skip-proofs-seen and redef-seen stay NIL).  A verified clause
; processor that consults H then proves NIL.  This is a different check from
; the name check used by boot-strap-flg.lisp, so making only
; chk-just-new-name consult the world global would not fix it; making
; boot-strap-flg untouchable fixes both.
; Plain LD at the top level, no ttag; verified on master 21aaad6 with SBCL and
; CCL 1.13.  (Inside make-event the attachment is reverted with the world, so
; no certifiable-book route via this path.)
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(encapsulate ((h (x) t))
  (local (defun h (x) (declare (ignore x)) t))
  (defthm h-true (h x)))
(defevaluator evl evl-list ((if x y z)))
(defun cp (cl) (declare (xargs :guard t)) (if (h 0) (list cl) nil))
(defthm cp-correct
  (implies (and (pseudo-term-listp cl) (alistp a)
                (evl (conjoin-clauses (cp cl)) a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)
(defun bad-h (x) (declare (xargs :guard t)) (declare (ignore x)) nil)
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
(defattach (h bad-h) :skip-checks t)
(assign boot-strap-flg nil)
(defthm bad nil :hints (("Goal" :clause-processor (cp clause))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
