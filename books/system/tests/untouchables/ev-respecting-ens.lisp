; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-213 (lead F1-6259, stage-2 batch G73): the touchable ev-respecting-ens evaluates a caller's term, which may
; call untouchable functions.  Proves nil and certifies, no trust tags: SBCL and CCL at 21aaad6 and
; 947ff84343.  Control: without the make-event, F-EXEC fails.
;
; G73 (lead F1-6259.A), same_as S-201: the touchable ev-respecting-ens
; (simplify.lisp, the forward-chaining ground evaluator) evaluates the
; arguments of any call in the form it is given and then applies the function
; with the untouchable EV-FNCALL on the live state, with no untouchable check,
; so it applies untouchable functions like S-201's ev-fncall-w-tau-recog.
; Here EV-REC-RETURN-LAST is first made untouchable (the S-24 fix, simulated
; with PUSH-UNTOUCHABLE), and no EV-REC key check is involved: the key SET is
; passed straight to EV-REC-RETURN-LAST, which sets *SAFE-MODE-VERIFIED-P*, so
; EC-CALL then runs raw code, (zp -3) = NIL.
; Proves nil and certifies (no trust tags) on 947ff84343 (new5 SBCL, CCL) and
; 21aaad6 (acl2-sbcl, acl2-ccl).  Control: without the make-event, F-EXEC
; (and BAD) fail.
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(push-untouchable ev-rec-return-last t)
(defun g (x) (declare (xargs :verify-guards nil)) (zp x))
(defun f (x) (declare (xargs :guard t)) (ec-call (g x)))
(defthm f-logic (equal (f -3) t)
  :hints (("Goal" :in-theory (disable (:e f))))
  :rule-classes nil)
(must-fail
(make-event
 (mv-let (erp val ttree)
   ; The call below fails: untouchable function
   (ev-respecting-ens '(ev-rec-return-last 'set '(quote *safe-mode-verified-p*) 'zzz
                                           'nil w 'nil '100000 'nil 't 'nil 't 'nil)
                      (list (cons 'w (w state))) state nil (ens state) (w state))
   (declare (ignore erp val ttree))
   (value '(value-triple :set))))
)

; The following are commented out since the event just above now fails.
#|
(defthm f-exec (equal (f -3) nil) :rule-classes nil)
(defthm nil-proved nil :hints (("Goal" :use (f-logic f-exec))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
