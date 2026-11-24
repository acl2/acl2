; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; S-201 (lead F1-5797, stage-2 batch G58): the touchable ev-fncall-w-tau-recog applies any function,
; untouchable ones included, to any arguments on the live world, with no ev-fncall-w-guard check; here it
; calls ev-rec-return-last directly after that has been made untouchable.  Proves nil and certifies,
; no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.  Control: without the make-event, F-EXEC fails.
;
(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

; G58 (same_as S-39, new route): EV-FNCALL-W-TAU-RECOG passes its EVG-LST
; unchanged as the argument list of the untouchable EV-FNCALL-W and never
; calls EV-FNCALL-W-GUARD, so with the LIVE world it applies an untouchable
; function of any arity.  Here EV-REC-RETURN-LAST is first made untouchable
; (the S-24 fix, simulated with PUSH-UNTOUCHABLE), and no EV-REC key check is
; involved: the key SET is passed straight to EV-REC-RETURN-LAST, which sets
; *SAFE-MODE-VERIFIED-P* to T, after which EC-CALL runs raw code.
(push-untouchable ev-rec-return-last t)
(defun g (x) (declare (xargs :verify-guards nil)) (zp x))
(defun f (x) (declare (xargs :guard t)) (ec-call (g x)))
(defthm f-logic (equal (f -3) t)
  :hints (("Goal" :in-theory (disable (:e f))))
  :rule-classes nil)
(must-fail
(make-event
 (prog2$ (ev-fncall-w-tau-recog ; fails: untouchable function
          'ev-rec-return-last
          (list 'set ''*safe-mode-verified-p* 'zzz
                nil (w state) nil 100000 nil t nil t nil)
          (ens state) (w state))
         (value '(value-triple :set))))
)

; The following are commented out since the event just above now fails.
#|
(defthm f-exec (equal (f -3) nil) :rule-classes nil)
(defthm nil-proved nil :hints (("Goal" :use (f-logic f-exec))) :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
