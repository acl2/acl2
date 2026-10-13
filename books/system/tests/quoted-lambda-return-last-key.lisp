; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug introduced after ACL2 Version 8.7 that was fixed
; before ACL2 Version 8.8.  The bug was introduced when we ceased removing
; guard-holders from quoted lambdas when processing them before insertion into
; the compiled lambda cache (see :DOC print-cl-cache), in source function
; logic-code-to-runnable-code; see comments there.

; Finding 56: a quoted LAMBDA object may carry ANY return-last key, and since
; c0fee4d67b raw Lisp macroexpands it.  THIS IS A REGRESSION INTRODUCED BY THAT
; COMMIT -- the one that fixed Finding 35 and N148.
;
; logic-code-to-runnable-code (defuns.lisp:9378-9385) now KEEPS the return-last
; call when RRL is nil, and make-compileable-guard-and-body-lambdas passes nil at
; defuns.lisp:9610 (the guard) and :9621 (the body).  The raw return-last macro
; (axioms.lisp:3257) emits (list fn arg2 arg3) for ANY fn with (fboundp fn).
; TRANSLATE enforces membership in return-last-table -- but a quoted LAMBDA
; object is never translated, and neither termp nor well-formed-lambda-objectp
; imposes such a check.
;
; Measured, same session:
;   (apply$ '(lambda (x) (return-last 'cons x '3)) '(1))  =>  (1 . 3)
;   (ev$ '(return-last 'cons y '3) '((y . 1)))            =>  3
;   (apply$ 'return-last '(cons 1 3))                     =>  3
; One ground term, two values.
;
; That it is a regression is measured, not inferred.  At 585c8afb51 the old
; defuns.lisp:9297-9298 was unconditionally
;   ((eq (ffn-symb term) 'return-last) (logic-code-to-runnable-code nil (fargn term 3) wrld))
; and make-compileable-guard-and-body-lambdas additionally applied
; remove-guard-holders first; measured,
;   (remove-guard-holders '(return-last 'cons x '3) (w state))  =>  '3
; so the compiled body used to be (LAMBDA (X) '3), the correct value.
;
; The key need not be harmless.  'nth gives
; "CORRUPTION WARNING in SBCL ... Memory fault at 0xf", and 'funcall applies an
; arbitrary raw function.  Worse, the GUARD slot takes the same path
; (defuns.lisp:9610), so a lying guard -- (xargs :guard (return-last 'cons x 'nil))
; -- computes non-nil in raw Lisp and makes EVERY guard obligation of the body
; vacuous while the body still runs.
;
; The proof of nil additionally needs the *aokp* gate on the cl-cache
; (apply-raw.lisp:4168) to be open inside the prover.  prog2$ does that: the raw
; return-last macro wraps its SECOND argument in (let ((*aokp* t)) arg2)
; (axioms.lisp:3253), on the stated ground that "evaluation of arg2 does not
; affect the logical result, there is no soundness issue here" -- which fails as
; soon as a side channel carries the value out, and MEMOIZE is such a channel.
; Measured in isolation: prog2$ alone 0, memoize alone 0, both 1.
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun g (x)
  (declare (xargs :guard t))
  (ec-call (apply$-lambda '(lambda (y) (return-last 'cons y '3)) (list x))))
(memoize 'g)
(defun f (x)
  (declare (xargs :guard t))
  (prog2$ (g x) (g x)))

; THE DEFECT: (f 1) evaluates to (1 . 3) through the compiled lambda cache while
; its logical value is 3.
(must-fail (defthm bad1 (equal (f 1) '(1 . 3)) :rule-classes nil))

; The logical value, which must remain provable: this is the honest half.
(defthm logical-value
  (equal (f 1) 3)
  :hints (("Goal" :in-theory (disable (:executable-counterpart f)
                                      (:executable-counterpart g))))
  :rule-classes nil)

; CONTROL 1: the same shape with a LEGITIMATE key must keep working -- 'progn is
; in return-last-table, and both paths give 3.  So the fix cannot be "stop
; keeping return-last in a quoted lambda" wholesale, which would undo the
; Finding 35 / N148 repair.
(defthm control-progn-ok
  (equal (ec-call (apply$-lambda '(lambda (y) (return-last 'progn y '3)) (list 1))) 3)
  :rule-classes nil)

; CONTROL 2: a DEFUN cannot do this -- translate refuses the illegal key.  This
; pins that the quoted-LAMBDA path is the hole, not return-last itself.
(must-fail (defun r1 (x) (declare (xargs :guard t)) (return-last 'cons x 3)))
