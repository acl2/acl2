; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-143 (lead F1-178, stage-2 batch G17): a cl-cache line can be validated
; while an event's world is installed but its event landmark is not yet
; added (install-event runs tau-visit-event after update-w and before
; add-event-landmark); the line is then stamped with the pre-event maximum
; event number, so a retraction to another world with the same maximum (here
; the end of encapsulate pass 1, which drops the LOCAL G) leaves it :GOOD.
; Tau evaluates P on the constant C, which applies the LAMBDA; its guard
; (consp (g x)) normalizes to NIL under the local G, so the line is :GOOD with
; no obligations.  With the new G the guard holds and the compiled code runs
; raw ZP on -1 (raw NIL, logically T); a clause processor proves nil.
; Proves nil and certifies, no trust tags, no books: SBCL and CCL, 21aaad6 and
; 227bafe2d1.  Control: without the encapsulate, BAD fails.
(in-package "ACL2")
(defconst *L*
  '(lambda (x)
     (declare (xargs :guard (consp (g x)) :split-types t))
     (zp x)))
(defun p (x)
  (declare (xargs :guard t))
  (prog2$ (if (equal x 'c) (apply$ *L* (list 0)) nil)
          (consp x)))
(encapsulate
  ()
  (local (defun g (x)
           (declare (xargs :guard t))
           (or (p x) (equal x 'c))))
  (defthm triv t :rule-classes nil))
(defun g (x) (declare (xargs :guard t)) (cons x x))
(defevaluator evl evl-list ((if x y z)))
(defun cp (cl)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (apply$-lambda *L* (list -1)) t)
      (list cl)
    nil))
(defthm cp-correct
  (implies (and (pseudo-term-listp cl) (alistp a)
                (evl (conjoin-clauses (cp cl)) a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad nil
  :hints (("Goal" :clause-processor (cp clause)))
  :rule-classes nil)
)

; The following was commented out by Matt K. since the event just above now
; fails.
; (value-triple (cw "~%NIL-PROVED~%"))
