; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-143, third reproducer (stage-2 batch G17): the mid-event world is that of a
; defun inside a make-event expansion that is discarded.  Proves nil (plain
; ld) on SBCL and CCL at 21aaad6 and 227bafe2d1.
(in-package "ACL2")
(defconst *L*
  '(lambda (x)
     (declare (xargs :guard (consp (g x)) :split-types t))
     (zp x)))
(defun p (x)
  (declare (xargs :guard t))
  (prog2$ (if (equal x 'c) (apply$ *L* (list 0)) nil)
          (consp x)))
(make-event (er-progn (defun g (x)
                       (declare (xargs :guard t))
                       (or (p x) (equal x 'c)))
                     (value '(value-triple :expansion-discarded))))
(value-triple (cw "~%g function-symbolp: ~x0~%" (function-symbolp 'g (w state))))
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
