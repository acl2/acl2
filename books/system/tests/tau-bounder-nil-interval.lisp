; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-209 (lead F1-5962, stage-2 batch G70): tau passes a bounder the ill-formed interval (NIL) for an argument
; it knows nothing about, which the bounder's correctness theorem does not cover.  Proves nil and certifies,
; no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.  Control: a bounder that returns its interval.
;
; Proof of nil: tau passes a bounder an ill-formed interval when an argument's
; tau has no interval (the universal interval is represented by NIL, and
; collect-bounder-args turns it into (change tau-interval nil :domain nil) =
; (NIL), which is not a TAU-INTERVALP).  The bounder correctness theorem says
; nothing about such an argument, so the bounder can return any interval.

(in-package "ACL2")

(defun f (x) (declare (xargs :guard t)) x)

; Correct on every well-formed interval; returns [5,5] otherwise.
(defun bnd (i)
  (declare (xargs :guard t))
  (if (tau-intervalp i)
      i
    (make-tau-interval 'integerp nil 5 nil 5)))

(defthm bnd-correct
  (implies (and (tau-intervalp i)
                (in-tau-intervalp x i))
           (and (tau-intervalp (bnd i))
                (in-tau-intervalp (f x) (bnd i))))
  :rule-classes :tau-system)

(in-theory (disable f))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
; Proved by tau alone: x has no tau information, so bnd gets (NIL).
(defthm f-is-5
  (equal (f x) 5)
  :rule-classes nil)
)

; The following were commented out by Matt K. since the defthm just above now
; fails.
#|
(defthm nil-proved nil
  :rule-classes nil
  :hints (("Goal" :use ((:instance f-is-5 (x 3)))
           :in-theory (enable f))))

(value-triple (cw "~%NIL-PROVED~%"))
|#
