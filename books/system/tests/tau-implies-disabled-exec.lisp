; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-200 (lead F1-5817, stage-2 batch G58): the same with a defined P whose executable counterpart is
; disabled.  Proves nil and certifies, no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.
;
(in-package "ACL2")
; Variant: P is an ordinary defined function whose executable counterpart is
; disabled, so tau cannot evaluate (P 'D).
(defun p (x) (equal x 'd))
(defun f (x) (declare (ignore x)) 'abc)
(in-theory (disable p (:e p) f (:e f) (:t f)))
(defthm f-type
  (implies (and (equal x 'd) (not (p x))) (integerp (f x)))
  :hints (("Goal" :in-theory (enable p)))
  :rule-classes :type-prescription)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm lemma (integerp (f 'd)) :rule-classes nil)
)

; The following were commented out by Matt K. since the defthm just above now
; fails.
#|
(defthm nil-proved nil
  :hints (("Goal" :use lemma :in-theory (enable f)))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
