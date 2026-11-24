; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-200 (lead F1-5817, stage-2 batch G58): a second route through the interval, which also needs the
; S-199 branch (the bound is not checked against the :pos-evg).  Proves nil and certifies, no trust tags:
; SBCL and CCL at 21aaad6 and 947ff84343.  Control: hypotheses in the other order, and LEMMA fails.
;
; G58 candidate (soundness), second route for G58-tau-implies-pos-evg-ignores-pairs:
; tau-implies ignores the :interval of a formal tau that has a :pos-evg.
;
; The hypothesis tau of F-TYPE is built last hypothesis first: (equal x :k)
; gives :pos-evg :K, then add-to-tau1's :lessp branch adds the bound 2 <= x via
; tighten-bound without checking it against the :pos-evg (the G59 F1-5834
; branch), leaving the unsatisfiable tau "x = :K and x in [2, oo) over
; ACL2-NUMBERP" instead of *tau-contradiction*.  That tau is still exact (it
; describes no object, like the hypotheses), but tau-implies compares only the
; :pos-evgs, so the vacuous signature rule fires on the actual :K.
;
; Control: with the hypotheses in the other order the contradiction is found,
; no signature rule is stored, and LEMMA fails.  Proves nil by ld and
; certifies (no ttag) on SBCL and CCL at 21aaad6, 9a589490e6 and 15e42ee881.
(in-package "ACL2")
(defun f (x) (declare (ignore x)) 'abc)
(in-theory (disable f (:e f) (:t f)))
(defthm f-type
  (implies (and (<= 2 x) (equal x :k)) (integerp (f x)))
  :rule-classes :type-prescription)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm lemma (integerp (f :k)) :rule-classes nil)
)

; The following were commented out by Matt K. since the defthm just above now
; fails.
#|
(defthm nil-proved nil
  :hints (("Goal" :use lemma :in-theory (enable f)))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
