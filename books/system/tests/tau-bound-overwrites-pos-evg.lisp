; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-199 (lead F1-5834, stage-2 batch G59): two bounds added to a tau whose :pos-evg is a non-rational
; constant replace that constant, so a vacuous :type-prescription rule becomes the false signature
; (integerp (f -1)).  Proves nil and certifies, no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.
; Control: with (equal x nil) listed first, LEMMA fails.
;
; G59 candidate (soundness): adding two bounds to a tau that already says
; x = <non-rational constant> replaces that constant with the bound.
;
; add-to-tau1 (tau.lisp ~4577) handles a signed (k . :lessp-x-k) or
; (k . :lessp-k-x) by calling tighten-bound directly, even when the tau has a
; :pos-evg (for tau-pairs it evaluates the recognizer on the evg instead,
; ~4609).  A non-rational :pos-evg such as NIL has no identity interval, so
; tighten-bound builds an interval from the bounds alone; once the two bounds
; meet (here -1 <= x <= -1, domain ACL2-NUMBERP) its singleton case calls
; set-tau-pos-evg (~4404), which overwrites the :pos-evg NIL with -1.  The tau
; for "x = nil, x <= -1, -1 <= x" (unsatisfiable) thus becomes "x = -1".
;
; Tau builds the hypothesis tau of a signature rule from the hypotheses last to
; first with add-to-tau1, so the vacuous :type-prescription rule F-TYPE (tau
; automatic mode, the default) becomes the signature rule
; "(integerp (f -1))", which is false.
;
; Control: with (equal x nil) listed first (so it is added last) the
; contradiction is detected, no signature rule is stored, and LEMMA fails.
(in-package "ACL2")

(defun f (x) (if (equal x -1) 'a 0))

(defthm f-type
  (implies (and (<= -1 x)
                (<= x -1)
                (equal x nil))
           (integerp (f x)))
  :rule-classes :type-prescription)

(in-theory (disable f (:e f)))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm lemma
  (integerp (f -1))
  :rule-classes nil)
)

; The following were commented out by Matt K. since the defthm just above now
; fails.
#|
(defthm nil-proved nil
  :hints (("Goal" :use lemma
                  :in-theory (enable (:e f))))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
