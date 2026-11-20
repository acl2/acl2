; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-198 (lead F1-5833, stage-2 batch G59): when (NIL) heads a tau's :neg-evgs, adding a bound drops the
; numeric exclusions, so the hypothesis tau of a plain :type-prescription rule loses (not (equal x -3)).
; Proves nil and certifies, no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.
; Control: without the hypothesis (not (equal x nil)), LEMMA fails.
;
; G59 candidate (soundness): tau drops an excluded constant from a rule's
; hypothesis tau when (NIL) heads the :neg-evgs.
;
; collect-<?-x-k and collect-<?-k-x (tau.lisp ~4016, ~4052), called by
; adjust-upper/lower-bound-with-neg-evgs from tighten-bound, assume that the
; :neg-evgs list is in lexorder, so that once they reach a non-number every
; remaining element is a non-number.  But a :neg-evgs list keeps (NIL) FIRST
; (tau.lisp ~31-40, insert-neg-evgs), before any numbers.  When (NIL) is
; present they treat the whole list as non-numeric and keep it or drop it
; wholesale.  For the upper bound (< x -1), (< 0 -1) is false, so they drop
; every element, including the numeric exclusion -3 that lies inside the new
; interval.
;
; In a goal, dropping a fact only weakens tau.  But tau also builds the
; hypothesis tau of signature rules (and the tau of conjunctive rules) with
; add-to-tau1, processing the hypotheses last to first.  For the
; :type-prescription rule F-TYPE below (tau automatic mode, the default), the
; hypotheses x /= nil, x /= -3, x < -1 become the tau "x < -1": the rule then
; fires on x = -3, where it is false.
;
; Control: without the hypothesis (not (equal x nil)) the hypothesis tau keeps
; (-3) and LEMMA fails.  The conjunctive-rule form ((implies (and (< x -1) (not
; (equal x -3)) (not (equal x nil))) (q x)) :rule-classes :tau-system) and the
; lower-bound mirror ((< 1 x), x /= 3) also prove nil.
(in-package "ACL2")

(defun f (x) (if (equal x -3) 'a 0))

(defthm f-type
  (implies (and (< x -1)
                (not (equal x -3))
                (not (equal x nil)))
           (integerp (f x)))
  :rule-classes :type-prescription)

(in-theory (disable f (:e f)))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm lemma
  (implies (< x -1) (integerp (f x)))
  :rule-classes nil)
)

; The following were commented out by Matt K. since the defthm just above now
; fails.
#|
(defthm nil-proved nil
  :hints (("Goal" :use ((:instance lemma (x -3)))
                  :in-theory (enable f)))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
