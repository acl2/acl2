; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-200 (lead F1-5817, stage-2 batch G58): when a signature rule's hypothesis tau has a :pos-evg, tau-implies
; compares only that constant and ignores the recognizers kept beside it, so a vacuous :type-prescription
; rule fires.  Proves nil and certifies, no trust tags: SBCL and CCL at 21aaad6 and 947ff84343.
; Control: with P defined and evaluable, LEMMA fails.
;
; G58 candidate (soundness): tau-implies ignores the recognizers of a formal
; tau that has a :pos-evg.
;
; tau-implies (tau.lisp:3767) decides whether the tau of an actual implies the
; tau required by a signature rule (its only caller is
; ok-to-fire-signature-rulep1).  When the required tau2 has a :pos-evg it
; returns (equal pos-evg2 pos-evg1) and never looks at tau2's :pos-pairs and
; :neg-pairs.  But add-to-tau1 (tau.lisp:4609-4649) keeps a recognizer in those
; lists next to a :pos-evg whenever ev-fncall-w-tau-recog cannot evaluate it on
; the evg (a constrained function, or one whose executable counterpart is
; disabled).  So a signature rule whose hypotheses say x = 'c AND (p x), with
; (p 'c) unevaluable, fires on every actual whose tau is x = 'c, as if (p 'c)
; were known.  If (p 'c) is false the rule is vacuous, and firing it proves
; anything about (f 'c).
;
; Here F-TYPE is an ordinary :type-prescription rule (tau automatic mode, the
; default, turns it into a signature rule).  LEMMA is proved by tau, with F
; disabled.
;
; Control: with P defined and its executable counterpart enabled (P = (equal x
; 'd)), adding (p x) to x = 'c is a contradiction, no signature rule is stored,
; and LEMMA fails.  Variants (all prove nil): a :tau-system rule class; a
; negated hypothesis (not (q x)) with (q 'c) true; P defined with (:e p)
; disabled.  Proves nil by ld and certifies (no ttag) on SBCL and CCL at
; 21aaad6, 9a589490e6 and 15e42ee881.
(in-package "ACL2")
(encapsulate ((p (x) t))
  (local (defun p (x) (declare (ignore x)) nil))
  (defthm booleanp-p (booleanp (p x)) :rule-classes :tau-system)
  (defthm p-c-false (not (p 'c)) :rule-classes nil))
(defun f (x) (declare (ignore x)) 'abc)
(in-theory (disable f (:e f) (:t f)))
(defthm f-type
  (implies (and (equal x 'c) (p x)) (integerp (f x)))
  :hints (("Goal" :use p-c-false))
  :rule-classes :type-prescription)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm lemma (integerp (f 'c)) :rule-classes nil)
)

; The following were commented out by Matt K. since the defun just above now
; fails.
#|
(defthm nil-proved nil
  :hints (("Goal" :use lemma :in-theory (enable f)))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
