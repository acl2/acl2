; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-277: tau-boolean-formp accepts (booleanp (not x)), so NOT becomes a tau recognizer; a conjunctive rule whose conclusion is (not (not x)) is then stored with a negated conclusion that tau cannot parse, read as "x /= NIL" and dropped, and tau proves a false theorem. Three ordinary defthms.
; Expected: proves nil (prints NIL-PROVED); default theory, no trust tags; certifies; SBCL and CCL.
;
; G166 candidate (soundness): a Boolean rule about NOT makes NOT a tau
; recognizer, and add-tau-conjunctive-rule then reads the negated conclusion
; of a rule (not (not x)) as the non-tau-like term (NOT X), whose all-NIL
; "recognizer" add-to-tau1 takes as the literal x /= NIL.
;
; tau-boolean-formp (tau.lisp ~7160) accepts any (booleanp (f v)), so
; NOT-IS-BOOLEAN (a plain :rewrite rule; tau is in automatic mode by default)
; gives NOT a tau-pair through add-tau-boolean-rule, although
; monadic-boolean-fnp excludes NOT (*non-tau-monadic-boolean-functions*).
; Now tau-like-term parses the conclusion (NOT (NOT X)) of POS-INT-NON-NIL as
; the literal -NOT(x), so tau-conjunctive-formp accepts the rule.
; add-tau-conjunctive-rule negates the conclusion by stripping one NOT, giving
; (NOT X); tau-like-term returns (mv nil nil nil nil) for it, and
; convert-tau-like-terms-to-tau passes sign NIL and recog NIL to add-to-tau1,
; which treats recog NIL (discriminator NIL) as an excluded constant (car NIL)
; = NIL.  Adding INTEGERP then drops that "exclusion" as redundant, so the
; stored conjunctive rule is {integerp, 1 <= x}, i.e. "no integer is >= 1",
; and tau proves BAD-LEMMA.
;
; Control: without NOT-IS-BOOLEAN, BAD-LEMMA fails.
(in-package "ACL2")

(defthm not-is-boolean (booleanp (not x)))

(defthm pos-int-non-nil
  (implies (and (integerp x) (< 0 x)) (not (not x))))

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad-lemma
  (implies (integerp x) (<= x 0))
  :rule-classes nil)
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defthm bad nil
  :rule-classes nil
  :hints (("Goal" :use ((:instance bad-lemma (x 1))))))

(value-triple (cw "~%NIL-PROVED~%"))
|#
