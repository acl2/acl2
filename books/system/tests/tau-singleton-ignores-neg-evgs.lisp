; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; S-276: tau's tighten-bound turns the unsatisfiable tau (x /= 0, 0 <= x <= 0, then a numeric domain) into x = 0, so a true :forward-chaining theorem becomes a false conjunctive tau rule.
; Expected: proves nil (prints NIL-PROVED); no trust tags; certifies; SBCL and CCL.
;
; G165 candidate (soundness): tighten-bound's singleton case ignores :neg-evgs.
;
; In the unrestricted (NIL) domain, adjust-upper/lower-bound-with-neg-evgs
; (tau.lisp ~4108, ~4145) and add-to-tau1's x /= evg branch (~4536)
; deliberately leave a weak bound 0 weak when 0 is excluded, because
; non-numbers satisfy x <= 0 but not x < 0.  So "x /= 0, 0 <= x, x <= 0" is
; stored as the NIL-domain interval [0,0] with :neg-evgs ((0)), which is exact
; (it means: x is a non-number).  When a numeric recognizer (INTEGERP,
; RATIONALP, ACL2-NUMBERP, NATP) is added afterwards, tighten-bound changes the
; domain but leaves both bounds unchanged, so it skips the neg-evgs adjustment
; (it runs it only for a bound that changed, ~4354-4366), finds the singleton
; interval 0 <= x <= 0 with a non-nil domain and calls set-tau-pos-evg with 0
; (~4394-4404) without checking that 0 is in :neg-evgs.  The unsatisfiable set
; "integer, 0 <= x <= 0, x /= 0" becomes the tau "x = 0".
;
; Tau builds conjunctive-rule taus from the hypotheses and the negated
; conclusion, last first (convert-tau-like-terms-to-tau), so the TRUE theorem
; below (a :forward-chaining rule, which tau's default automatic mode also
; turns into a conjunctive tau rule) is stored as the conjunctive rule {x = 0},
; i.e. "x is never 0".  Tau then proves (not (equal x 0)).
;
; The same defect makes a signature rule's hypothesis tau satisfiable: see
; G165-tau-singleton-ignores-neg-evgs-signature.lisp.
;
; Control: with (integerp x) as the last hypothesis (added first), the bounds
; go through the INTEGERP adjustment, the rule's tau is a contradiction, no
; conjunctive rule is stored and LEMMA fails.
(in-package "ACL2")

(defthm integer-between-0-and-0
  (implies (and (integerp x)
                (<= 0 x)
                (<= x 0))
           (equal x 0))
  :rule-classes :forward-chaining)

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm lemma
  (not (equal x 0))
  :rule-classes nil)
)

; The following were commented out by Matt K. since the event just above now
; fails.
#|
(defthm nil-proved nil
  :hints (("Goal" :use ((:instance lemma (x 0)))))
  :rule-classes nil)

(value-triple (cw "~%NIL-PROVED~%"))
|#
