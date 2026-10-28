; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; But first, a note added by J Moore:

; AI discovered a bug in our forward-chaining, specifically in the source code
; function advance-fc-activation2.  We failed to account for free variables
; properly when calling that function and the bug allowed capture and thus
; unsoundness.

; Finding 47: forward chaining FORCEs a free-variable hypothesis under one
; substitution and instantiates the rule's CONCLUSION under a different one.
;
; Site: advance-fc-activation1, simplify.lisp:2910-2939.  The branch binds
;   (fully-bound-unify-subst (bind-free-vars-to-unbound-free-vars (all-vars hyp)
;                                                                 unify-subst))
; forces (sublis-var fully-bound-unify-subst hyp) -- i.e. hyp[y := UNBOUND-FREE-Y] --
; and then recurses with UNIFY-SUBST, in which y is still unbound.  So the
; obligation ACL2 promises to discharge is about UNBOUND-FREE-Y while the
; conclusion asserted into the type-alist is about the clause variable y.
;
; The rewriter's analogous code does it right: relieve-hyps1-free-2
; (rewrite.lisp:18528) binds fully-bound-unify-subst at :18558, forces with it at
; :18572, and CONTINUES WITH IT at :18603.  Two implementations of one idea that
; disagree.
;
; Soundness therefore rests on UNBOUND-FREE-<v> being fresh for the conjecture --
; and ACL2's own warning in chk-triggers (defthm.lisp:3389-3400) says of exactly
; this renaming: "This is not guaranteed to generate a new variable but at least
; it generates an unusual one."  Nothing checks it against the clause.
;
; FIX: pass fully-bound-unify-subst at simplify.lisp:2935, matching
; rewrite.lisp:18603.  That is sufficient independently of freshness.
;
; This book uses CASE-SPLIT rather than FORCE deliberately: with FORCE an
; undischargeable instance sends the prover through unbounded forcing rounds
; (25,458 observed before being killed -- recorded separately), whereas with
; CASE-SPLIT the failure is immediate, so the control terminates.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun f47-small (y) (equal y 0))
(defun f47-tiny  (y) (f47-small y))

(defthm f47-tiny-implies-small (implies (f47-tiny y) (f47-small y)))
(defthm f47-small-implies-zero (implies (f47-small y) (equal y 0)) :rule-classes nil)

; disabled only so expand-abbreviations does not erase the trigger term before
; simplify-clause1 runs -- nothing here depends on the disabling for soundness.
(in-theory (disable f47-tiny f47-small
                    (:type-prescription f47-tiny) (:type-prescription f47-small)))

; An ordinary theorem.  y is free in the hypothesis relative to the trigger.
(defthm f47-rule
  (implies (case-split (f47-small y)) (equal y 0))
  :hints (("Goal" :use f47-small-implies-zero))
  :rule-classes ((:forward-chaining :trigger-terms ((f47-tiny x)) :match-free :all)))

; FALSE: take unbound-free-y = 0 and y = 1.
(must-fail
 (local (defthm f47-bad
          (implies (f47-tiny unbound-free-y) (equal y 0))
          :rule-classes nil)))

; CONTROL: the same shape with a conjecture variable that does NOT collide with
; the generated name must fail too -- and must fail for the ordinary reason.
; If this ever succeeds the defect has widened beyond variable capture.
(must-fail
 (local (defthm f47-control-no-collision
          (implies (f47-tiny w) (equal y 0))
          :rule-classes nil)))

; CONTROL: the rule itself must remain usable for what it legitimately proves.
(defthm f47-control-legit
  (implies (f47-tiny y) (equal y 0))
  :hints (("Goal" :in-theory (enable f47-tiny f47-small)))
  :rule-classes nil)
