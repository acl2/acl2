; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 46: CLAUSIFY can return a clause set STRICTLY STRONGER than its input,
; and two consumers accept those clauses as individually valid.
;
; Chain, all at f0c63a9627:
;  1. if-interp-assume-true (rewrite.lisp:3139) recurses through EVERY NOT, while
;     if-interp-assumed-value (rewrite.lisp:3348) strips exactly ONE and then calls
;     if-interp-assumed-value-x (rewrite.lisp:3315), which has no NOT case at all.
;     Measured: (if-interp-assumed-value '(NOT (NOT A)) '(A)) = NIL.
;  2. call-stack (rewrite.lisp:3584, fn='NOT) deliberately refuses to collapse
;     (NOT (NOT x)) -- the Qiang Zhang Version_2.7 note at :3600-3616 -- so the
;     double negation really does reach if-interp as a test value.  if-interp then
;     records CONTRADICTORY assumptions on one path.
;  3. convert-assumptions-to-clause-segment (rewrite.lisp:3366) builds the clause
;     with plain CONS and never calls add-literal / member-complement-term, so the
;     propositional tautology SURVIVES into the clause set.
;  4. subsumption-replacement-loop (rewrite.lisp:4455) then does exactly what its
;     own "Caution:" comment (:4463-4470) warns about: it uses the tautology as a
;     replacement-resolution parent, and the output no longer implies the input.
;
; Measured on the term below:
;   strip-branches          ((A (NOT C) (NOT A) B) (A (NOT A) B))   both tautologies
;   clausify ... sr 500     (((NOT C) (NOT A) B) (A (NOT A) B))     1st is FALSE
;   clausify ... sr 1       ((A (NOT C) (NOT A) B) (A (NOT A) B))   loop skipped, sound
;
; This book pins BOTH reachable consumers.  It certifies exactly when neither
; route works, i.e. when the defect is fixed.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; A genuine propositional tautology -- T on all eight assignments, Q.E.D. with
; Rules: NIL.  Nothing about it is unusual except the (NOT (NOT A)) subterm.
(defthm f46-taut
  (if (if t (if a a (if c c t)) t)
      (if a a (if (not (not a)) b t))
      t)
  :rule-classes nil)

; ROUTE 1 -- the :BY hint.  No rule class, no trust tag: apply-top-hints-clause
; clausifies the lemma's formula (prove.lisp:1483) and accepts the goal on
; clause-set-subsumes (:1489-1513).
(must-fail
 (local (defthm f46-boom-by
          (implies (and a c) b)
          :hints (("Goal" :by f46-taut))
          :rule-classes nil)))

; ROUTE 2 -- :rule-classes :built-in-clause.  make-built-in-clause-rules
; (defthm.lisp:2872, clausify at :2880) stores EACH clause as a known truth;
; chk-acceptable-built-in-clause-rule2 (:2699) checks only non-emptiness.
(must-fail
 (local (encapsulate ()
          (defthm f46-bic
            (if (if t (if a a (if c c t)) t)
                (if a a (if (not (not a)) b t))
                t)
            :rule-classes :built-in-clause)
          (defthm f46-boom-bic (implies (and a c) b) :rule-classes nil))))

; CONTROL: the tautology itself must still be provable, and must still be
; provable the ordinary way.  If this fails the harness is broken, not ACL2.
(defthm f46-control-taut-still-provable
  (if (if t (if a a (if c c t)) t)
      (if a a (if (not (not a)) b t))
      t)
  :rule-classes nil)

; CONTROL: the false formula must remain unprovable without the bad route.
(must-fail (local (defthm f46-control-false (implies (and a c) b) :rule-classes nil)))
