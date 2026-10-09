; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 50: CNF-DNF (tau.lisp:8722) chooses its combinator from CNFP alone and
; ignores SIGN, so the DNF it builds for a rule's hypothesis is WEAKER than the
; hypothesis actually proved.  Every tau rule derived from that hypothesis is then
; stronger than the theorem it came from, and nil follows.
;
; The contract CNF-DNF is supposed to satisfy is that its result, read as a CNF
; when CNFP is on and as a DNF when CNFP is off, is equivalent to SIGN/TERM.
; For the four IF shapes the combinator must therefore be chosen from
; (if sign cnfp (not cnfp)), not from cnfp: with sign off, (if x y nil) means
; ~x \/ ~y, so its DNF is an APPEND and its CNF is a CROSS-PROD -- the opposite of
; what the code picks.  The NOT case at :8754 flips both sign and cnfp and so
; stays consistent; the two implication/disjunction cases at :8775/:8777 and
; :8781/:8783 flip sign only, which is how a negative sign reaches the AND case.
;
; Concretely, with hypothesis  (if (if (r1 v) (rationalp v) t) (consp v) t),
; i.e.  (p1 -> rat) -> p2,  i.e.  (p1 & ~rat) \/ p2:
; SPLIT-ON-CONJOINED-DISJUNCTIONS-IN-HYPS-OF-PAIRS receives the three
; INDEPENDENT hypotheses p1, ~rat, p2 instead of the two disjuncts, and stores
; (among others) the rule (implies (r1 v) (not (r2 v))), which is
; (implies (integerp v) (not (integerp v))).
;
; Since (p1 v) implies (rationalp v), the conjunct (p1 & ~rat) is FALSE and the
; hypothesis is just (consp v), so BAD-TP / BAD-TAU below are the true theorem
; (implies (consp v) (not (integerp v))).  Nothing unsound is asserted by the
; user anywhere in this book.
;
; POLARITY: the MUST-FAILs state the CORRECT behaviour -- the false formula
; BAD-INST must not be provable.  The book is RED while the defect is present
; and turns GREEN when cnf-dnf takes sign into account.
;
; Two routes, because the fix must close both:
;   A. an explicit :TAU-SYSTEM rule class;
;   B. an ordinary :TYPE-PRESCRIPTION rule, mined by tau in its DEFAULT auto
;      mode -- no :tau-system rule class anywhere, which is the wide version.
;
; The CONTROL at the end is the honest conjunctive-hypothesis rule: a correct
; fix must leave it both storable and usable, so the repair cannot be "stop
; mining hypotheses".
;
; No trust tag, no skip-proofs, no defaxiom.  Books: tau2/{minimal,cnfdnf,tp}.lisp.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(tau-status :system t)

(defun r1 (v) (if (integerp v) t nil))
(defun r2 (v) (if (integerp v) t nil))

; ---- route A: explicit :tau-system rule class ----------------------------
; A true theorem; its hypothesis is propositionally just (consp v).
(defthm bad-tau
  (implies (if (if (r1 v) (rationalp v) t) (consp v) t)
           (not (r2 v)))
  :rule-classes :tau-system)

; THE DEFECT.  (implies (integerp x) (not (integerp x))) is false, and tau
; proves it alone from the mis-split hypothesis of BAD-TAU.
; (:instance bad-inst (x 0)) then gives nil outright.
(must-fail
 (defthm bad-inst
   (implies (r1 x) (not (r2 x)))
   :hints (("Goal" :in-theory (disable r1 r2 (:e r1) (:e r2))))
   :rule-classes nil))

; ---- route B: no :tau-system rule class at all ---------------------------
; Tau auto mode is on by default, so an ordinary :type-prescription corollary
; goes through the same split-on-conjoined-disjunctions pipeline.
(defun q1 (v) (if (integerp v) t nil))
(defun q2 (v) (if (integerp v) t nil))

(defthm bad-tp
  (implies (if (if (q1 v) (rationalp v) t) (consp v) t)
           (not (q2 v)))
  :rule-classes ((:type-prescription :typed-term (q2 v))))

(must-fail
 (defthm bad-inst-tp
   (implies (q1 x) (not (q2 x)))
   :hints (("Goal" :in-theory (disable q1 q2 (:e q1) (:e q2))))
   :rule-classes nil))

; ---- CONTROL: the honest conjunctive hypothesis must survive the fix -----
(defun c1 (v) (if (consp v) t nil))
(defun c2 (v) (if (true-listp v) t nil))
(defun c3 (v) (if (integerp v) t nil))

; (c1 v) & (c2 v) --> ~(c3 v).  True, and correctly stored today.
(defthm honest-tp
  (implies (if (c1 v) (c2 v) nil)
           (not (c3 v)))
  :rule-classes ((:type-prescription :typed-term (c3 v))))

(defthm honest-use
  (implies (if (c1 x) (c2 x) nil) (not (c3 x)))
  :hints (("Goal" :in-theory (disable c1 c2 c3 (:e c1) (:e c2) (:e c3))))
  :rule-classes nil)
