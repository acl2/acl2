; (Note from Matt Kaufmann and J Moore:) This book was mostly produced by
; Claude and passed along by Eric Smith, as explained below.  It illustrates a
; soundness bug introduced by a fix to an ACL2 Version 8.7 soundness bug as
; described in the book tau-cnf-dnf-not-cnfp.lisp in this directory.  This was
; however not a soundness bug in ACl2 Version 8.7.

(in-package "ACL2") ; added by Matt and J to make this a book

; Events from Claude, preceded by its comment:

#|
Heads-up: while surveying targets I found what looks like a live soundness bug
in the current testing-kestrel sources (tau’s cnf-dnf), and I’ve confirmed it
with a proof of nil on an ACL2 I rebuilt from 91c653f:
|#

(defthm not-int-or-string            ; true
   (implies (not (or (integerp x) (stringp x)))
            (not (natp x)))
   :rule-classes :tau-system)

(include-book "std/testing/must-fail" :dir :system) ; added post-Claude

(must-fail ; wrapper added post-Claude
(defthm bad                          ; false, proved by tau
   (implies (natp x) (stringp x))
   :hints (("Goal" :in-theory (disable natp)))
   :rule-classes nil)
)

; Commented out because of the must-fail above:
#|
(thm nil :hints (("Goal" :use (:instance bad (x 3)))))   ; Proof succeeded
|#

; A further comment from Claude:

#|
Cause: the recent fix to cnf-dnf (the cnfp1 change for Findings 50/51) left the
NOT case flipping cnfp: (cnf-dnf (not sign) (fargn term 1) (not cnfp)). The
result of the recursive call is then read in the wrong normal form, so (cnf-dnf
t '(not (if a a b)) nil) = (((NOT A)) ((NOT B))), i.e. ¬a ∨ ¬b instead of ¬a ∧
¬b, and the tau rule is split into two rules that are each stronger than the
theorem. The one-line fix is to pass cnfp unchanged in the NOT case. The Oct 6
ACL2 image (before the cnfp1 change) does not prove bad, so this looks like a
regression from that fix."
|#
