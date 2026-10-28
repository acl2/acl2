; This book, modified only as noted below by Matt Kaufmann, was produced by
; Claude and passed along by Eric Smith.  It illustrates a soundness bug fixed
; before ACL2 Version 8.8.

; But first, a note from J Moore:

; AI discovered a soundness bug in the source code function
; clause-set-subsumes-1, which tries to answer the question whether one set of
; first order clauses subsumes another, but imposes a budget on how many times
; unification can be tried.  The bug was a mishandling of the ``don't know''
; answer when the budget was exhausted and was fixed by a simple change to the
; accumulator.

(in-package "ACL2") ; Added by Matt K. to make a certifiable book

; Added by Matt K.:
(include-book "std/testing/must-fail" :dir :system)

(defun my-le (x y) (<= (nfix x) (nfix y)))   ; not symmetric

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm my-le-is-an-equivalence
   (and (booleanp (my-le x y))
        (my-le x x)
        ;; trivially true; its 22 variable literals make the symmetry
        ;; check give up but the buggy function reports t.
        (implies (and (not p1) (not p2) (not p3) (not p4) (not p5)
                      (not p6) (not p7) (not p8) (not p9) (not p10)
                      (not p11) (not p12) (not p13) (not p14) (not p15)
                      (not p16) (not p17) (not p18) (not p19) (not p20)
                      (not p21) (not p22))
                 (equal q q))
        (implies (and (my-le x y) (my-le y z)) (my-le x z)))
   :rule-classes :equivalence)
)

(must-fail ; This must-fail wrapper was added by Matt K.
(defthm bad (implies (my-le a b) (my-le b a)) :rule-classes nil)
)

(must-fail ; This must-fail wrapper was added by Matt K.
(thm nil :hints (("Goal" :use (:instance bad (a 0) (b 1)))))
)
