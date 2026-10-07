; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; Soundness bug: :REFINEMENT rule stored in pass 2 of ENCAPSULATE without the
; equivalence-relationp check (chk-acceptable-rules skips everything except
; :meta/:clause-processor/:congruence when ld-skip-proofsp is 'include-book).
; add-refinement-rule then gives EQV a 'coarsenings property, so ACL2 treats
; EQV as a known equivalence relation even though nothing was proved about it.
(in-package "ACL2")

(defun triv (x y) (declare (ignore x y)) t)

(defequiv triv)

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(encapsulate
  (((eqv * *) => *))
  (local (defun eqv (x y) (declare (ignore x y)) t))
  (local (defequiv eqv))            ; LOCAL: makes EQV an equivalence in pass 1 only
  (defthm eqv-refines-triv          ; non-local, trivially true
    (implies (eqv x y) (triv x y))
    :rule-classes :refinement))
)

;; Commented out by Matt Kaufmann (as the rest of the file is irrelevant after
; the bug fix):

#|
 The only constraint on EQV is (implies (eqv x y) (triv x y)), i.e. nothing:
; TRIV is constantly T.  Yet ACL2 now "proves" that EQV is reflexive.
(defthm eqv-reflexive
  (eqv x x)
  :rule-classes nil)

(defthm nil-proved
  nil
  :hints (("Goal" :use (:functional-instance eqv-reflexive
                                             (eqv (lambda (x y) nil)))))
  :rule-classes nil)
|#
