; This book, modified by Matt Kaufmann only in the addition of this paragraph
; and as noted below, was produced by Claude and passed along by Eric Smith.
; It illustrates a soundness bug fixed before ACL2 Version 8.8.  Interestingly,
; my initial fix was in source function
; cert-data-tp-from-runic-type-prescription, to check that the :corollary
; contains only known function symbols.  But Claude's suggested fix is probably
; better: guarded-termp indeed failed to descends into its arguments for the
; call of a function symbol, and that needed to be fixed and was sufficient.

; Finding 38: guarded-termp (defuns.lisp) checks only the HEAD symbol of a term
; and never descends into the arguments, contradicting its own comment ("we
; check that in addition, x is a termp in w by checking that all function
; symbols are defined in w").  It is the gate that decides whether a
; :type-prescription :corollary carried in cert-data may be reused in another
; world, so a corollary mentioning a LOCAL-only function survives into the
; including world, where that name can be defined to mean anything.
;
; With the bug present, certdata/cd1 installs (:type-prescription FC) whose
; corollary mentions MYCONSP while MYCONSP is absent from the world; defining
; MYCONSP to be constantly nil then makes the stored rule false, and NIL
; follows.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "cert-data/cd1")

; First guard: the world should not contain a rule about an undefined function.
(must-fail
 (assert-event
  (let ((tp (car (getpropc 'fc 'type-prescriptions nil (w state)))))
    (and tp
         (not (eq (getpropc 'myconsp 'formals t (w state)) t))))))

; Second guard: and even if it does, the rule must not be usable to prove nil.
(must-fail
 (progn
   (defun myconsp (x) (declare (ignore x)) nil)
   (defthm contradiction nil
     :hints (("Goal" :use ((:instance (:type-prescription fc) (x '(a))))))
     :rule-classes nil)))
