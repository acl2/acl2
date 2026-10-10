; This book, modified only as noted below, and originally named
; new-83-subversive-measure.lisp (but renamed here because "subversive"
; typically refers to a related but different issue), was produced by Claude
; and passed along by Eric Smith.  It illustrates a soundness bug in ACL2
; Version 8.7 fixed before ACL2 Version 8.8.

; Finding 59: subversivep (defuns.lisp:1557) decides whether a defun inside an
; encapsulate is "subversive" from TWO conditions -- (1) a governing test, or
; (2) an actual of a recursive call in a measured position, having a signature
; function as an instantiable ancestor -- and NEVER LOOKS AT THE :MEASURE.
;
; A definition whose measure mentions a signature function cannot be "moved back
; to after the encapsulation" (:DOC subversive-recursions' own soundness story):
; its termination obligation was discharged only of the LOCAL WITNESS.  It is
; nevertheless classified non-subversive, receives no 'constraint-lst-etc, and
; its 'JUSTIFICATION -- hence (:TERMINATION-THEOREM f) -- is exported as a
; theorem.  Functional instantiation of the signature function then gives nil.
;
; Measured:
;   (getpropc 'f 'justification nil (w state))
;     = (JUSTIFICATION (X) (NIL O-P . O<) ((G X) IF MV-LIST RETURN-LAST))
;   (getpropc 'f 'constraint-lst-etc :none (w state))  = :NONE
;   (getpropc 'g 'constraint-lst nil (w state))        = NIL
; The measure is (G X), f has no constraint, and g's constraint list is empty.
;
; THE SMOKING GUN: the identical hazard for GUARD verification is caught by
; bogus-exported-compliants (other-events.lisp:6100), which returns the exported
; functions "whose body or guard has at least one ancestor in sig-fns", with the
; comment "because the guard proof obligations may depend on local properties".
; There is no measure analogue.  Two implementations of one idea, one written.
;
; Note that f's BODY does not mention g at all.  Only its measure does.
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; This must-fail wrapper was added by Matt Kaufmann.
(encapsulate (((g *) => *))
  (local (defun g (x) (acl2-count x)))
  ; Admitted: the local witness makes (g x) = (acl2-count x), which decreases.
  (defun f (x) (declare (xargs :measure (g x))) (if (consp x) (f (cdr x)) x)))
)

; Added by Matt Kaufmann: A version of the encapsulate above that avoids the
; issue.
(encapsulate (((g *) => *))
  (local (defun g (x) (acl2-count x)))
  (local (defun f (x) (declare (xargs :measure (g x))) (if (consp x) (f (cdr x)) x)))
  (defun f (x) (declare (xargs :measure (:? x))) (if (consp x) (f (cdr x)) x)))


; THE DEFECT: (:termination-theorem f) is
;   (and (o-p (g x)) (implies (consp x) (o< (g (cdr x)) (g x))))
; a claim about g that g's (empty) constraint does not imply.  The functional
; instance g := (lambda (x) 0) carries no obligation and gives
; (implies (consp x) nil).
(must-fail
 (defthm nil-proved nil
   :rule-classes nil
   :hints (("Goal" :use ((:instance (:functional-instance
                                      (:termination-theorem f)
                                      (g (lambda (x) 0)))
                                    (x '(1))))))))

; CONTROL 1: the signature function in a governing TEST is caught today --
; subversive-p = T, 'constraint-lst-etc = (G1).  Pins that condition (1) fires.
(encapsulate (((g1 *) => *))
  (local (defun g1 (x) (consp x)))
  (defun f1 (x) (if (g1 x) (if (consp x) (f1 (cdr x)) x) x)))
(assert-event (equal (getpropc 'f1 'constraint-lst-etc :none (w state)) '(G1)))
(must-fail
 (defthm t1-nil nil
   :rule-classes nil
   :hints (("Goal" :use ((:instance (:functional-instance
                                      (:termination-theorem f1)
                                      (g1 (lambda (x) 0)))
                                    (x '(1))))))))

; CONTROL 2: an honest encapsulated recursion with a signature-function-free
; measure must stay admissible AND its termination theorem must stay usable, so
; the fix cannot be "refuse every measure inside an encapsulate".
(encapsulate (((g3 *) => *))
  (local (defun g3 (x) (consp x)))
  (defun f3 (x) (declare (xargs :measure (acl2-count x)))
    (if (consp x) (f3 (cdr x)) (g3 x))))
(defthm honest-tt
  (implies (consp x) (o< (acl2-count (cdr x)) (acl2-count x)))
  :rule-classes nil
  :hints (("Goal" :use (:termination-theorem f3))))
