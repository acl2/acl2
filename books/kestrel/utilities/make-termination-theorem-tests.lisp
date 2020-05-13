; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; See :DOC make-termination-theorem for an introduction to that utility.  Here
; we provide some tests, which also serve as further documentation.

(include-book "make-termination-theorem")
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

; Introduce "aliases" for car and cdr, which we will disable in order to
; demonstrate the value of substituting, using stubs, for recursive functions
; in their own termination theorems.

(defun my-car (x)
  (car x))
(defun my-cdr (x)
  (cdr x))

; The termination-theorem for the following mutual-recursion mentions f1 and
; f2, because each call of AND expands to an IF term with f1 or f2 called in
; the test of the IF.

(mutual-recursion
 (defun f1 (x)
   (if (consp x) (and (f1 (my-car x)) (f2 (my-cdr x))) x))
 (defun f2 (x)
   (if (consp x) (and (f2 (my-car x)) (f1 (my-cdr x))) x)))

; Let's take a look at the (untranslated) termination-theorem for f1/f2.

(assert!
 (equal (untranslate (termination-theorem 'f1 (w state)) t (w state))
        '(AND (OR (NOT (CONSP X))
                  (NOT (F1 (MY-CAR X)))
                  (O< (ACL2-COUNT (MY-CDR X))
                      (ACL2-COUNT X)))
              (O-P (ACL2-COUNT X))
              (OR (NOT (CONSP X))
                  (O< (ACL2-COUNT (MY-CAR X))
                      (ACL2-COUNT X)))
              (OR (NOT (CONSP X))
                  (NOT (F2 (MY-CAR X)))
                  (O< (ACL2-COUNT (MY-CDR X))
                      (ACL2-COUNT X))))))

; By disabling my-car and my-cdr we defeat ACL2's ability to reason about
; termination for schemes like the one above, so that the termination-theorem
; for f1/f2 needs to be suitably applied in such reasoning.

(in-theory (disable my-car my-cdr))

; We make a defthm event representing the termination theorem for f1/f2.  But
; note that f1 and f2 have been replaced by f1$stub and f2$stub, respectively.

(make-termination-theorem f1)

(must-be-redundant
 (DEFTHM
   F1$TTHM
   (AND (OR (NOT (CONSP X))
            (NOT (F1$STUB (MY-CAR X)))
            (O< (ACL2-COUNT (MY-CDR X))
                (ACL2-COUNT X)))
        (O-P (ACL2-COUNT X))
        (OR (NOT (CONSP X))
            (O< (ACL2-COUNT (MY-CAR X))
                (ACL2-COUNT X)))
        (OR (NOT (CONSP X))
            (NOT (F2$STUB (MY-CAR X)))
            (O< (ACL2-COUNT (MY-CDR X))
                (ACL2-COUNT X))))
   :HINTS (("Goal" :USE (:TERMINATION-THEOREM F1 ((F1 F1$STUB) (F2 F2$STUB)))
                   :IN-THEORY (THEORY 'MINIMAL-THEORY)))
   :RULE-CLASSES NIL)
)

; Here we see that f1$stub and f2$stub indeed have no constraints.

(assert!
 (flet ((defstub-p (fn wrld)
          (mv-let (flg constraint-lst)
            (constraint-info fn wrld)
            (and flg (null constraint-lst)))))
   (let ((wrld (w state)))
     (and (defstub-p 'f1$stub wrld)
          (defstub-p 'f2$stub wrld)))))

; Now we define functions g1 and g2 in complete analogy to f1 and f2.  Note
; that the termination proof fails.  (It would succeed with suitable use of a
; :termination-theorem lemma-instance, but below we illustrate a more direct
; use of functional instantiation using the make-termination-theorem tool.)

(must-fail
 (mutual-recursion
  (defun g1 (x)
    (if (consp x) (and (g1 (my-car x)) (g2 (my-cdr x))) x))
  (defun g2 (x)
    (if (consp x) (and (g2 (my-car x)) (g1 (my-cdr x))) x))))

; But by functionally instantiating the theorem introduced above by
; make-termination-theorem, we admit the mutual-recursion.

(mutual-recursion
 (defun g1 (x)
   (declare (xargs :hints
                   (("Goal" :use ((:functional-instance f1$tthm
                                                        (f1$stub g1)
                                                        (f2$stub g2)))))))
   (if (consp x) (and (g1 (my-car x)) (g2 (my-cdr x))) x))
 (defun g2 (x)
   (if (consp x) (and (g2 (my-car x)) (g1 (my-cdr x))) x)))

; Let's illustrate keyword arguments for make-termination-theorem.

(make-termination-theorem
 f1
 :subst ((f1 f1-new) (f2 characterp))
 :thm-name f1-term
 :rule-classes :built-in-clause ; just for kicks
 )

(must-be-redundant

; Here we paste in what was printed by the make-termination-theorem call just
; above.  If you compare the body with what is printed by :tthm f1, or with
; what is in the first assert! form above, you'll see that they are identical
; except that f1 and f2 have been replaced below by f1-new and characterp,
; respectively.

(DEFTHM
     F1-TERM
     (AND (OR (NOT (CONSP X))
              (NOT (F1-NEW (MY-CAR X)))
              (O< (ACL2-COUNT (MY-CDR X))
                  (ACL2-COUNT X)))
          (O-P (ACL2-COUNT X))
          (OR (NOT (CONSP X))
              (O< (ACL2-COUNT (MY-CAR X))
                  (ACL2-COUNT X)))
          (OR (NOT (CONSP X))
              (NOT (CHARACTERP (MY-CAR X)))
              (O< (ACL2-COUNT (MY-CDR X))
                  (ACL2-COUNT X))))
     :HINTS (("Goal" :USE (:TERMINATION-THEOREM F1 ((F1 F1-NEW) (F2 CHARACTERP)))
                     :IN-THEORY (THEORY 'MINIMAL-THEORY)))
     :RULE-CLASSES :BUILT-IN-CLAUSE)
)
