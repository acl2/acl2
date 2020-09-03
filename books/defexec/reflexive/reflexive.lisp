; This example illustrates the admission of a reflexive function by adding an
; extra test for termination, but then eliminating that test for execution
; using mbe.

(in-package "ACL2")

; Get the MUST-FAIL macro so that we can check that the original weird-identity
; is not admissible.
(include-book "std/testing/must-fail" :dir :system)

(must-fail
 (defun weird-identity (x)
   (if (and (integerp x) (< 0 x))
       (+ 1 (weird-identity (weird-identity (- x 1))))
     0)))

(defun weird-identity-logic (x)
  (if (and (integerp x) (< 0 x))
      (let ((rec-call (weird-identity-logic (- x 1))))
        (if (and (integerp rec-call)
                 (<= 0 rec-call)
                 (< rec-call x))
            (+ 1 (weird-identity-logic rec-call))
          'do-not-care))
    0))

(defthm weird-identity-lemma
  (implies (and (integerp x) (<= 0 x))
           (equal (weird-identity-logic x)
                  x)))

(defun weird-identity (x)
  (declare (xargs :guard (and (integerp x) (<= 0 x))))
  (mbe :logic
       (weird-identity-logic x)
       :exec
       (if (and (integerp x) (< 0 x))
           (+ 1 (weird-identity (weird-identity (- x 1))))
         0)))
