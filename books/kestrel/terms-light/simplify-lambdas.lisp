; A tools to simplify lambdas in terms
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; TODO: Add more kinds of simplifications

(include-book "substitute-constants-in-lambdas")
(include-book "clean-up-lambdas")
;; (include-book "substitute-unnecessary-lambda-vars")

(defund simplify-lambdas-one-step (term)
  (declare (xargs :guard (pseudo-termp term)))
  (let* ((term (substitute-constants-in-lambdas term))
         (term (drop-unused-lambda-bindings term))
         ;; (term (substitute-unnecessary-lambda-vars-in-term term nil)) ; todo: put back
         )
    term))

(defthm pseudo-termp-of-simplify-lambdas-one-step
  (implies (pseudo-termp term)
           (pseudo-termp (simplify-lambdas-one-step term)))
  :hints (("Goal" :in-theory (enable simplify-lambdas-one-step))))

;; count ensures termination
;; todo: thread through a print argument
(defund simplify-lambdas-loop (count term)
  (declare (xargs :guard (and (natp count)
                              (pseudo-termp term))))
  (if (zp count)
      (prog2$ (cw "WARNING: Ran out of steps when simplifying lambdas.~%")
              term)
    (let ((new-term (simplify-lambdas-one-step term)))
      (if (equal term new-term)
          term
        (progn$
         ;;(cw "Simplified lambdas.~%")
         (simplify-lambdas-loop (+ -1 count) new-term))))))

(defthm pseudo-termp-of-simplify-lambdas-loop
  (implies (pseudo-termp term)
           (pseudo-termp (simplify-lambdas-loop count term)))
  :hints (("Goal" :in-theory (enable simplify-lambdas-loop))))

(defund simplify-lambdas (term print)
  (declare (xargs :guard (and (pseudo-termp term)
                              (booleanp print))))
  (let ((new-term (simplify-lambdas-loop 10000 term)))
    (progn$
     (and print (not (equal term new-term)) (cw "Simplified:~%~X01~%to:~%~X23.~%" term nil new-term nil))
     new-term)))

(defthm pseudo-termp-of-simplify-lambdas
  (implies (pseudo-termp term)
           (pseudo-termp (simplify-lambdas term print)))
  :hints (("Goal" :in-theory (enable simplify-lambdas))))
