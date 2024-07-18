; A tools to simplify terms in generic ways not involving full rewriting
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; TODO: Add more kinds of simplifications (e.g., subst lambda vars bound to vars, replace hard-error/cw with nil, replace eql with equal, trivial lambdas, resolve ifs)

;; See correctness proof in pre-simplify-term-proofs.lisp.

(include-book "substitute-constants-in-lambdas2")
(include-book "drop-unused-lambda-bindings")
(include-book "drop-trivial-lambdas")
(include-book "substitute-unnecessary-lambda-vars2")
(include-book "simplify-ors")
(local (include-book "substitute-constants-in-lambdas2-proofs"))

;; todo: think about the order of these steps (but note that we repeat the whole sequence)
(defund pre-simplify-term-one-step (term)
  (declare (xargs :guard (pseudo-termp term)))
  (let* ((term (substitute-constants-in-lambdas2 term))
         (term (drop-unused-lambda-bindings term))
         (term (substitute-unnecessary-lambda-vars-in-term2 term nil nil))
         ;; todo: this is not really about lambdas.  rename this book?
         (term (simplify-ors term nil)) ; could pass in bool-fix, as for a hyp
         (term (drop-trivial-lambdas term))
         )
    term))

(defthm pseudo-termp-of-pre-simplify-term-one-step
  (implies (pseudo-termp term)
           (pseudo-termp (pre-simplify-term-one-step term)))
  :hints (("Goal" :in-theory (enable pre-simplify-term-one-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; count ensures termination
;; todo: thread through a print argument
(defund pre-simplify-term-loop (count term)
  (declare (xargs :guard (and (natp count)
                              (pseudo-termp term))))
  (if (zp count)
      (prog2$ (cw "WARNING: Ran out of steps when simplifying lambdas.~%")
              term)
    (let ((new-term (pre-simplify-term-one-step term)))
      (if (equal term new-term)
          term
        (progn$
         ;;(cw "Simplified lambdas.~%")
         (pre-simplify-term-loop (+ -1 count) new-term))))))

(defthm pseudo-termp-of-pre-simplify-term-loop
  (implies (pseudo-termp term)
           (pseudo-termp (pre-simplify-term-loop count term)))
  :hints (("Goal" :in-theory (enable pre-simplify-term-loop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund pre-simplify-term (term print)
  (declare (xargs :guard (and (pseudo-termp term)
                              (booleanp print))))
  (let ((new-term (pre-simplify-term-loop 10000 term)))
    (progn$
     (and print (not (equal term new-term)) (cw "Simplified:~%~X01~%to:~%~X23.~%" term nil new-term nil))
     new-term)))

(defthm pseudo-termp-of-pre-simplify-term
  (implies (pseudo-termp term)
           (pseudo-termp (pre-simplify-term term print)))
  :hints (("Goal" :in-theory (enable pre-simplify-term))))
