; A tool to simplify terms in generic ways not involving full rewriting
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; TODO: Add more kinds of simplifications (e.g., subst lambda vars bound to
;; other vars, replace hard-error/cw with nil, replace eql with equal, resolve
;; ifs).

;; See correctness proof in pre-simplify-term-proofs.lisp.

(include-book "substitute-constants-in-lambdas")
(include-book "drop-unused-lambda-bindings")
(include-book "drop-trivial-lambdas")
(include-book "substitute-unnecessary-lambda-vars2")
(include-book "simplify-ors")
(local (include-book "substitute-constants-in-lambdas-proofs"))

;; todo: think about the order of these steps (but note that we repeat the whole sequence)
;; IFFP indicates whether we can preserve just IFF rather than EQUAL
(defund pre-simplify-term-one-step (term iffp)
  (declare (xargs :guard (and (pseudo-termp term)
                              (booleanp iffp))))
  (let* ((term (substitute-constants-in-lambdas term))
         (term (drop-unused-lambda-bindings term))
         (term (substitute-unnecessary-lambda-vars-in-term2 term nil nil))
         (term (simplify-ors term iffp))
         (term (drop-trivial-lambdas term)))
    term))

(defthm pseudo-termp-of-pre-simplify-term-one-step
  (implies (pseudo-termp term)
           (pseudo-termp (pre-simplify-term-one-step term iffp)))
  :hints (("Goal" :in-theory (enable pre-simplify-term-one-step))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; count ensures termination
;; todo: thread through a print argument
;; IFFP indicates whether we can preserve just IFF rather than EQUAL
(defund pre-simplify-term-loop (count term iffp)
  (declare (xargs :guard (and (natp count)
                              (pseudo-termp term)
                              (booleanp iffp))))
  (if (zp count)
      (prog2$ (cw "WARNING: Ran out of steps when simplifying lambdas.~%")
              term)
    (let ((new-term (pre-simplify-term-one-step term iffp)))
      (if (equal term new-term)
          term
        (progn$
         ;;(cw "Simplified lambdas.~%")
         (pre-simplify-term-loop (+ -1 count) new-term iffp))))))

(defthm pseudo-termp-of-pre-simplify-term-loop
  (implies (pseudo-termp term)
           (pseudo-termp (pre-simplify-term-loop count term iffp)))
  :hints (("Goal" :in-theory (enable pre-simplify-term-loop))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; IFFP indicates whether we can preserve just IFF rather than EQUAL
(defund pre-simplify-term (term iffp print)
  (declare (xargs :guard (and (pseudo-termp term)
                              (booleanp iffp)
                              (booleanp print))))
  (let ((new-term (pre-simplify-term-loop 10000 term iffp)))
    (progn$
     (and print (not (equal term new-term)) (cw "Simplified:~%~X01~%to:~%~X23.~%" term nil new-term nil))
     new-term)))

(defthm pseudo-termp-of-pre-simplify-term
  (implies (pseudo-termp term)
           (pseudo-termp (pre-simplify-term term iffp print)))
  :hints (("Goal" :in-theory (enable pre-simplify-term))))
