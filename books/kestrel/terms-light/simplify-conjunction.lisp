; A utility to simplify conjunctions
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "../clause-processors/simple-subsumption") ;todo: move that stuff to this dir

;; Treats TERM as a conjunction, dropping conjuncts that are clearly implied by
;; earlier conjuncts or by terms in TRUE-TERMS.  Treats the conjuncts and the
;; terms in TRUE-TERMS as disjunctions when checking whether one implies another.
;l The preserves iff on TERM.
(defund drop-clearly-implied-conjuncts (term true-terms)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-term-listp true-terms))))
  (if (quotep term)
      term
    (if (clearly-implied-by-some-disjunctionp term true-terms)
        *t*
      ;; (if (clearly-unimplied-by-some-conjunctionp term false-terms)
      ;;     *nil*
      (if (not (term-is-conjunctionp term))
          term
        ;; term is a conjunction (if x y 'nil):
        (let* ((x (farg1 term))
               (y (farg2 term))
               ;; We add x to true-terms, so that later terms weaker than x get
               ;; simplified away:
               (simplified-y (drop-clearly-implied-conjuncts y (cons x true-terms))))
          (if (clearly-implied-by-some-disjunctionp x true-terms)
              (progn$ (cw "Dropping clearly implied conjunct ~X01.~%" x nil)
                      simplified-y)
            `(if ,x ,simplified-y 'nil)))))))

(defthm pseudo-termp-of-drop-clearly-implied-conjuncts
  (implies (pseudo-termp term)
           (pseudo-termp (drop-clearly-implied-conjuncts term true-terms)))
  :hints (("Goal" :in-theory (enable drop-clearly-implied-conjuncts))))

;;move
;; Correctness of drop-clearly-implied-conjuncts.
(defthm if-and-not-eval-of-drop-clearly-implied-conjuncts
  (implies (all-eval-to-true-with-if-and-not-eval true-terms a)
           (iff (if-and-not-eval (drop-clearly-implied-conjuncts term true-terms) a)
                (if-and-not-eval term a)))
  :hints (("Goal" :in-theory (enable drop-clearly-implied-conjuncts))))
