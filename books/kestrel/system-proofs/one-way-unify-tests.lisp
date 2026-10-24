; Tests and examples for one-way-unify.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Counterexamples and examples for the theorems in one-way-unify.lisp.  This
;; book is not included by top.lisp.

(include-book "one-way-unify")

;; Counterexamples showing that pseudo-termp is not enough:

;; A pattern variable named T is treated as "no further requirements":
(defthm one-way-unify-incorrect-with-variable-t
  (let ((pat '(binary-+ '1 t))
        (term ''7))
    (and (pseudo-termp pat)
         (pseudo-termp term)
         (equal (mv-nth 0 (one-way-unify pat term)) t)
         (equal (mv-nth 1 (one-way-unify pat term)) nil)
         (not (equal (one-way-unify-eval pat (one-way-unify-eval-alist (mv-nth 1 (one-way-unify pat term)) a))
                     (one-way-unify-eval term a)))))
  :rule-classes nil)

;; The "variable" NIL always evaluates to NIL, whatever it is bound to:
(defthm one-way-unify-incorrect-with-variable-nil
  (let ((pat 'nil)
        (term ''5))
    (and (pseudo-termp pat)
         (pseudo-termp term)
         (equal (mv-nth 0 (one-way-unify pat term)) t)
         (not (equal (one-way-unify-eval pat (one-way-unify-eval-alist (mv-nth 1 (one-way-unify pat term)) a))
                     (one-way-unify-eval term a)))))
  :rule-classes nil)

;; A call of CONS with one argument matches a cons constant by its car alone:
(defthm one-way-unify-incorrect-with-wrong-arity-for-cons
  (let ((pat '(cons x))
        (term ''(1 . 2)))
    (and (pseudo-termp pat)
         (pseudo-termp term)
         (equal (mv-nth 0 (one-way-unify pat term)) t)
         (not (equal (one-way-unify-eval pat (one-way-unify-eval-alist (mv-nth 1 (one-way-unify pat term)) a))
                     (one-way-unify-eval term a)))))
  :rule-classes nil)

;; One-way-unify1-lst is not a "No-Change Loser": it can fail after extending
;; the alist.
(defthm one-way-unify1-lst-not-a-no-change-loser
  (let ((pl '(x 'c))
        (tl '(a b)))
    (and (not (mv-nth 0 (one-way-unify1-lst pl tl nil)))
         (equal (mv-nth 1 (one-way-unify1-lst pl tl nil))
                '((x . a)))))
  :rule-classes nil)
