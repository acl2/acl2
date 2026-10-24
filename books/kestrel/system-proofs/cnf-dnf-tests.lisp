; Tests and examples for cnf-dnf.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Counterexamples and examples for the theorems in cnf-dnf.lisp.  This book
;; is not included by top.lisp.

(include-book "cnf-dnf")

;; CNF-DNF is wrong when TERM is a call of NOT: it calls itself on the argument
;; of the NOT with CNFP negated, so the result for the argument is read in the
;; wrong normal form.  Here the DNF it returns for (not (or a b)) means
;; (or (not a) (not b)), which is true when A is true and B is false:

(defthm cnf-dnf-incorrect-for-not
  (let ((sign t)
        (term '(not (if a a b))) ; (not (or a b))
        (cnfp nil)
        (alist '((a . t) (b . nil))))
    (and (equal (cnf-dnf sign term cnfp)
                '(((not a)) ((not b))))
         (cnf-dnf-eval-dnf (cnf-dnf sign term cnfp) alist)
         (not (cnf-dnf-eval term alist))))
  :hints (("Goal" :in-theory (e/d (cnf-dnf-eval-dnf
                                   cnf-dnf-eval-conjunction)
                                  ((:e cnf-dnf-eval-dnf)
                                   (:e cnf-dnf-eval-conjunction)))))
  :rule-classes nil)

;; As a result, split-on-conjoined-disjunctions turns the hypothesis
;; (not (or a b)) into two alternative hypotheses, (not a) and (not b), each
;; weaker than the original, so a tau rule made from them is stronger than
;; the theorem it comes from:
(defthm split-on-conjoined-disjunctions-incorrect-for-not
  (equal (split-on-conjoined-disjunctions '((not (if a a b))))
         '(((not a)) ((not b))))
  :rule-classes nil)
