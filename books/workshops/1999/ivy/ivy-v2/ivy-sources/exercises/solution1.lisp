;; Exercise file to accompany
;;
;; Ivy: A Preprocessor and Proof Checker for First-order Logic
;;
;; William McCune (mccune@mcs.anl.gov)
;; Olga Shumsky (shumsky@ece.nwu.edu)
;;
;; Solution for exercise 1.
;;
;; Define a function to check whether a given variable occurs
;; freely in a formula.  Prove that substitution for a variable
;; that does not occur in the formula has no effect.

(in-package "ACL2")

;; All neccesary definitions are in:
(include-book "../base")

;; Function var-occurrence-term-list (x l) checks if list of
;; terms l contains a variable x

(defun var-occurrence-term-list (x l)
  (declare (xargs :guard (and (variable-term x)
                              (wft-list l))))
  (if (atom l)
      nil
    (or (cond ((variable-term (car l)) (equal (car l) x))
	      ((domain-term (car l)) nil)
	      ((wf-ap-term-top (car l)) (var-occurrence-term-list x (cdar l)))
	      (t nil))  ;; non-term
	(var-occurrence-term-list x (cdr l)))))

;; Function free-occurrence (x f) checks if formula f contains
;; x as a free variable.

(defun free-occurrence (x f)
  (declare (xargs :guard (and (variable-term x) (wff f))))
  (cond ((wfnot f) (free-occurrence x (a1 f)))
        ((wfbinary f) (or (free-occurrence x (a1 f))
                          (free-occurrence x (a2 f))))
        ((wfquant f) (if (equal x (a1 f))
                         nil
                         (free-occurrence x (a2 f))))
        ((wfatomtop f) (var-occurrence-term-list x (cdr f)))
        (t nil)))


;; supporting lemma, domain term is a natural number,
;; and therefore not a cons pair
(defthm domain-term-is-not-cons
  (not (domain-term (cons x y)))
  :hints (("Goal"
           :in-theory (enable domain-term))))

;; substitution in term list preserves occurrences of
;; other variables in term list
(defthm var-occurrence-subst
  (implies (and (var-occurrence-term-list y l)
                (not (equal x y)))
           (var-occurrence-term-list y (subst-term-list l x tm)))
  :hints (("Goal" :do-not generalize)))

;; substitution in formula preserves occurrences of other
;; free variables in formula
(defthm free-subst
  (implies (and (free-occurrence y f)
                (not (equal x y)))
           (free-occurrence y (subst-free f x tm))))
