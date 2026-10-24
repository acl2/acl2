; Correctness of the ACL2 system function fsubcor-var
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; FSUBCOR-VAR (in other-events.lisp) is like SUBCOR-VAR (see subcor-var.lisp)
;; but rebuilds terms using FCONS-TERM instead of CONS-TERM, so as to preserve
;; the structure of the term.  It is used when printing guard violations (see
;; print-gv-form).

;; Since it does not use CONS-TERM, we state its correctness using EMPTY-EVAL,
;; which knows no functions; thus the result holds for every evaluator.

(include-book "kestrel/evaluators/empty-eval" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "tools/flag" :dir :system))
(local (include-book "helpers"))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))

(local (make-flag fsubcor-var))

(local
 (defthm subcor-var1-becomes-assoc-equal-of-pairlis$
   (equal (subcor-var1 vars terms var)
          (let ((pair (assoc-equal var (pairlis$ vars terms))))
            (if pair (cdr pair) var)))
   :hints (("Goal" :in-theory (enable subcor-var1 pairlis$ assoc-equal)))))

(local
 (defthm empty-eval-of-cdr-of-assoc-equal-of-pairlis$
   (equal (empty-eval (cdr (assoc-equal key (pairlis$ vars terms))) a)
          (cdr (assoc-equal key (pairlis$ vars (empty-eval-list terms a)))))
   :hints (("Goal" :in-theory (enable pairlis$ assoc-equal)))))

;; Evaluating the result of FSUBCOR-VAR is like evaluating FORM in an alist
;; that binds the VARS to the values of the TERMS.
(defthm-flag-fsubcor-var
  (defthm fsubcor-var-correct
    (implies (and (not (member-equal nil (free-vars-in-term form))) ; the "variable" NIL always evaluates to NIL
                  (pseudo-termp form))
             (equal (empty-eval (fsubcor-var vars terms form) a)
                    (empty-eval form (append (pairlis$ vars (empty-eval-list terms a)) a))))
    :flag fsubcor-var)
  (defthm fsubcor-var-lst-correct
    (implies (and (not (member-equal nil (free-vars-in-terms forms)))
                  (pseudo-term-listp forms))
             (equal (empty-eval-list (fsubcor-var-lst vars terms forms) a)
                    (empty-eval-list forms (append (pairlis$ vars (empty-eval-list terms a)) a))))
    :flag fsubcor-var-lst)
  :hints (("Goal" :in-theory (e/d (empty-eval-of-fncall-args free-vars-in-term free-vars-in-terms)
                                  (empty-eval-of-fncall-args-back)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Properties of terms that FSUBCOR-VAR preserves.  (That it preserves
;; pseudo-termp is implied by its guard verification; see
;; books/system/kestrel.lisp.)

;; We use the lemmas about subcor-var1 in helpers.lisp.
(local (in-theory (disable subcor-var1-becomes-assoc-equal-of-pairlis$)))

(defthm len-of-fsubcor-var-lst
  (equal (len (fsubcor-var-lst vars terms forms))
         (len forms))
  :hints (("Goal" :induct (len forms)
           :in-theory (enable fsubcor-var-lst))))

(defthm-flag-fsubcor-var
  (defthm termp-of-fsubcor-var
    (implies (and (termp form w)
                  (term-listp terms w)
                  (equal (len vars) (len terms)))
             (termp (fsubcor-var vars terms form) w))
    :flag fsubcor-var)
  (defthm term-listp-of-fsubcor-var-lst
    (implies (and (term-listp forms w)
                  (term-listp terms w)
                  (equal (len vars) (len terms)))
             (term-listp (fsubcor-var-lst vars terms forms) w))
    :flag fsubcor-var-lst)
  :hints (("Goal" :expand ((termp form w)))))

(defthm-flag-fsubcor-var
  (defthm no-nils-in-termp-of-fsubcor-var
    (implies (and (no-nils-in-termp form)
                  (no-nils-in-termsp terms)
                  (equal (len vars) (len terms)))
             (no-nils-in-termp (fsubcor-var vars terms form)))
    :flag fsubcor-var)
  (defthm no-nils-in-termsp-of-fsubcor-var-lst
    (implies (and (no-nils-in-termsp forms)
                  (no-nils-in-termsp terms)
                  (equal (len vars) (len terms)))
             (no-nils-in-termsp (fsubcor-var-lst vars terms forms)))
    :flag fsubcor-var-lst))

(defthm-flag-fsubcor-var
  (defthm lambdas-closed-in-termp-of-fsubcor-var
    (implies (and (lambdas-closed-in-termp form)
                  (lambdas-closed-in-termsp terms))
             (lambdas-closed-in-termp (fsubcor-var vars terms form)))
    :flag fsubcor-var)
  (defthm lambdas-closed-in-termsp-of-fsubcor-var-lst
    (implies (and (lambdas-closed-in-termsp forms)
                  (lambdas-closed-in-termsp terms))
             (lambdas-closed-in-termsp (fsubcor-var-lst vars terms forms)))
    :flag fsubcor-var-lst)
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp))))

(defthm-flag-fsubcor-var
  (defthm no-duplicate-lambda-formals-in-termp-of-fsubcor-var
    (implies (and (no-duplicate-lambda-formals-in-termp form)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termp (fsubcor-var vars terms form)))
    :flag fsubcor-var)
  (defthm no-duplicate-lambda-formals-in-termsp-of-fsubcor-var-lst
    (implies (and (no-duplicate-lambda-formals-in-termsp forms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termsp (fsubcor-var-lst vars terms forms)))
    :flag fsubcor-var-lst)
  :hints (("Goal" :in-theory (enable no-duplicate-lambda-formals-in-termp))))

;; What FSUBCOR-VAR is for: the free vars of the result are those of the TERMS
;; plus those of FORM other than the VARS (at most).
(defthm-flag-fsubcor-var
  (defthm subsetp-equal-of-free-vars-in-term-of-fsubcor-var
    (implies (equal (len vars) (len terms))
             (subsetp-equal (free-vars-in-term (fsubcor-var vars terms form))
                            (union-equal (free-vars-in-terms terms)
                                         (set-difference-equal (free-vars-in-term form) vars))))
    :flag fsubcor-var)
  (defthm subsetp-equal-of-free-vars-in-terms-of-fsubcor-var-lst
    (implies (equal (len vars) (len terms))
             (subsetp-equal (free-vars-in-terms (fsubcor-var-lst vars terms forms))
                            (union-equal (free-vars-in-terms terms)
                                         (set-difference-equal (free-vars-in-terms forms) vars))))
    :flag fsubcor-var-lst)
  :hints (("Goal" :in-theory (enable free-vars-in-term free-vars-in-terms))))
