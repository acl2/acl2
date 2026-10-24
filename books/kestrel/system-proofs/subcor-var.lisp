; Correctness of the ACL2 system function subcor-var
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; SUBCOR-VAR (in basis-b.lisp) substitutes the TERMS for the corresponding
;; VARS in FORM.  It is the workhorse for beta-reduction in the prover.  It
;; does not descend into lambda bodies, and it rebuilds terms using CONS-TERM.

;; See also subcor-var-is-sublis-var1 in sublis-var-meaning.lisp, which, together
;; with eval-of-sublis-var there, gives a similar result but requires that NIL
;; not be among the VARS.  Here, we instead require that NIL not be a free
;; variable of FORM (true for all proper terms).

(include-book "clause-processors/sublis-var-meaning" :dir :system) ; for cterm-ev and the correctness of cons-term
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "cons-term-helpers") ; properties of terms preserved by cons-term
(local (include-book "cterm-ev-helpers"))
(local (include-book "helpers"))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "tools/flag" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))

;; We reason about subcor-var directly, rather than in terms of sublis-var1.
(local (in-theory (disable subcor-var-is-sublis-var1 subcor-var-lst-is-sublis-var1-lst)))

(local (make-flag subcor-var))

;; Evaluating the result of SUBCOR-VAR is like evaluating FORM in an alist
;; that binds the VARS to the values of the TERMS.
(defthm-flag-subcor-var
  (defthm subcor-var-correct
    (implies (and (not (member-equal nil (free-vars-in-term form))) ; the "variable" NIL always evaluates to NIL
                  (pseudo-termp form))
             (equal (cterm-ev (subcor-var vars terms form) a)
                    (cterm-ev form (append (pairlis$ vars (cterm-ev-lst terms a)) a))))
    :flag subcor-var)
  (defthm subcor-var-lst-correct
    (implies (and (not (member-equal nil (free-vars-in-terms forms)))
                  (pseudo-term-listp forms))
             (equal (cterm-ev-lst (subcor-var-lst vars terms forms) a)
                    (cterm-ev-lst forms (append (pairlis$ vars (cterm-ev-lst terms a)) a))))
    :flag subcor-var-lst)
  :hints (("Goal" :in-theory (enable cterm-ev-of-fncall-args free-vars-in-term free-vars-in-terms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm-flag-subcor-var
  (defthm no-nils-in-termp-of-subcor-var
    (implies (and (no-nils-in-termp form)
                  (no-nils-in-termsp terms)
                  (equal (len vars) (len terms)))
             (no-nils-in-termp (subcor-var vars terms form)))
    :flag subcor-var)
  (defthm no-nils-in-termsp-of-subcor-var-lst
    (implies (and (no-nils-in-termsp forms)
                  (no-nils-in-termsp terms)
                  (equal (len vars) (len terms)))
             (no-nils-in-termsp (subcor-var-lst vars terms forms)))
    :flag subcor-var-lst))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; More properties of terms that SUBCOR-VAR preserves.  (That it preserves
;; pseudo-termp is proved in books/system/subcor-var.lisp.)

;; We use the lemmas about subcor-var1 in helpers.lisp.
(local (in-theory (disable subcor-var1-in-terms-of-cdr-assoc)))

(defthm len-of-subcor-var-lst
  (equal (len (subcor-var-lst vars terms forms))
         (len forms))
  :hints (("Goal" :induct (len forms)
           :in-theory (enable subcor-var-lst))))

(defthm-flag-subcor-var
  (defthm termp-of-subcor-var
    (implies (and (termp form w)
                  (term-listp terms w)
                  (equal (len vars) (len terms)))
             (termp (subcor-var vars terms form) w))
    :flag subcor-var)
  (defthm term-listp-of-subcor-var-lst
    (implies (and (term-listp forms w)
                  (term-listp terms w)
                  (equal (len vars) (len terms)))
             (term-listp (subcor-var-lst vars terms forms) w))
    :flag subcor-var-lst)
  :hints (("Goal" :expand ((termp form w)))))

(defthm-flag-subcor-var
  (defthm lambdas-closed-in-termp-of-subcor-var
    (implies (and (lambdas-closed-in-termp form)
                  (lambdas-closed-in-termsp terms))
             (lambdas-closed-in-termp (subcor-var vars terms form)))
    :flag subcor-var)
  (defthm lambdas-closed-in-termsp-of-subcor-var-lst
    (implies (and (lambdas-closed-in-termsp forms)
                  (lambdas-closed-in-termsp terms))
             (lambdas-closed-in-termsp (subcor-var-lst vars terms forms)))
    :flag subcor-var-lst)
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp))))

(defthm-flag-subcor-var
  (defthm no-duplicate-lambda-formals-in-termp-of-subcor-var
    (implies (and (no-duplicate-lambda-formals-in-termp form)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termp (subcor-var vars terms form)))
    :flag subcor-var)
  (defthm no-duplicate-lambda-formals-in-termsp-of-subcor-var-lst
    (implies (and (no-duplicate-lambda-formals-in-termsp forms)
                  (no-duplicate-lambda-formals-in-termsp terms))
             (no-duplicate-lambda-formals-in-termsp (subcor-var-lst vars terms forms)))
    :flag subcor-var-lst)
  :hints (("Goal" :in-theory (enable no-duplicate-lambda-formals-in-termp))))

(defthm-flag-subcor-var
  (defthm lambda-free-termp-of-subcor-var
    (implies (and (lambda-free-termp form)
                  (lambda-free-termsp terms))
             (lambda-free-termp (subcor-var vars terms form)))
    :flag subcor-var)
  (defthm lambda-free-termsp-of-subcor-var-lst
    (implies (and (lambda-free-termsp forms)
                  (lambda-free-termsp terms))
             (lambda-free-termsp (subcor-var-lst vars terms forms)))
    :flag subcor-var-lst)
  :hints (("Goal" :in-theory (enable lambda-free-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What SUBCOR-VAR is for: the free vars of the result are those of the TERMS
;; plus those of FORM other than the VARS (at most).

(defthm-flag-subcor-var
  (defthm subsetp-equal-of-free-vars-in-term-of-subcor-var
    (implies (equal (len vars) (len terms))
             (subsetp-equal (free-vars-in-term (subcor-var vars terms form))
                            (union-equal (free-vars-in-terms terms)
                                         (set-difference-equal (free-vars-in-term form) vars))))
    :flag subcor-var)
  (defthm subsetp-equal-of-free-vars-in-terms-of-subcor-var-lst
    (implies (equal (len vars) (len terms))
             (subsetp-equal (free-vars-in-terms (subcor-var-lst vars terms forms))
                            (union-equal (free-vars-in-terms terms)
                                         (set-difference-equal (free-vars-in-terms forms) vars))))
    :flag subcor-var-lst)
  :hints (("Goal" :in-theory (enable free-vars-in-term free-vars-in-terms))))
