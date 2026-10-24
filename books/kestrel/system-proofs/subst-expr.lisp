; Correctness of the ACL2 system functions subst-expr and subst-expr1
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; SUBST-EXPR (in rewrite.lisp) replaces occurrences of the term OLD with the
;; term NEW in TERM ("equals for equals").  It does not descend into lambda
;; bodies.  It is used when applying :generalize rules
;; (apply-generalize-rule).

(include-book "clause-processors/sublis-var-meaning" :dir :system) ; for cterm-ev and the correctness of cons-term
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(local (include-book "subst-var")) ; since subst-expr calls subst-var
(local (include-book "cons-term-helpers"))
(local (include-book "helpers"))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "tools/flag" :dir :system))

(local (make-flag subst-expr1))

(defthm-flag-subst-expr1
  (defthm subst-expr1-correct
    (implies (equal (cterm-ev new a) (cterm-ev old a))
             (equal (cterm-ev (subst-expr1 new old term) a)
                    (cterm-ev term a)))
    :flag subst-expr1)
  (defthm subst-expr1-lst-correct
    (implies (equal (cterm-ev new a) (cterm-ev old a))
             (equal (cterm-ev-lst (subst-expr1-lst new old args) a)
                    (cterm-ev-lst args a)))
    :flag subst-expr1-lst)
  :hints (("Goal" :in-theory (enable cterm-ev-of-fncall-args))))

;; Replacing a term with something that has the same value preserves the
;; value of the term.  The (not (quotep old)) hyp comes from the guard.
(defthm subst-expr-correct
  (implies (and (equal (cterm-ev new a) (cterm-ev old a))
                (not (quotep old)))
           (equal (cterm-ev (subst-expr new old term) a)
                  (cterm-ev term a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Properties of terms that SUBST-EXPR preserves.  (That it preserves
;; pseudo-termp is implied by its guard verification.)

(defthm len-of-subst-expr1-lst
  (equal (len (subst-expr1-lst new old args))
         (len args))
  :hints (("Goal" :induct (len args)
           :in-theory (enable subst-expr1-lst))))

(defthm-flag-subst-expr1
  (defthm termp-of-subst-expr1
    (implies (and (termp new w)
                  (termp term w))
             (termp (subst-expr1 new old term) w))
    :flag subst-expr1)
  (defthm term-listp-of-subst-expr1-lst
    (implies (and (termp new w)
                  (term-listp args w))
             (term-listp (subst-expr1-lst new old args) w))
    :flag subst-expr1-lst)
  :hints (("Goal" :expand ((termp term w)))))

(defthm-flag-subst-expr1
  (defthm no-nils-in-termp-of-subst-expr1
    (implies (and (no-nils-in-termp new)
                  (no-nils-in-termp term))
             (no-nils-in-termp (subst-expr1 new old term)))
    :flag subst-expr1)
  (defthm no-nils-in-termsp-of-subst-expr1-lst
    (implies (and (no-nils-in-termp new)
                  (no-nils-in-termsp args))
             (no-nils-in-termsp (subst-expr1-lst new old args)))
    :flag subst-expr1-lst))

(defthm-flag-subst-expr1
  (defthm lambdas-closed-in-termp-of-subst-expr1
    (implies (and (lambdas-closed-in-termp new)
                  (lambdas-closed-in-termp term))
             (lambdas-closed-in-termp (subst-expr1 new old term)))
    :flag subst-expr1)
  (defthm lambdas-closed-in-termsp-of-subst-expr1-lst
    (implies (and (lambdas-closed-in-termp new)
                  (lambdas-closed-in-termsp args))
             (lambdas-closed-in-termsp (subst-expr1-lst new old args)))
    :flag subst-expr1-lst)
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp))))

(defthm-flag-subst-expr1
  (defthm no-duplicate-lambda-formals-in-termp-of-subst-expr1
    (implies (and (no-duplicate-lambda-formals-in-termp new)
                  (no-duplicate-lambda-formals-in-termp term))
             (no-duplicate-lambda-formals-in-termp (subst-expr1 new old term)))
    :flag subst-expr1)
  (defthm no-duplicate-lambda-formals-in-termsp-of-subst-expr1-lst
    (implies (and (no-duplicate-lambda-formals-in-termp new)
                  (no-duplicate-lambda-formals-in-termsp args))
             (no-duplicate-lambda-formals-in-termsp (subst-expr1-lst new old args)))
    :flag subst-expr1-lst)
  :hints (("Goal" :in-theory (enable no-duplicate-lambda-formals-in-termp))))

(defthm termp-of-subst-expr
  (implies (and (not (quotep old)) ; from the guard
                (termp new w)
                (termp term w))
           (termp (subst-expr new old term) w)))

(defthm no-nils-in-termp-of-subst-expr
  (implies (and (not (quotep old)) ; from the guard
                (no-nils-in-termp new)
                (no-nils-in-termp term))
           (no-nils-in-termp (subst-expr new old term))))

(defthm lambdas-closed-in-termp-of-subst-expr
  (implies (and (not (quotep old)) ; from the guard
                (lambdas-closed-in-termp new)
                (lambdas-closed-in-termp term))
           (lambdas-closed-in-termp (subst-expr new old term))))

(defthm no-duplicate-lambda-formals-in-termp-of-subst-expr
  (implies (and (not (quotep old)) ; from the guard
                (no-duplicate-lambda-formals-in-termp new)
                (no-duplicate-lambda-formals-in-termp term))
           (no-duplicate-lambda-formals-in-termp (subst-expr new old term))))

;; The free vars of the result are among those of NEW and TERM.
(defthm-flag-subst-expr1
  (defthm subsetp-equal-of-free-vars-in-term-of-subst-expr1
    (subsetp-equal (free-vars-in-term (subst-expr1 new old term))
                   (union-equal (free-vars-in-term new)
                                (free-vars-in-term term)))
    :flag subst-expr1)
  (defthm subsetp-equal-of-free-vars-in-terms-of-subst-expr1-lst
    (subsetp-equal (free-vars-in-terms (subst-expr1-lst new old args))
                   (union-equal (free-vars-in-term new)
                                (free-vars-in-terms args)))
    :flag subst-expr1-lst)
  :hints (("Goal" :in-theory (enable free-vars-in-term free-vars-in-terms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What SUBST-EXPR is for.  It is used to replace a term with a new variable
;; (see apply-generalize-rule and the checking of :typed-term in
;; type-prescription rules).  When NEW is a variable that does not occur in
;; OLD, OLD no longer occurs in the result (as checked by OCCUR, which, like
;; SUBST-EXPR, does not look inside lambda bodies) -- provided that TERM
;; contains no calls that CONS-TERM would evaluate (see the counterexample in
;; subst-expr-tests.lisp).

;; Checks that no subterm of TERM (outside lambda bodies) is a call that
;; CONS-TERM would evaluate.
(mutual-recursion
 (defun cons-term-normal-p (term)
   (declare (xargs :verify-guards nil))
   (if (or (variablep term)
           (fquotep term))
       t
     (and (cons-term-normal-listp (fargs term))
          (equal (cons-term (ffn-symb term) (fargs term))
                 term))))
 (defun cons-term-normal-listp (terms)
   (declare (xargs :verify-guards nil))
   (if (endp terms)
       t
     (and (cons-term-normal-p (car terms))
          (cons-term-normal-listp (cdr terms))))))

(local (make-flag cons-term-normal-p))

;; Substituting for something that does not occur changes nothing, for a term
;; in normal form.
(defthm-flag-subst-expr1
  (defthm subst-expr1-when-not-occur
    (implies (and (not (occur old term))
                  (not (quotep old))
                  (cons-term-normal-p term)
                  (pseudo-termp term))
             (equal (subst-expr1 new old term)
                    term))
    :flag subst-expr1)
  (defthm subst-expr1-lst-when-not-occur-lst
    (implies (and (not (occur-lst old args))
                  (not (quotep old))
                  (cons-term-normal-listp args)
                  (pseudo-term-listp args))
             (equal (subst-expr1-lst new old args)
                    args))
    :flag subst-expr1-lst))

;; If OLD occurs, the variable NEW occurs in the result.
(defthm-flag-subst-expr1
  (defthm occur-of-subst-expr1
    (implies (and (occur old term)
                  (variablep new)
                  new
                  (not (quotep old)))
             (occur new (subst-expr1 new old term)))
    :flag subst-expr1)
  (defthm occur-lst-of-subst-expr1-lst
    (implies (and (occur-lst old args)
                  (variablep new)
                  new
                  (not (quotep old)))
             (occur-lst new (subst-expr1-lst new old args)))
    :flag subst-expr1-lst)
  :hints (("Goal" :in-theory (enable cons-term cons-term1))))

(local
 (defthm not-quote-listp-when-occur-lst
   (implies (and (occur-lst new args)
                 (not (quotep new)))
            (not (quote-listp args)))
   :hints (("Goal" :in-theory (enable quote-listp)))))

(local
 (defthm cons-term-when-not-quote-listp
   (implies (not (quote-listp args))
            (equal (cons-term fn args)
                   (cons fn args)))
   :hints (("Goal" :in-theory (enable cons-term)))))

;; The step for a function call.
(local
 (defthm not-occur-of-cons-term-of-subst-expr1-lst
   (implies (and (not (occur-lst old (subst-expr1-lst new old (cdr term))))
                 (consp term)
                 (not (equal 'quote (car term)))
                 (not (equal term old))
                 (variablep new)
                 new
                 (not (occur new old))
                 (not (quotep old))
                 (cons-term-normal-listp (cdr term))
                 (equal (cons-term (car term) (cdr term)) term)
                 (pseudo-termp term))
            (not (occur old (cons-term (car term) (subst-expr1-lst new old (cdr term))))))
   :hints (("Goal" :cases ((occur-lst old (cdr term)))
            :use ((:instance occur-lst-of-subst-expr1-lst (args (cdr term)))
                  (:instance not-quote-listp-when-occur-lst
                             (args (subst-expr1-lst new old (cdr term))))
                  (:instance cons-term-when-not-quote-listp
                             (fn (car term))
                             (args (subst-expr1-lst new old (cdr term)))))
            :expand ((occur new old)
                     (pseudo-termp term)
                     (occur old (cons (car term) (subst-expr1-lst new old (cdr term)))))
            :in-theory (disable cons-term occur-lst-of-subst-expr1-lst
                                not-quote-listp-when-occur-lst
                                cons-term-when-not-quote-listp)))))

(defthm-flag-subst-expr1
  (defthm not-occur-of-subst-expr1
    (implies (and (variablep new)
                  new
                  (not (occur new old))
                  (not (quotep old))
                  (cons-term-normal-p term)
                  (pseudo-termp term))
             (not (occur old (subst-expr1 new old term))))
    :flag subst-expr1)
  (defthm not-occur-lst-of-subst-expr1-lst
    (implies (and (variablep new)
                  new
                  (not (occur new old))
                  (not (quotep old))
                  (cons-term-normal-listp args)
                  (pseudo-term-listp args))
             (not (occur-lst old (subst-expr1-lst new old args))))
    :flag subst-expr1-lst))

;; Without the normal-form hypothesis, OLD can remain, though this seldom
;; matters in practice: see subst-expr1-can-leave-old in subst-expr-tests.lisp.
