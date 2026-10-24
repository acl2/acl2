; Correctness of the ACL2 system function expand-all-lambdas
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; EXPAND-ALL-LAMBDAS (in translate.lisp) beta-reduces every lambda
;; application in a term, using SUBCOR-VAR.  It is used when cleaning up
;; lambda objects (clean-up-dirty-lambda-object-body, part of
;; remove-guard-holders) and by badger.  The comment after its definition in
;; translate.lisp gives an informal proof that its result is provably equal
;; to its input; here we prove that formally, in terms of an evaluator.

;; As with remove-lambdas (see remove-lambdas.lisp), correctness requires
;; closed lambdas and no NIL variables, which every TERMP has but which the
;; guard (PSEUDO-TERMP) does not imply (see the counterexamples in
;; expand-all-lambdas-tests.lisp).

(include-book "clause-processors/sublis-var-meaning" :dir :system) ; for cterm-ev
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(include-book "kestrel/terms-light/lambda-free-termp" :dir :system)
(local (include-book "subcor-var"))
(local (include-book "cterm-ev-helpers"))
(local (include-book "helpers"))
(local (include-book "system/subcor-var" :dir :system)) ; for pseudo-termp of subcor-var
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "tools/flag" :dir :system))

;; We reason about subcor-var directly, rather than in terms of sublis-var1.
(local (in-theory (disable subcor-var-is-sublis-var1 subcor-var-lst-is-sublis-var1-lst)))

(local (make-flag expand-all-lambdas))

(defthm len-of-expand-all-lambdas-lst
  (equal (len (expand-all-lambdas-lst terms))
         (len terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable expand-all-lambdas-lst))))

(defthm-flag-expand-all-lambdas
  (defthm pseudo-termp-of-expand-all-lambdas
    (implies (pseudo-termp term)
             (pseudo-termp (expand-all-lambdas term)))
    :flag expand-all-lambdas)
  (defthm pseudo-term-listp-of-expand-all-lambdas-lst
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (expand-all-lambdas-lst terms)))
    :flag expand-all-lambdas-lst))

(defthm-flag-expand-all-lambdas
  (defthm no-nils-in-termp-of-expand-all-lambdas
    (implies (and (no-nils-in-termp term)
                  (pseudo-termp term))
             (no-nils-in-termp (expand-all-lambdas term)))
    :flag expand-all-lambdas)
  (defthm no-nils-in-termsp-of-expand-all-lambdas-lst
    (implies (and (no-nils-in-termsp terms)
                  (pseudo-term-listp terms))
             (no-nils-in-termsp (expand-all-lambdas-lst terms)))
    :flag expand-all-lambdas-lst))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Like the recursion in expand-all-lambdas, but the alist changes when we
;; enter a lambda body.
(local
 (defun induct-expand-all-lambdas (flg x a)
   (declare (xargs :measure (acl2-count x)))
   (if flg
       (if (or (variablep x)
               (fquotep x))
           a
         (if (flambdap (ffn-symb x))
             (list (induct-expand-all-lambdas nil (fargs x) a)
                   (induct-expand-all-lambdas t
                                              (lambda-body (ffn-symb x))
                                              (append (pairlis$ (lambda-formals (ffn-symb x))
                                                                (cterm-ev-lst (fargs x) a))
                                                      a)))
           (induct-expand-all-lambdas nil (fargs x) a)))
     (if (consp x)
         (list (induct-expand-all-lambdas t (car x) a)
               (induct-expand-all-lambdas nil (cdr x) a))
       a))))

(local
 (defthm expand-all-lambdas-correct-flag
   (if flg
       (implies (and (pseudo-termp x)
                     (lambdas-closed-in-termp x)
                     (no-nils-in-termp x))
                (equal (cterm-ev (expand-all-lambdas x) a)
                       (cterm-ev x a)))
     (implies (and (pseudo-term-listp x)
                   (lambdas-closed-in-termsp x)
                   (no-nils-in-termsp x))
              (equal (cterm-ev-lst (expand-all-lambdas-lst x) a)
                     (cterm-ev-lst x a))))
   :rule-classes nil
   :hints (("Goal" :induct (induct-expand-all-lambdas flg x a)
            :in-theory (enable cterm-ev-of-fncall-args)))))

(defthm expand-all-lambdas-correct
  (implies (and (pseudo-termp term)
                (lambdas-closed-in-termp term)
                (no-nils-in-termp term))
           (equal (cterm-ev (expand-all-lambdas term) a)
                  (cterm-ev term a)))
  :hints (("Goal" :use (:instance expand-all-lambdas-correct-flag (flg t) (x term)))))

(defthm expand-all-lambdas-lst-correct
  (implies (and (pseudo-term-listp terms)
                (lambdas-closed-in-termsp terms)
                (no-nils-in-termsp terms))
           (equal (cterm-ev-lst (expand-all-lambdas-lst terms) a)
                  (cterm-ev-lst terms a)))
  :hints (("Goal" :use (:instance expand-all-lambdas-correct-flag (flg nil) (x terms)))))

;; Every proper term satisfies the hyps of expand-all-lambdas-correct (see
;; helpers.lisp).
(defthm expand-all-lambdas-correct-when-termp
  (implies (termp term w)
           (equal (cterm-ev (expand-all-lambdas term) a)
                  (cterm-ev term a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Counterexamples showing that the hyps of expand-all-lambdas-correct (other
;; than pseudo-termp) cannot be dropped are in expand-all-lambdas-tests.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What EXPAND-ALL-LAMBDAS is for: the result contains no lambdas.  It also
;; preserves termp.

(local (include-book "kestrel/terms-light/termp" :dir :system))

(defthm-flag-expand-all-lambdas
  (defthm lambda-free-termp-of-expand-all-lambdas
    (implies (pseudo-termp term)
             (lambda-free-termp (expand-all-lambdas term)))
    :flag expand-all-lambdas)
  (defthm lambda-free-termsp-of-expand-all-lambdas-lst
    (implies (pseudo-term-listp terms)
             (lambda-free-termsp (expand-all-lambdas-lst terms)))
    :flag expand-all-lambdas-lst)
  :hints (("Goal" :in-theory (enable lambda-free-termp))))

(defthm-flag-expand-all-lambdas
  (defthm termp-of-expand-all-lambdas
    (implies (termp term w)
             (termp (expand-all-lambdas term) w))
    :flag expand-all-lambdas)
  (defthm term-listp-of-expand-all-lambdas-lst
    (implies (term-listp terms w)
             (term-listp (expand-all-lambdas-lst terms) w))
    :flag expand-all-lambdas-lst))

;; These two are trivial, since the result has no lambdas.
(defthm lambdas-closed-in-termp-of-expand-all-lambdas
  (implies (pseudo-termp term)
           (lambdas-closed-in-termp (expand-all-lambdas term))))

(defthm no-duplicate-lambda-formals-in-termp-of-expand-all-lambdas
  (implies (pseudo-termp term)
           (no-duplicate-lambda-formals-in-termp (expand-all-lambdas term))))
