; Correctness of the ACL2 system function sublis-expr
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; SUBLIS-EXPR (in other-processes.lisp) replaces each term in the domain of
;; ALIST with the corresponding term in its range, wherever it occurs in TERM
;; (but not inside lambda bodies).  It is used by generalization (to replace
;; terms with new variables; see generalize-clause), by destructor elimination
;; (see eliminate-destructors-clause1), when checking :elim rules (see
;; chk-acceptable-elim-rule), and by induction (see sublis-tests-rev).

;; SUBLIS-EXPR is in :program mode in the sources.  We put it in :logic mode
;; here.  The measures are a bit unusual because SUBLIS-EXPR-LST tests for
;; the end of the list with NULL, so it recurs (once) on a non-NIL atom.

(verify-termination
  (sublis-expr (declare (xargs :measure (if (consp term)
                                            (+ 2 (* 2 (acl2-count term)))
                                          0))))
  (sublis-expr-lst (declare (xargs :measure (if (null lst)
                                                0
                                              (+ 1 (* 2 (acl2-count lst))))))))

(include-book "clause-processors/sublis-var-meaning" :dir :system) ; for cterm-ev and the correctness of cons-term
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(local (include-book "cterm-ev-helpers"))
(local (include-book "helpers"))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "tools/flag" :dir :system))

(local (make-flag sublis-expr))

;; Each term in the domain of ALIST has the same value, in A, as the
;; corresponding term in the range.
(defund cterm-ev-pairs-agreep (alist a)
  (declare (xargs :guard (alistp alist)
                  :verify-guards nil))
  (if (endp alist)
      t
    (and (equal (cterm-ev (car (car alist)) a)
                (cterm-ev (cdr (car alist)) a))
         (cterm-ev-pairs-agreep (cdr alist) a))))

(local
 (defthm cterm-ev-of-cdr-of-assoc-equal-when-cterm-ev-pairs-agreep
   (implies (and (cterm-ev-pairs-agreep alist a)
                 (assoc-equal term alist)
                 (alistp alist))
            (equal (cterm-ev (cdr (assoc-equal term alist)) a)
                   (cterm-ev term a)))
   :hints (("Goal" :in-theory (enable cterm-ev-pairs-agreep assoc-equal)))))

(defthm-flag-sublis-expr
  (defthm sublis-expr-correct
    (implies (and (cterm-ev-pairs-agreep alist a)
                  (alistp alist)
                  (pseudo-termp term))
             (equal (cterm-ev (sublis-expr alist term) a)
                    (cterm-ev term a)))
    :flag sublis-expr)
  (defthm sublis-expr-lst-correct
    (implies (and (cterm-ev-pairs-agreep alist a)
                  (alistp alist)
                  (pseudo-term-listp lst))
             (equal (cterm-ev-lst (sublis-expr-lst alist lst) a)
                    (cterm-ev-lst lst a)))
    :flag sublis-expr-lst)
  :hints (("Goal" :in-theory (enable cterm-ev-of-fncall-args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What SUBLIS-EXPR is for: generalization.  Replacing TERMS with new
;; variables VARS (that occur neither in TERM nor in TERMS) gives a term whose
;; value, when the VARS are bound to the values of the TERMS, is the value of
;; TERM.  So if the generalized term is true for all values of the VARS, the
;; original term is true.  This is how generalize-clause uses SUBLIS-EXPR.

(local
 (defthm cterm-ev-pairs-agreep-of-pairlis$
   (implies (and (equal (cterm-ev-lst vars b)
                        (cterm-ev-lst terms b))
                 (equal (len vars) (len terms)))
            (cterm-ev-pairs-agreep (pairlis$ terms vars) b))
   :hints (("Goal" :induct (pairlis$ terms vars)
            :in-theory (enable cterm-ev-pairs-agreep pairlis$)))))

(local
 (defthm cterm-ev-lst-of-cons-of-cons-irrelevant
   (implies (and (symbol-listp vars)
                 (not (member-equal key vars)))
            (equal (cterm-ev-lst vars (cons (cons key val) alist))
                   (cterm-ev-lst vars alist)))
   :hints (("Goal" :induct (len vars)))))

(local
 (defthm cterm-ev-lst-of-vars-and-append-of-pairlis$
   (implies (and (symbol-listp vars)
                 (no-duplicatesp-equal vars)
                 (not (member-equal nil vars))
                 (equal (len vars) (len vals)))
            (equal (cterm-ev-lst vars (append (pairlis$ vars vals) alist))
                   (true-list-fix vals)))
   :hints (("Goal" :induct (pairlis$ vars vals)
            :in-theory (enable pairlis$ true-list-fix)))))

(local
 (defthm assoc-equal-of-append-of-pairlis$-when-not-member-equal
   (implies (not (member-equal key vars))
            (equal (assoc-equal key (append (pairlis$ vars vals) alist))
                   (assoc-equal key alist)))
   :hints (("Goal" :in-theory (enable pairlis$ assoc-equal)))))

(local
 (defthm alists-equiv-on-of-append-of-pairlis$-when-not-intersection-equal
   (implies (not (intersection-equal vars keys))
            (alists-equiv-on keys (append (pairlis$ vars vals) alist) alist))
   :hints (("Goal" :induct (len keys)
            :in-theory (e/d (alists-equiv-on)
                            (alists-equiv-on-of-append-arg2))))))

(local
 (defthm cterm-ev-of-append-of-pairlis$-irrelevant
   (implies (and (not (intersection-equal vars (free-vars-in-term term)))
                 (pseudo-termp term))
            (equal (cterm-ev term (append (pairlis$ vars vals) alist))
                   (cterm-ev term alist)))
   :hints (("Goal" :use (:instance equal-of-cterm-ev-and-cterm-ev-when-alists-equiv-on
                                   (keys (free-vars-in-term term))
                                   (alist1 (append (pairlis$ vars vals) alist))
                                   (alist2 alist))
            :in-theory (e/d (alists-equiv-on-of-append-of-pairlis$-when-not-intersection-equal)
                            (equal-of-cterm-ev-and-cterm-ev-when-alists-equiv-on))))))

(local
 (defthm not-intersection-equal-of-free-vars-in-term-of-car
   (implies (and (not (intersection-equal vars (free-vars-in-terms terms)))
                 (consp terms))
            (not (intersection-equal vars (free-vars-in-term (car terms)))))
   :hints (("Goal" :expand (free-vars-in-terms terms)
            :in-theory (enable intersection-equal)))))

(local
 (defthm not-intersection-equal-of-free-vars-in-terms-of-cdr
   (implies (not (intersection-equal vars (free-vars-in-terms terms)))
            (not (intersection-equal vars (free-vars-in-terms (cdr terms)))))
   :hints (("Goal" :expand (free-vars-in-terms terms)
            :in-theory (enable intersection-equal)))))

(local
 (defthm cterm-ev-lst-of-append-of-pairlis$-irrelevant
   (implies (and (not (intersection-equal vars (free-vars-in-terms terms)))
                 (pseudo-term-listp terms))
            (equal (cterm-ev-lst terms (append (pairlis$ vars vals) alist))
                   (cterm-ev-lst terms alist)))
   :hints (("Goal" :induct (len terms)
            :in-theory (disable pairlis$)))))

(local
 (defthm len-of-cterm-ev-lst
   (equal (len (cterm-ev-lst terms a))
          (len terms))
   :hints (("Goal" :induct (len terms)))))

(local
 (defthm true-listp-of-cterm-ev-lst
   (true-listp (cterm-ev-lst terms a))
   :hints (("Goal" :induct (len terms)))))

(local
 (defthm cterm-ev-pairs-agreep-for-generalization
   (implies (and (not (intersection-equal vars (free-vars-in-terms terms)))
                 (symbol-listp vars)
                 (no-duplicatesp-equal vars)
                 (not (member-equal nil vars))
                 (equal (len vars) (len terms))
                 (pseudo-term-listp terms))
            (cterm-ev-pairs-agreep (pairlis$ terms vars)
                                   (append (pairlis$ vars (cterm-ev-lst terms a)) a)))
   :hints (("Goal" :use (:instance cterm-ev-pairs-agreep-of-pairlis$
                                   (b (append (pairlis$ vars (cterm-ev-lst terms a)) a)))
            :in-theory (disable cterm-ev-pairs-agreep-of-pairlis$)))))

(defthm sublis-expr-of-pairlis$-generalizes
  (implies (and (not (intersection-equal vars (free-vars-in-term term)))
                (not (intersection-equal vars (free-vars-in-terms terms)))
                (symbol-listp vars)
                (no-duplicatesp-equal vars)
                (not (member-equal nil vars))
                (equal (len vars) (len terms))
                (pseudo-termp term)
                (pseudo-term-listp terms))
           (equal (cterm-ev (sublis-expr (pairlis$ terms vars) term)
                            (append (pairlis$ vars (cterm-ev-lst terms a)) a))
                  (cterm-ev term a)))
  :hints (("Goal" :do-not-induct t
           :use (:instance sublis-expr-correct
                           (alist (pairlis$ terms vars))
                           (a (append (pairlis$ vars (cterm-ev-lst terms a)) a)))
           :in-theory (disable sublis-expr-correct))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Properties of terms that SUBLIS-EXPR preserves, given that the terms in the
;; range of the ALIST have them.

(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(local (include-book "cons-term-helpers"))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))

(defthm len-of-sublis-expr-lst
  (implies (true-listp lst)
           (equal (len (sublis-expr-lst alist lst))
                  (len lst)))
  :hints (("Goal" :induct (len lst)
           :in-theory (enable sublis-expr-lst))))

(local
 (defthm termp-of-cdr-of-assoc-equal
   (implies (and (term-listp (strip-cdrs alist) w)
                 (assoc-equal key alist))
            (termp (cdr (assoc-equal key alist)) w))
   :hints (("Goal" :in-theory (enable assoc-equal)))))

(local
 (defthm pseudo-termp-of-cdr-of-assoc-equal
   (implies (pseudo-term-listp (strip-cdrs alist))
            (pseudo-termp (cdr (assoc-equal key alist))))
   :hints (("Goal" :in-theory (enable assoc-equal)))))

(local
 (defthm lambdas-closed-in-termp-of-cdr-of-assoc-equal
   (implies (lambdas-closed-in-termsp (strip-cdrs alist))
            (lambdas-closed-in-termp (cdr (assoc-equal key alist))))
   :hints (("Goal" :in-theory (enable assoc-equal lambdas-closed-in-termsp)))))

(local
 (defthm no-duplicate-lambda-formals-in-termp-of-cdr-of-assoc-equal
   (implies (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist))
            (no-duplicate-lambda-formals-in-termp (cdr (assoc-equal key alist))))
   :hints (("Goal" :in-theory (enable assoc-equal no-duplicate-lambda-formals-in-termsp)))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-cdr-of-assoc-equal
   (implies (assoc-equal key alist)
            (subsetp-equal (free-vars-in-term (cdr (assoc-equal key alist)))
                           (free-vars-in-terms (strip-cdrs alist))))
   :hints (("Goal" :in-theory (enable assoc-equal free-vars-in-terms)))))

(defthm-flag-sublis-expr
  (defthm pseudo-termp-of-sublis-expr
    (implies (and (pseudo-termp term)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-termp (sublis-expr alist term)))
    :flag sublis-expr)
  (defthm pseudo-term-listp-of-sublis-expr-lst
    (implies (and (pseudo-term-listp lst)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-term-listp (sublis-expr-lst alist lst)))
    :flag sublis-expr-lst)
  :hints (("Goal" :expand ((pseudo-termp term)))))

(defthm-flag-sublis-expr
  (defthm termp-of-sublis-expr
    (implies (and (termp term w)
                  (term-listp (strip-cdrs alist) w))
             (termp (sublis-expr alist term) w))
    :flag sublis-expr)
  (defthm term-listp-of-sublis-expr-lst
    (implies (and (term-listp lst w)
                  (term-listp (strip-cdrs alist) w))
             (term-listp (sublis-expr-lst alist lst) w))
    :flag sublis-expr-lst)
  :hints (("Goal" :expand ((termp term w)))))

(defthm-flag-sublis-expr
  (defthm no-nils-in-termp-of-sublis-expr
    (implies (and (no-nils-in-termp term)
                  (no-nils-in-termsp (strip-cdrs alist))
                  (pseudo-termp term))
             (no-nils-in-termp (sublis-expr alist term)))
    :flag sublis-expr)
  (defthm no-nils-in-termsp-of-sublis-expr-lst
    (implies (and (no-nils-in-termsp lst)
                  (no-nils-in-termsp (strip-cdrs alist))
                  (pseudo-term-listp lst))
             (no-nils-in-termsp (sublis-expr-lst alist lst)))
    :flag sublis-expr-lst))

(defthm-flag-sublis-expr
  (defthm lambdas-closed-in-termp-of-sublis-expr
    (implies (and (lambdas-closed-in-termp term)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termp (sublis-expr alist term)))
    :flag sublis-expr)
  (defthm lambdas-closed-in-termsp-of-sublis-expr-lst
    (implies (and (lambdas-closed-in-termsp lst)
                  (lambdas-closed-in-termsp (strip-cdrs alist)))
             (lambdas-closed-in-termsp (sublis-expr-lst alist lst)))
    :flag sublis-expr-lst)
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp))))

(defthm-flag-sublis-expr
  (defthm no-duplicate-lambda-formals-in-termp-of-sublis-expr
    (implies (and (no-duplicate-lambda-formals-in-termp term)
                  (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist)))
             (no-duplicate-lambda-formals-in-termp (sublis-expr alist term)))
    :flag sublis-expr)
  (defthm no-duplicate-lambda-formals-in-termsp-of-sublis-expr-lst
    (implies (and (no-duplicate-lambda-formals-in-termsp lst)
                  (no-duplicate-lambda-formals-in-termsp (strip-cdrs alist)))
             (no-duplicate-lambda-formals-in-termsp (sublis-expr-lst alist lst)))
    :flag sublis-expr-lst)
  :hints (("Goal" :in-theory (enable no-duplicate-lambda-formals-in-termp))))

;; The free vars of the result are among those of TERM and those of the terms
;; in the range of ALIST.
(defthm-flag-sublis-expr
  (defthm subsetp-equal-of-free-vars-in-term-of-sublis-expr
    (implies (pseudo-termp term)
             (subsetp-equal (free-vars-in-term (sublis-expr alist term))
                            (union-equal (free-vars-in-term term)
                                         (free-vars-in-terms (strip-cdrs alist)))))
    :flag sublis-expr)
  (defthm subsetp-equal-of-free-vars-in-terms-of-sublis-expr-lst
    (implies (pseudo-term-listp lst)
             (subsetp-equal (free-vars-in-terms (sublis-expr-lst alist lst))
                            (union-equal (free-vars-in-terms lst)
                                         (free-vars-in-terms (strip-cdrs alist)))))
    :flag sublis-expr-lst)
  :hints (("Goal" :expand ((free-vars-in-term term)
                           (free-vars-in-terms lst)
                           (sublis-expr-lst alist lst))
           :do-not '(generalize eliminate-destructors))))
