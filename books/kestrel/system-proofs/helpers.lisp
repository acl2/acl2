; Helper lemmas for the proofs in this directory
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The lemmas in this book are about general-purpose functions
;; (collect-by-position, free-vars-in-term, termp, arglistp, etc.) and probably
;; belong in libraries such as kestrel/lists-light and kestrel/terms-light.
;; They are collected here so that the proofs in this directory don't require
;; changes to those libraries.

(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(include-book "kestrel/terms-light/lambda-free-termp" :dir :system)
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/add-to-set-equal" :dir :system))
(local (include-book "tools/flag" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; collect-by-position (perhaps for a new kestrel/lists-light book)

;; (collect-by-position sub-domain full-domain full-range) collects the
;; elements of FULL-RANGE whose corresponding elements of FULL-DOMAIN are
;; members of SUB-DOMAIN.

(defthm len-of-collect-by-position
  (equal (len (collect-by-position sub-domain full-domain full-range))
         (len (intersection-equal full-domain sub-domain)))
  :hints (("Goal" :in-theory (enable intersection-equal))))

;; Pairing the kept elements of FULL-DOMAIN with the collected elements of
;; FULL-RANGE gives the same bindings for keys in SUB-DOMAIN.
(defthm assoc-equal-of-pairlis$-of-intersection-equal-and-collect-by-position
  (implies (member-equal key sub-domain)
           (equal (assoc-equal key (pairlis$ (intersection-equal full-domain sub-domain)
                                             (collect-by-position sub-domain full-domain full-range)))
                  (assoc-equal key (pairlis$ full-domain full-range))))
  :hints (("Goal" :in-theory (enable intersection-equal pairlis$ assoc-equal))))

(defthm subsetp-equal-of-collect-by-position
  (implies (<= (len full-domain) (len full-range))
           (subsetp-equal (collect-by-position sub-domain full-domain full-range)
                          full-range))
  :hints (("Goal" :in-theory (enable collect-by-position subsetp-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Splitting a list into the members that are in Y and those that are not
;; (perhaps for kestrel/lists-light)

(local
 (defthmd member-equal-of-append-local
   (iff (member-equal a (append x y))
        (or (member-equal a x)
            (member-equal a y)))))

(local
 (defthm subsetp-equal-of-append-of-intersection-equal-and-set-difference-equal-helper
   (implies (and (subsetp-equal x z)
                 (subsetp-equal x w))
            (subsetp-equal x (append (intersection-equal y z)
                                     (set-difference-equal w y))))
   :hints (("Goal" :in-theory (enable subsetp-equal member-equal-of-append-local)))))

(defthm subsetp-equal-of-append-of-intersection-equal-and-set-difference-equal
  (subsetp-equal x (append (intersection-equal y x)
                           (set-difference-equal x y))))

(local
 (defthm set-difference-equal-of-intersection-equal-when-subsetp-equal
   (implies (subsetp-equal x z)
            (equal (set-difference-equal x (intersection-equal y z))
                   (set-difference-equal x y)))
   :hints (("Goal" :in-theory (enable subsetp-equal set-difference-equal)))))

(defthm set-difference-equal-of-intersection-equal-same
  (equal (set-difference-equal x (intersection-equal y x))
         (set-difference-equal x y)))

(defthm subsetp-equal-of-union-equal-of-set-difference-equal-same
  (subsetp-equal x (union-equal y (set-difference-equal x y)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthm not-intersection-equal-of-set-difference-equal-when-subsetp-equal
  (implies (subsetp-equal x y)
           (not (intersection-equal x (set-difference-equal z y))))
  :hints (("Goal" :in-theory (enable subsetp-equal intersection-equal))))

(defthm not-intersection-equal-of-intersection-equal-and-set-difference-equal
  (not (intersection-equal (intersection-equal y x)
                           (set-difference-equal z y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; free-vars-in-term (for kestrel/terms-light/free-vars-in-term.lisp)

(defthm free-vars-in-term-when-not-all-vars1
  (implies (not (all-vars1 term nil))
           (equal (free-vars-in-term term)
                  nil))
  :hints (("Goal" :use subsetp-equal-of-free-vars-in-term-and-all-vars1
           :in-theory (disable subsetp-equal-of-free-vars-in-term-and-all-vars1))))

(defthm not-consp-of-free-vars-in-term-when-not-all-vars1
  (implies (not (all-vars1 term nil))
           (not (consp (free-vars-in-term term))))
  :hints (("Goal" :use subsetp-equal-of-free-vars-in-term-and-all-vars1
           :in-theory (disable subsetp-equal-of-free-vars-in-term-and-all-vars1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; all-vars (perhaps for kestrel/terms-light/all-vars1.lisp)

(defthm no-duplicatesp-equal-of-add-to-set-equal
  (implies (no-duplicatesp-equal x)
           (no-duplicatesp-equal (add-to-set-equal a x)))
  :hints (("Goal" :in-theory (enable add-to-set-equal))))

(defthm arglistp1-of-add-to-set-equal
  (implies (and (arglistp1 x)
                (legal-variablep a))
           (arglistp1 (add-to-set-equal a x)))
  :hints (("Goal" :in-theory (enable add-to-set-equal arglistp1))))

(local (make-flag all-vars1))

(defthm-flag-all-vars1
  (defthm no-duplicatesp-equal-of-all-vars1
    (implies (no-duplicatesp-equal ans)
             (no-duplicatesp-equal (all-vars1 term ans)))
    :flag all-vars1)
  (defthm no-duplicatesp-equal-of-all-vars1-lst
    (implies (no-duplicatesp-equal ans)
             (no-duplicatesp-equal (all-vars1-lst lst ans)))
    :flag all-vars1-lst)
  :hints (("Goal" :in-theory (enable all-vars1 all-vars1-lst))))

(defthm no-duplicatesp-equal-of-all-vars
  (no-duplicatesp-equal (all-vars term))
  :hints (("Goal" :in-theory (enable all-vars))))

;; The variables of a proper term are legal variables.
(defthm-flag-all-vars1
  (defthm arglistp1-of-all-vars1
    (implies (and (termp term w)
                  (arglistp1 ans))
             (arglistp1 (all-vars1 term ans)))
    :flag all-vars1)
  (defthm arglistp1-of-all-vars1-lst
    (implies (and (term-listp lst w)
                  (arglistp1 ans))
             (arglistp1 (all-vars1-lst lst ans)))
    :flag all-vars1-lst)
  :hints (("Goal" :in-theory (enable all-vars1 all-vars1-lst arglistp1 termp))))

(defthm not-member-equal-of-nil-and-all-vars1-when-no-nils-in-termp
  (implies (no-nils-in-termp term)
           (not (member-equal nil (all-vars1 term nil))))
  :hints (("Goal" :use ((:instance member-equal-when-subsetp-equal-1
                                   (x nil)
                                   (lst2 (all-vars1 term nil))
                                   (lst (free-vars-in-term term)))
                        subsetp-equal-of-all-vars1-of-nil-and-free-vars-in-term
                        not-member-equal-of-nil-and-free-vars-in-term)
           :in-theory (disable member-equal-when-subsetp-equal-1
                               member-equal-when-subsetp-equal-2))))

(defthm arglistp1-of-all-vars
  (implies (termp term w)
           (arglistp1 (all-vars term)))
  :hints (("Goal" :in-theory (enable all-vars))))

;; A list of legal variables is a list of terms.
;; Same as in books/system/legal-variablep.lisp.
(local
 (defthm symbolp-when-legal-variablep-local
   (implies (legal-variablep x)
            (and (symbolp x)
                 (not (equal x t))
                 (not (equal x nil))))
   :rule-classes :compound-recognizer
   :hints (("Goal" :in-theory (disable member-equal)))))

(defthm termp-when-legal-variablep
  (implies (legal-variablep x)
           (termp x w))
  :hints (("Goal" :expand (termp x w)
           :in-theory (disable legal-variablep))))

(defthm term-listp-when-arglistp1
  (implies (arglistp1 vars)
           (term-listp vars w))
  :hints (("Goal" :in-theory (enable arglistp1 term-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Every proper term has closed lambdas and contains no NIL variables.  These
;; are also proved, locally, in lambdas-closed-in-termp.lisp and
;; no-nils-in-termp.lisp in kestrel/terms-light/.

(local (make-flag lambdas-closed-in-termp))

(defthm-flag-lambdas-closed-in-termp
  (defthm lambdas-closed-in-termp-when-termp
    (implies (termp term w) ; w is a free var
             (lambdas-closed-in-termp term))
    :flag lambdas-closed-in-termp)
  (defthm lambdas-closed-in-termsp-when-term-listp
    (implies (term-listp terms w) ; w is a free var
             (lambdas-closed-in-termsp terms))
    :flag lambdas-closed-in-termsp)
  :hints (("Goal" :expand (free-vars-in-terms terms)
           :in-theory (enable free-vars-in-term lambdas-closed-in-termp))))

(local (make-flag no-nils-in-termp))

(defthm-flag-no-nils-in-termp
  (defthm no-nils-in-termp-when-termp
    (implies (termp term w) ; w is a free var
             (no-nils-in-termp term))
    :flag no-nils-in-termp)
  (defthm no-nils-in-termsp-when-term-listp
    (implies (term-listp terms w) ; w is a free var
             (no-nils-in-termsp terms))
    :flag no-nils-in-termsp)
  :hints (("Goal" :expand (free-vars-in-terms terms)
           :in-theory (enable free-vars-in-term no-nils-in-termp no-nils-in-termsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lambda applications

(defthm subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
  (implies (and (termp term w)
                (consp (car term)))
           (subsetp-equal (free-vars-in-term (lambda-body (car term)))
                          (lambda-formals (car term)))))

(defthm not-consp-of-free-vars-in-term-of-lambda-body-of-car-when-termp
  (implies (and (termp term w)
                (consp (car term))
                (not (consp (lambda-formals (car term)))))
           (not (consp (free-vars-in-term (lambda-body (car term))))))
  :hints (("Goal" :use subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
           :in-theory (disable subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp))))

(defthm not-member-equal-of-nil-and-free-vars-in-term-of-lambda-body-of-car-when-termp
  (implies (and (termp term w)
                (consp (car term)))
           (not (member-equal nil (free-vars-in-term (lambda-body (car term))))))
  :hints (("Goal" :use (:instance no-nils-in-termp-when-termp (term (lambda-body (car term))))
           :in-theory (disable no-nils-in-termp-when-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A lambda-free term trivially has closed lambdas and no duplicate lambda
;; formals (perhaps for kestrel/terms-light/lambda-free-termp.lisp).

(local (make-flag lambda-free-termp))

(defthm-flag-lambda-free-termp
  (defthm lambdas-closed-in-termp-when-lambda-free-termp
    (implies (lambda-free-termp term)
             (lambdas-closed-in-termp term))
    :flag lambda-free-termp)
  (defthm lambdas-closed-in-termsp-when-lambda-free-termsp
    (implies (lambda-free-termsp terms)
             (lambdas-closed-in-termsp terms))
    :flag lambda-free-termsp)
  :hints (("Goal" :in-theory (enable lambda-free-termp lambda-free-termsp
                                     lambdas-closed-in-termp lambdas-closed-in-termsp))))

(defthm-flag-lambda-free-termp
  (defthm no-duplicate-lambda-formals-in-termp-when-lambda-free-termp
    (implies (lambda-free-termp term)
             (no-duplicate-lambda-formals-in-termp term))
    :flag lambda-free-termp)
  (defthm no-duplicate-lambda-formals-in-termsp-when-lambda-free-termsp
    (implies (lambda-free-termsp terms)
             (no-duplicate-lambda-formals-in-termsp terms))
    :flag lambda-free-termsp)
  :hints (("Goal" :in-theory (enable lambda-free-termp lambda-free-termsp
                                     no-duplicate-lambda-formals-in-termp
                                     no-duplicate-lambda-formals-in-termsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; arglistp (perhaps for a new kestrel/terms-light book).  Note that arglistp
;; could perhaps better be called legal-variable-listp.

;; Same as in books/system/remove-guard-holders.lisp.
(defthm arglistp-forward-to-symbol-listp
  (implies (arglistp x)
           (symbol-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable arglistp arglistp1))))

(defthm not-member-equal-of-nil-when-arglistp
  (implies (arglistp x)
           (not (member-equal nil x)))
  :hints (("Goal" :in-theory (enable arglistp arglistp1))))

(defthm symbolp-when-member-equal-and-arglistp
  (implies (and (member-equal v x)
                (arglistp x))
           (symbolp v))
  :hints (("Goal" :in-theory (enable arglistp arglistp1))))

(defthm symbolp-of-car-when-arglistp
  (implies (arglistp x)
           (symbolp (car x)))
  :hints (("Goal" :in-theory (enable arglistp arglistp1))))

(defthm car-when-arglistp
  (implies (and (arglistp x)
                (consp x))
           (car x))
  :hints (("Goal" :in-theory (enable arglistp arglistp1))))

(defthm legal-variablep-when-member-equal-and-arglistp1
  (implies (and (member-equal var vars)
                (arglistp1 vars))
           (legal-variablep var))
  :hints (("Goal" :in-theory (e/d (arglistp1) (legal-variablep)))))

(defthm arglistp1-of-append
  (implies (and (arglistp1 x)
                (arglistp1 y))
           (arglistp1 (append x y)))
  :hints (("Goal" :in-theory (e/d (arglistp1 append) (legal-variablep)))))

(defthm arglistp1-of-set-difference-equal
  (implies (arglistp1 x)
           (arglistp1 (set-difference-equal x y)))
  :hints (("Goal" :in-theory (e/d (arglistp1 set-difference-equal) (legal-variablep)))))

;; The members of the intersection are members of Y.
(defthm arglistp1-of-intersection-equal-when-arglistp1-arg2
  (implies (arglistp1 y)
           (arglistp1 (intersection-equal x y)))
  :hints (("Goal" :in-theory (e/d (arglistp1 intersection-equal) (legal-variablep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; termp (for kestrel/terms-light/termp.lisp)

(local (include-book "kestrel/terms-light/termp" :dir :system))

(defthm len-of-cdr-when-termp
  (implies (and (termp term w)
                (consp term)
                (not (eq 'quote (car term))))
           (equal (len (cdr term))
                  (arity (car term) w)))
  :hints (("Goal" :in-theory (enable arity termp))))

(defthm symbolp-of-car-when-termp
  (implies (and (termp term w)
                (not (consp (car term))))
           (symbolp (car term)))
  :hints (("Goal" :expand (termp term w))))

(defthm term-listp-of-cdr-when-termp
  (implies (and (termp term w)
                (consp term)
                (not (equal 'quote (car term))))
           (term-listp (cdr term) w))
  :hints (("Goal" :expand (termp term w))))

;; for the second argument
(defthm termp-of-caddr-when-termp
  (implies (and (termp term w)
                (consp term)
                (not (eq 'quote (car term)))
                (< 1 (arity (car term) w)))
           (termp (caddr term) w))
  :hints (("Goal" :use (term-listp-of-cdr-when-termp
                        len-of-cdr-when-termp)
           :expand ((term-listp (cdr term) w)
                    (term-listp (cddr term) w)
                    (len (cdr term))
                    (len (cddr term)))
           :in-theory (disable term-listp-of-cdr-when-termp len-of-cdr-when-termp arity len))))

(defthm term-listp-of-append
  (implies (and (term-listp x w)
                (term-listp y w))
           (term-listp (append x y) w))
  :hints (("Goal" :in-theory (enable append))))

(defthm termp-of-car-of-last-when-term-listp
  (implies (and (term-listp terms w)
                (consp terms))
           (termp (car (last terms)) w)))

;; for the last argument
(defthm termp-of-car-of-last-of-cdr-when-termp
  (implies (and (termp term w)
                (consp term)
                (not (equal 'quote (car term)))
                (symbolp (car term))
                (< 0 (arity (car term) w)))
           (termp (car (last (cdr term))) w))
  :hints (("Goal" :expand ((termp term w))
           :cases ((consp (cdr term)))
           :use (:instance termp-of-car-of-last-when-term-listp (terms (cdr term)))
           :in-theory (disable termp-of-car-of-last-when-term-listp last))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lambda applications

(defthm termp-of-lambda-body-of-car-when-termp
  (implies (and (termp term w)
                (consp (car term)))
           (termp (lambda-body (car term)) w))
  :hints (("Goal" :expand (termp term w))))

(defthm pseudo-termp-of-lambda-body-of-car-when-termp
  (implies (and (termp term w)
                (consp (car term)))
           (pseudo-termp (lambda-body (car term))))
  :hints (("Goal" :use termp-of-lambda-body-of-car-when-termp
           :in-theory (disable termp-of-lambda-body-of-car-when-termp))))

(defthm arglistp-of-lambda-formals-of-car-when-termp
  (implies (and (termp term w)
                (consp (car term)))
           (arglistp (lambda-formals (car term))))
  :hints (("Goal" :expand (termp term w))))

(defthm consp-of-cdr-when-termp-and-consp-of-lambda-formals-of-car
  (implies (and (termp term w)
                (consp (car term))
                (consp (lambda-formals (car term))))
           (consp (cdr term)))
  :hints (("Goal" :use len-of-lambda-formals-of-car-when-termp
           :expand ((len (lambda-formals (car term)))
                    (len (cdr term)))
           :in-theory (disable len-of-lambda-formals-of-car-when-termp))))

;; for the first argument
(defthm termp-of-cadr-when-termp-and-consp-of-lambda-formals-of-car
  (implies (and (termp term w)
                (consp (car term))
                (consp (lambda-formals (car term))))
           (termp (cadr term) w))
  :hints (("Goal" :use term-listp-of-cdr-when-termp
           :expand ((term-listp (cdr term) w))
           :in-theory (disable term-listp-of-cdr-when-termp))))

;; Replacing the arguments of a call with the same number of terms gives a term.
(defthm termp-of-cons-of-car-when-termp
  (implies (and (termp term w)
                (consp term)
                (not (equal 'quote (car term)))
                (term-listp args w)
                (equal (len args) (len (cdr term))))
           (termp (cons (car term) args) w))
  :hints (("Goal" :expand ((termp term w))
           :in-theory (enable termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; subcor-var1 (perhaps for books/system/subcor-var.lisp)

;; SUBCOR-VAR1 returns VAR or one of the TERMS (or NIL, if there are fewer
;; TERMS than VARS).

(defthm termp-of-subcor-var1
  (implies (and (termp var w)
                (term-listp terms w)
                (equal (len vars) (len terms)))
           (termp (subcor-var1 vars terms var) w))
  :hints (("Goal" :induct (subcor-var1 vars terms var) :in-theory (enable subcor-var1))))

(defthm no-nils-in-termp-of-subcor-var1
  (implies (and (no-nils-in-termp var)
                (no-nils-in-termsp terms)
                (equal (len vars) (len terms)))
           (no-nils-in-termp (subcor-var1 vars terms var)))
  :hints (("Goal" :induct (subcor-var1 vars terms var) :in-theory (enable subcor-var1))))

(defthm lambda-free-termp-of-subcor-var1
  (implies (and (symbolp var)
                (lambda-free-termsp terms))
           (lambda-free-termp (subcor-var1 vars terms var)))
  :hints (("Goal" :induct (subcor-var1 vars terms var) :in-theory (enable subcor-var1 lambda-free-termp))))

(defthm lambdas-closed-in-termp-of-subcor-var1
  (implies (and (symbolp var)
                (lambdas-closed-in-termsp terms))
           (lambdas-closed-in-termp (subcor-var1 vars terms var)))
  :hints (("Goal" :induct (subcor-var1 vars terms var) :in-theory (enable subcor-var1 lambdas-closed-in-termp))))

(defthm no-duplicate-lambda-formals-in-termp-of-subcor-var1
  (implies (and (symbolp var)
                (no-duplicate-lambda-formals-in-termsp terms))
           (no-duplicate-lambda-formals-in-termp (subcor-var1 vars terms var)))
  :hints (("Goal" :induct (subcor-var1 vars terms var) :in-theory (enable subcor-var1 no-duplicate-lambda-formals-in-termp))))

(defthm subsetp-equal-of-free-vars-in-term-of-subcor-var1
  (implies (and (symbolp var)
                (equal (len vars) (len terms)))
           (subsetp-equal (free-vars-in-term (subcor-var1 vars terms var))
                          (union-equal (free-vars-in-terms terms)
                                       (set-difference-equal (list var) vars))))
  :hints (("Goal" :induct (subcor-var1 vars terms var) :in-theory (enable subcor-var1 free-vars-in-terms free-vars-in-term))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; collect-by-position of terms gives terms (if there are enough of them)

(defthm term-listp-of-collect-by-position
  (implies (and (term-listp full-range w)
                (<= (len full-domain) (len full-range)))
           (term-listp (collect-by-position sub-domain full-domain full-range) w))
  :hints (("Goal" :in-theory (enable collect-by-position))))

(defthm pseudo-term-listp-of-collect-by-position
  (implies (pseudo-term-listp full-range)
           (pseudo-term-listp (collect-by-position sub-domain full-domain full-range)))
  :hints (("Goal" :in-theory (enable collect-by-position))))

(defthm no-nils-in-termsp-of-collect-by-position
  (implies (and (no-nils-in-termsp full-range)
                (<= (len full-domain) (len full-range)))
           (no-nils-in-termsp (collect-by-position sub-domain full-domain full-range)))
  :hints (("Goal" :in-theory (enable collect-by-position no-nils-in-termsp))))

(defthm lambdas-closed-in-termsp-of-collect-by-position
  (implies (lambdas-closed-in-termsp full-range)
           (lambdas-closed-in-termsp (collect-by-position sub-domain full-domain full-range)))
  :hints (("Goal" :in-theory (enable collect-by-position lambdas-closed-in-termsp))))

(defthm no-duplicate-lambda-formals-in-termsp-of-collect-by-position
  (implies (no-duplicate-lambda-formals-in-termsp full-range)
           (no-duplicate-lambda-formals-in-termsp (collect-by-position sub-domain full-domain full-range)))
  :hints (("Goal" :in-theory (enable collect-by-position no-duplicate-lambda-formals-in-termsp))))

(defthm subsetp-equal-of-free-vars-in-terms-of-collect-by-position
  (implies (<= (len full-domain) (len full-range))
           (subsetp-equal (free-vars-in-terms (collect-by-position sub-domain full-domain full-range))
                          (free-vars-in-terms full-range)))
  :hints (("Goal" :in-theory (enable collect-by-position free-vars-in-terms))))
