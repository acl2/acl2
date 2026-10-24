; Properties of the ACL2 system function remove-guard-holders1
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; See remove-guard-holders1.lisp for the correctness of REMOVE-GUARD-HOLDERS1
;; (it returns a term equal to its input).  This book proves other properties:
;;
;; - The CHANGEDP flag is accurate (when it is NIL, the term is returned
;;   unchanged), as the comments in remove-guard-holders1 say, provided every
;;   call of TO-DF has one argument (as in any TERMP).  (Before a recent fix to
;;   the TO-DF case, this failed for terms containing calls of TO-DF; see
;;   remove-guard-holders1.lisp.)
;;
;; - The result has no free variables that the input lacks, and it is a TERMP
;;   if the input is (and so its lambdas are closed, it contains no NIL
;;   variables, and its lambdas have no duplicate formals).
;;
;; - The result contains no guard holders, except inside calls of HIDE (which
;;   remove-guard-holders1 may leave alone), again provided every call of TO-DF
;;   has one argument.

(include-book "system/remove-guard-holders-weak" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(local (include-book "subcor-var"))
(local (include-book "cons-term-helpers"))
(local (include-book "helpers"))
(local (include-book "system/remove-guard-holders1" :dir :system))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "tools/flag" :dir :system))
(local (include-book "system/pseudo-termp-lemmas" :dir :system))
(local (include-book "system/legal-variablep" :dir :system))

;; We reason about subcor-var directly, rather than in terms of sublis-var1.
(local (in-theory (disable subcor-var-is-sublis-var1 subcor-var-lst-is-sublis-var1-lst)))

(local (make-flag remove-guard-holders1))

;; The term returned doesn't depend on changedp0 (for a pseudo-term; see
;; remove-guard-holders1.lisp).
(local
 (defthm cons-term-when-consp
   (implies (consp fn)
            (equal (cons-term fn args)
                   (cons fn args)))
   :hints (("Goal" :in-theory (enable cons-term cons-term1)))))

(local
 (defthm mv-nth-1-of-remove-guard-holders1-lst-when-unchanged-simple
   (implies (and (not (mv-nth 0 (remove-guard-holders1-lst lst lamp)))
                 (true-listp lst))
            (equal (mv-nth 1 (remove-guard-holders1-lst lst lamp))
                   lst))
   :hints (("Goal" :expand ((remove-guard-holders1-lst lst lamp))))))

(local
 (defthm-flag-remove-guard-holders1
   (defthm mv-nth-1-of-remove-guard-holders1-normalize-changedp0-helper
     (implies (pseudo-termp term)
              (equal (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))
                     (mv-nth 1 (remove-guard-holders1 nil term lamp))))
     :rule-classes nil
     :flag remove-guard-holders1)
   (defthm remove-guard-holders1-lst-dummy
     t
     :rule-classes nil
     :flag remove-guard-holders1-lst)
   :hints (("Goal" :expand ((remove-guard-holders1 changedp0 term lamp)
                            (remove-guard-holders1 nil term lamp))))))

(local
 (defthm mv-nth-1-of-remove-guard-holders1-normalize-changedp0
   (implies (and (syntaxp (not (equal changedp0 ''nil)))
                 (pseudo-termp term))
            (equal (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))
                   (mv-nth 1 (remove-guard-holders1 nil term lamp))))
   :hints (("Goal" :use mv-nth-1-of-remove-guard-holders1-normalize-changedp0-helper))))

;; Keep cons-term for the lemmas about it below.
(local (in-theory (disable cons-term-when-consp)))

(local
 (defthm pseudo-termp-of-car-of-last
   (implies (pseudo-term-listp terms)
            (pseudo-termp (car (last terms))))
   :hints (("Goal" :in-theory (enable last)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Every call of TO-DF in TERM has exactly one argument, as in any TERMP
;; (given the arity of TO-DF; see unary-to-df-callsp-when-termp below).
(mutual-recursion
 (defun unary-to-df-callsp (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil))
   (cond ((variablep term) t)
         ((fquotep term) t)
         (t (and (unary-to-df-callsp-lst (fargs term))
                 (if (eq (ffn-symb term) 'to-df)
                     (and (consp (fargs term))
                          (null (cdr (fargs term))))
                   t)
                 (if (flambdap (ffn-symb term))
                     (unary-to-df-callsp (lambda-body (ffn-symb term)))
                   t)))))
 (defun unary-to-df-callsp-lst (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       t
     (and (unary-to-df-callsp (car terms))
          (unary-to-df-callsp-lst (cdr terms))))))

(verify-guards unary-to-df-callsp)

(local (make-flag unary-to-df-callsp))

(defthm-flag-unary-to-df-callsp
  (defthm unary-to-df-callsp-when-termp
    (implies (and (termp term w)
                  (equal (arity 'to-df w) 1))
             (unary-to-df-callsp term))
    :flag unary-to-df-callsp)
  (defthm unary-to-df-callsp-lst-when-term-listp
    (implies (and (term-listp terms w)
                  (equal (arity 'to-df w) 1))
             (unary-to-df-callsp-lst terms))
    :flag unary-to-df-callsp-lst)
  :hints (("Goal" :expand ((termp term w)
                           (term-listp terms w)
                           (len (cdr term))
                           (len (cddr term))))))

(local
 (defthm unary-to-df-callsp-lst-of-cdr-when-unary-to-df-callsp
   (implies (and (unary-to-df-callsp term)
                 (consp term)
                 (not (equal 'quote (car term))))
            (unary-to-df-callsp-lst (cdr term)))
   :hints (("Goal" :expand (unary-to-df-callsp term)))))

(local
 (defthm unary-to-df-callsp-of-lambda-body-when-unary-to-df-callsp
   (implies (and (unary-to-df-callsp term)
                 (consp term)
                 (consp (car term)))
            (unary-to-df-callsp (caddr (car term))))
   :hints (("Goal" :expand (unary-to-df-callsp term)))))

(local
 (defthm unary-to-df-callsp-of-car-when-unary-to-df-callsp-lst
   (implies (unary-to-df-callsp-lst terms)
            (unary-to-df-callsp (car terms)))
   :hints (("Goal" :expand ((unary-to-df-callsp-lst terms)
                            (unary-to-df-callsp nil))))))

(local
 (defthm unary-to-df-callsp-lst-of-cdr-when-unary-to-df-callsp-lst
   (implies (unary-to-df-callsp-lst terms)
            (unary-to-df-callsp-lst (cdr terms)))
   :hints (("Goal" :expand ((unary-to-df-callsp-lst terms))))))

(local
 (defthm unary-to-df-callsp-of-car-of-last-when-unary-to-df-callsp-lst
   (implies (unary-to-df-callsp-lst terms)
            (unary-to-df-callsp (car (last terms))))
   :hints (("Goal" :in-theory (enable last unary-to-df-callsp-lst)
            :expand ((unary-to-df-callsp nil))))))

(local
 (defthm cddr-when-unary-to-df-callsp
   (implies (and (unary-to-df-callsp term)
                 (consp term)
                 (equal (car term) 'to-df))
            (and (consp (cdr term))
                 (not (cddr term))))
   :hints (("Goal" :expand (unary-to-df-callsp term)))))

(local
 (defthm equal-of-list-of-to-df-when-unary-to-df-callsp
   (implies (and (unary-to-df-callsp term)
                 (consp term)
                 (equal (car term) 'to-df))
            (equal (list 'to-df (cadr term))
                   term))
   :hints (("Goal" :use cddr-when-unary-to-df-callsp
            :in-theory (disable cddr-when-unary-to-df-callsp)))))

(local (in-theory (disable unary-to-df-callsp unary-to-df-callsp-lst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The CHANGEDP flag is accurate when every call of TO-DF has one argument:
;; "if changedp is nil, then changedp0 is nil and new-term is identical to
;; term".

(defthm-flag-remove-guard-holders1
  (defthm remove-guard-holders1-changedp-contract
    (implies (and (not (mv-nth 0 (remove-guard-holders1 changedp0 term lamp)))
                  (unary-to-df-callsp term))
             (and (not changedp0)
                  (equal (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))
                         term)))
    :rule-classes nil
    :flag remove-guard-holders1)
  (defthm remove-guard-holders1-lst-changedp-contract
    (implies (and (not (mv-nth 0 (remove-guard-holders1-lst lst lamp)))
                  (unary-to-df-callsp-lst lst)
                  (true-listp lst))
             (equal (mv-nth 1 (remove-guard-holders1-lst lst lamp))
                    lst))
    :flag remove-guard-holders1-lst)
  :hints (("Goal" :expand ((unary-to-df-callsp-lst lst)))))

(defthm mv-nth-1-of-remove-guard-holders1-when-unchanged
  (implies (and (not (mv-nth 0 (remove-guard-holders1 changedp0 term lamp)))
                (unary-to-df-callsp term))
           (equal (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))
                  term))
  :hints (("Goal" :use remove-guard-holders1-changedp-contract)))

(defthm mv-nth-0-of-remove-guard-holders1-when-changedp0
  (implies (and changedp0
                (unary-to-df-callsp term))
           (mv-nth 0 (remove-guard-holders1 changedp0 term lamp)))
  :hints (("Goal" :use remove-guard-holders1-changedp-contract)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The arities of the functions that remove-guard-holders1 treats specially or
;; introduces, as in any world that ACL2 actually uses.
(defund remove-guard-holders1-arities-okp (w)
  (declare (xargs :guard (plist-worldp-with-formals w)))
  (and (equal (arity 'return-last w) 3)
       (equal (arity 'mv-list w) 2)
       (equal (arity 'the-check w) 3)
       (equal (arity 'cons-with-hint w) 3)
       (equal (arity 'to-df w) 1)
       (equal (arity 'from-df w) 1)
       (equal (arity 'cons w) 2)
       (equal (arity 'do$ w) 6)))

(local
 (defthm arities-when-remove-guard-holders1-arities-okp
   (implies (remove-guard-holders1-arities-okp w)
            (and (equal (arity 'return-last w) 3)
                 (equal (arity 'mv-list w) 2)
                 (equal (arity 'the-check w) 3)
                 (equal (arity 'cons-with-hint w) 3)
                 (equal (arity 'to-df w) 1)
                 (equal (arity 'from-df w) 1)
                 (equal (arity 'cons w) 2)
                 (equal (arity 'do$ w) 6)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable remove-guard-holders1-arities-okp)))))

(local
 (defthm termp-of-car-of-last-of-cdr-when-termp-special
   (implies (and (termp term w)
                 (member-equal (car term) '(return-last mv-list the-check))
                 (remove-guard-holders1-arities-okp w))
            (termp (car (last (cdr term))) w))
   :hints (("Goal" :use termp-of-car-of-last-of-cdr-when-termp
            :in-theory (disable termp-of-car-of-last-of-cdr-when-termp last termp)))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-car-of-last
   (implies (consp terms)
            (subsetp-equal (free-vars-in-term (car (last terms)))
                           (free-vars-in-terms terms)))
   :hints (("Goal" :in-theory (enable last free-vars-in-terms)))))

(local
 (defthm consp-of-cdr-when-termp-special
   (implies (and (termp term w)
                 (member-equal (car term) '(return-last mv-list the-check))
                 (remove-guard-holders1-arities-okp w))
            (consp (cdr term)))
   :hints (("Goal" :expand (termp term w)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Remove-guard-holders1 introduces no free variables.

(local
 (defthm consp-of-mv-nth-1-of-remove-guard-holders1-lst
   (equal (consp (mv-nth 1 (remove-guard-holders1-lst lst lamp)))
          (consp lst))
   :hints (("Goal" :expand ((remove-guard-holders1-lst lst lamp))))))

(local
 (defthm termp-of-cadddr-when-return-last
   (implies (and (termp term w)
                 (equal (car term) 'return-last)
                 (remove-guard-holders1-arities-okp w))
            (termp (cadddr term) w))
   :hints (("Goal" :expand ((termp term w) (term-listp (cdr term) w) (term-listp (cddr term) w)
                            (term-listp (cdddr term) w))))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-cadddr
   (implies (and (consp term)
                 (not (equal 'quote (car term)))
                 (consp (cdddr term)))
            (subsetp-equal (free-vars-in-term (cadddr term))
                           (free-vars-in-term term)))
   :hints (("Goal" :expand ((free-vars-in-term term)
                            (free-vars-in-terms (cdr term))
                            (free-vars-in-terms (cddr term))
                            (free-vars-in-terms (cdddr term)))))))

;; Facts about the "logic" part of a lambda body of the form
;; (return-last 'mbe1-raw exec logic), which arises from let-mbe:

(local
 (defthm termp-of-mbe1-raw-logic-when-termp
   (implies (and (termp term w)
                 (consp (car term))
                 (equal (car (caddr (car term))) 'return-last)
                 (remove-guard-holders1-arities-okp w))
            (termp (cadddr (caddr (car term))) w))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-mbe1-raw-logic
   (implies (and (termp term w)
                 (consp (car term))
                 (equal (car (caddr (car term))) 'return-last)
                 (remove-guard-holders1-arities-okp w))
            (subsetp-equal (free-vars-in-term (cadddr (caddr (car term))))
                           (cadr (car term))))
   :hints (("Goal" :use (subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
                         (:instance subsetp-equal-of-free-vars-in-term-of-cadddr (term (caddr (car term)))))
            :in-theory (disable subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
                                subsetp-equal-of-free-vars-in-term-of-cadddr)))))

;; The free vars of a call are those of its arguments.
(local
 (defthm free-vars-in-term-when-call
   (implies (and (consp term)
                 (not (equal 'quote (car term))))
            (equal (free-vars-in-term term)
                   (free-vars-in-terms (cdr term))))
   :hints (("Goal" :expand (free-vars-in-term term)))))

(local
 (defthm subsetp-equal-of-free-vars-in-terms-of-take-chain
   (implies (and (subsetp-equal (free-vars-in-terms terms) x)
                 (<= n (len terms)))
            (subsetp-equal (free-vars-in-terms (take n terms)) x))
   :hints (("Goal" :in-theory (enable take free-vars-in-terms)))))

(local
 (defthm subsetp-equal-of-free-vars-in-term-of-subcor-var-chain
   (implies (and (subsetp-equal (free-vars-in-terms terms) x)
                 (subsetp-equal (free-vars-in-term form) vars)
                 (equal (len vars) (len terms)))
            (subsetp-equal (free-vars-in-term (subcor-var vars terms form)) x))
   :hints (("Goal" :use subsetp-equal-of-free-vars-in-term-of-subcor-var
            :in-theory (disable subsetp-equal-of-free-vars-in-term-of-subcor-var)))))

(local
 (defthm subsetp-equal-of-free-vars-in-terms-when-symbol-listp
   (implies (symbol-listp vars)
            (subsetp-equal vars (free-vars-in-terms vars)))
   :hints (("Goal" :in-theory (enable free-vars-in-terms-when-symbol-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We prove properties of remove-guard-holders1 by induction, with a lemma for
;; each case of its definition (whose hypotheses include the property for the
;; recursive calls), so that remove-guard-holders1 can be disabled in the main
;; induction.

(local (include-book "kestrel/lists-light/len" :dir :system))

(local
 (defthm termp-of-cadr-when-termp-and-consp-of-cdr
   (implies (and (termp term w)
                 (consp term)
                 (not (equal 'quote (car term)))
                 (consp (cdr term)))
            (termp (cadr term) w))
   :hints (("Goal" :use term-listp-of-cdr-when-termp
            :expand ((term-listp (cdr term) w))
            :in-theory (disable term-listp-of-cdr-when-termp)))))

(local
 (defthm consp-of-cdr-when-termp-and-arity
   (implies (and (termp term w)
                 (consp term)
                 (not (equal 'quote (car term)))
                 (< 0 (arity (car term) w)))
            (consp (cdr term)))
   :hints (("Goal" :use len-of-cdr-when-termp
            :in-theory (disable len-of-cdr-when-termp)))))

(local
 (defthm consp-of-cddr-when-termp-and-arity
   (implies (and (termp term w)
                 (consp term)
                 (not (equal 'quote (car term)))
                 (< 1 (arity (car term) w)))
            (consp (cddr term)))
   :hints (("Goal" :use len-of-cdr-when-termp
            :in-theory (disable len-of-cdr-when-termp)))))

;; An induction scheme that follows the case structure of remove-guard-holders1.
(local
 (defun induct-remove-guard-holders1 (flg x)
   (declare (xargs :measure (acl2-count x)
                   :ruler-extenders :all
                   :verify-guards nil))
   (if flg
       (cond ((or (variablep x) (fquotep x)) nil)
             ((flambdap (ffn-symb x))
              (list (induct-remove-guard-holders1 nil (fargs x))
                    (if (consp (fargs x))
                        (induct-remove-guard-holders1 t (car (fargs x)))
                      nil)
                    (induct-remove-guard-holders1 t (lambda-body (ffn-symb x)))
                    (if (and (consp (lambda-body (ffn-symb x)))
                             (eq (car (lambda-body (ffn-symb x))) 'return-last))
                        (induct-remove-guard-holders1 t (car (cdr (cdr (cdr (lambda-body (ffn-symb x)))))))
                      nil)))
             ((member-eq (ffn-symb x) '(return-last mv-list the-check))
              (induct-remove-guard-holders1 t (car (last (fargs x)))))
             ((eq (ffn-symb x) 'cons-with-hint)
              (list (induct-remove-guard-holders1 t (cadr x))
                    (induct-remove-guard-holders1 t (caddr x))))
             ((member-eq (ffn-symb x) '(to-df from-df))
              (induct-remove-guard-holders1 t (cadr x)))
             (t (induct-remove-guard-holders1 nil (fargs x))))
     (if (consp x)
         (list (induct-remove-guard-holders1 t (car x))
               (induct-remove-guard-holders1 nil (cdr x)))
       nil))))

(local (in-theory (disable remove-guard-holders1 remove-guard-holders1-lst)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Free vars

(local
 (defthm mv-nth-1-of-remove-guard-holders1-when-atom-or-quote
   (implies (or (atom x)
                (equal 'quote (car x)))
            (equal (mv-nth 1 (remove-guard-holders1 nil x lamp))
                   x))
   :hints (("Goal" :expand ((remove-guard-holders1 nil x lamp))))))

(local
 (defthm free-vars-case-non-lambda
   (implies (and (consp x)
                 (not (equal 'quote (car x)))
                 (not (consp (car x)))
                 (termp x w)
                 (remove-guard-holders1-arities-okp w)
                 (implies (member-equal (car x) '(return-last mv-list the-check))
                          (subsetp-equal (free-vars-in-term (mv-nth 1 (remove-guard-holders1 nil (car (last (cdr x))) lamp)))
                                         (free-vars-in-term (car (last (cdr x))))))
                 (implies (member-equal (car x) '(cons-with-hint to-df from-df))
                          (subsetp-equal (free-vars-in-term (mv-nth 1 (remove-guard-holders1 nil (cadr x) lamp)))
                                         (free-vars-in-term (cadr x))))
                 (implies (equal (car x) 'cons-with-hint)
                          (subsetp-equal (free-vars-in-term (mv-nth 1 (remove-guard-holders1 nil (caddr x) lamp)))
                                         (free-vars-in-term (caddr x))))
                 (implies (not (member-equal (car x) '(return-last mv-list the-check cons-with-hint to-df from-df)))
                          (subsetp-equal (free-vars-in-terms (mv-nth 1 (remove-guard-holders1-lst (cdr x) lamp)))
                                         (free-vars-in-terms (cdr x)))))
            (subsetp-equal (free-vars-in-term (mv-nth 1 (remove-guard-holders1 nil x lamp)))
                           (free-vars-in-term x)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil x lamp))
            :in-theory (disable take quote-listp last)))))

;; For a lambda whose (new) arguments are its formals:
(local
 (defthm subsetp-equal-of-free-vars-in-term-of-lambda-body-when-args-are-formals
   (implies (and (termp x w)
                 (consp (car x))
                 (equal (cadr (car x)) args2)
                 (subsetp-equal (free-vars-in-terms args2) (free-vars-in-terms (cdr x))))
            (subsetp-equal (free-vars-in-term (caddr (car x)))
                           (free-vars-in-terms (cdr x))))
   :hints (("Goal" :use ((:instance subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
                                    (term x))
                         (:instance subsetp-equal-transitive-alt
                                    (x (free-vars-in-term (caddr (car x))))
                                    (y (cadr (car x)))
                                    (z (free-vars-in-terms (cadr (car x)))))
                         (:instance subsetp-equal-transitive-alt
                                    (x (free-vars-in-term (caddr (car x))))
                                    (y (free-vars-in-terms (cadr (car x))))
                                    (z (free-vars-in-terms (cdr x)))))
            :in-theory (disable subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
                                subsetp-equal-transitive-alt
                                subsetp-equal-transitive-2-alt)))))

(local
 (defthm free-vars-case-lambda
   (implies (and (consp x)
                 (consp (car x))
                 (termp x w)
                 (remove-guard-holders1-arities-okp w)
                 (subsetp-equal (free-vars-in-terms (mv-nth 1 (remove-guard-holders1-lst (cdr x) lamp)))
                                (free-vars-in-terms (cdr x)))
                 (implies (consp (cdr x))
                          (subsetp-equal (free-vars-in-term (mv-nth 1 (remove-guard-holders1 nil (cadr x) lamp)))
                                         (free-vars-in-term (cadr x))))
                 (subsetp-equal (free-vars-in-term (mv-nth 1 (remove-guard-holders1 nil (caddr (car x)) lamp)))
                                (free-vars-in-term (caddr (car x))))
                 (implies (and (consp (caddr (car x)))
                               (equal (car (caddr (car x))) 'return-last))
                          (subsetp-equal (free-vars-in-term (mv-nth 1 (remove-guard-holders1 nil (cadddr (caddr (car x))) lamp)))
                                         (free-vars-in-term (cadddr (caddr (car x)))))))
            (subsetp-equal (free-vars-in-term (mv-nth 1 (remove-guard-holders1 nil x lamp)))
                           (free-vars-in-term x)))
   :hints (("Goal" :expand ((remove-guard-holders1 nil x lamp))
            :use ((:instance subsetp-equal-of-free-vars-in-term-of-lambda-body-when-args-are-formals
                             (args2 (mv-nth 1 (remove-guard-holders1-lst (cdr x) lamp))))
                  (:instance subsetp-equal-transitive-alt
                             (x (free-vars-in-term (mv-nth 1 (remove-guard-holders1 nil (caddr (car x)) lamp))))
                             (y (free-vars-in-term (caddr (car x))))
                             (z (free-vars-in-terms (cdr x)))))
            :in-theory (disable take quote-listp last
                                subsetp-equal-of-free-vars-in-term-of-lambda-body-when-args-are-formals)))))

(local (in-theory (disable free-vars-in-term-when-call)))

(local
 (defthm mv-nth-1-of-remove-guard-holders1-lst-of-nil
   (equal (mv-nth 1 (remove-guard-holders1-lst nil lamp))
          nil)
   :hints (("Goal" :expand ((remove-guard-holders1-lst nil lamp))))))

(local
 (defthm free-vars-flag
   (if flg
       (implies (and (termp x w)
                     (remove-guard-holders1-arities-okp w))
                (subsetp-equal (free-vars-in-term (mv-nth 1 (remove-guard-holders1 nil x lamp)))
                               (free-vars-in-term x)))
     (implies (and (term-listp x w)
                   (remove-guard-holders1-arities-okp w))
              (subsetp-equal (free-vars-in-terms (mv-nth 1 (remove-guard-holders1-lst x lamp)))
                             (free-vars-in-terms x))))
   :rule-classes nil
   :hints (("Goal" :induct (induct-remove-guard-holders1 flg x)
            :expand ((remove-guard-holders1-lst x lamp))
            :in-theory (disable free-vars-in-term-when-call last take quote-listp
                                free-vars-in-term-when-not-all-vars1
                                not-consp-of-free-vars-in-term-when-not-all-vars1)))))

(defthm subsetp-equal-of-free-vars-in-term-of-mv-nth-1-of-remove-guard-holders1
  (implies (and (termp term w)
                (remove-guard-holders1-arities-okp w))
           (subsetp-equal (free-vars-in-term (mv-nth 1 (remove-guard-holders1 changedp0 term lamp)))
                          (free-vars-in-term term)))
  :hints (("Goal" :use (:instance free-vars-flag (flg t) (x term)))))

(defthm subsetp-equal-of-free-vars-in-terms-of-mv-nth-1-of-remove-guard-holders1-lst
  (implies (and (term-listp lst w)
                (remove-guard-holders1-arities-okp w))
           (subsetp-equal (free-vars-in-terms (mv-nth 1 (remove-guard-holders1-lst lst lamp)))
                          (free-vars-in-terms lst)))
  :hints (("Goal" :use (:instance free-vars-flag (flg nil) (x lst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Remove-guard-holders1 preserves termp.

(local
 (defthm term-listp-of-take
   (implies (and (term-listp terms w)
                 (<= n (len terms)))
            (term-listp (take n terms) w))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm termp-case-non-lambda
   (implies (and (consp x)
                 (not (equal 'quote (car x)))
                 (not (consp (car x)))
                 (termp x w)
                 (remove-guard-holders1-arities-okp w)
                 (implies (member-equal (car x) '(return-last mv-list the-check))
                          (termp (mv-nth 1 (remove-guard-holders1 nil (car (last (cdr x))) lamp)) w))
                 (implies (member-equal (car x) '(cons-with-hint to-df from-df))
                          (termp (mv-nth 1 (remove-guard-holders1 nil (cadr x) lamp)) w))
                 (implies (equal (car x) 'cons-with-hint)
                          (termp (mv-nth 1 (remove-guard-holders1 nil (caddr x) lamp)) w))
                 (implies (not (member-equal (car x) '(return-last mv-list the-check cons-with-hint to-df from-df)))
                          (term-listp (mv-nth 1 (remove-guard-holders1-lst (cdr x) lamp)) w)))
            (termp (mv-nth 1 (remove-guard-holders1 nil x lamp)) w))
   :hints (("Goal" :expand ((remove-guard-holders1 nil x lamp))
            :in-theory (disable take quote-listp last)))))

(local
 (defthm not-set-difference-equal-of-all-vars-when-subsetp-equal-of-free-vars-in-term
   (implies (subsetp-equal (free-vars-in-term term) vars)
            (not (set-difference-equal (all-vars term) vars)))
   :hints (("Goal" :use set-difference-equal-of-all-vars-arg1-iff
            :in-theory (disable set-difference-equal-of-all-vars-arg1-iff)))))

(local
 (defthm termp-of-cons-of-lambda
   (implies (and (arglistp formals)
                 (termp body w)
                 (subsetp-equal (free-vars-in-term body) formals)
                 (term-listp args w)
                 (equal (len formals) (len args)))
            (termp (cons (list 'lambda formals body) args) w))))

(local
 (defthm consp-when-consp-of-cdr-forward
   (implies (consp (cdr x))
            (consp x))
   :rule-classes :forward-chaining))

;; The lambda made when the body changes is a term:
(local
 (defthm termp-of-cons-term-of-lambda-with-new-body
   (implies (and (termp x w)
                 (consp (car x))
                 (termp body2 w)
                 (subsetp-equal (free-vars-in-term body2) (free-vars-in-term (caddr (car x))))
                 (term-listp args2 w)
                 (equal (len args2) (len (cdr x))))
            (termp (cons-term (list 'lambda (cadr (car x)) body2) args2) w))
   :hints (("Goal" :use ((:instance subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
                                    (term x))
                         (:instance subsetp-equal-transitive-alt
                                    (x (free-vars-in-term body2))
                                    (y (free-vars-in-term (caddr (car x))))
                                    (z (cadr (car x)))))
            :in-theory (disable subsetp-equal-of-free-vars-in-term-of-lambda-body-of-car-when-termp
                                subsetp-equal-transitive-alt
                                cons-term)))))

(local
 (defthm termp-case-lambda
   (implies (and (consp x)
                 (consp (car x))
                 (termp x w)
                 (remove-guard-holders1-arities-okp w)
                 (term-listp (mv-nth 1 (remove-guard-holders1-lst (cdr x) lamp)) w)
                 (implies (consp (cdr x))
                          (termp (mv-nth 1 (remove-guard-holders1 nil (cadr x) lamp)) w))
                 (termp (mv-nth 1 (remove-guard-holders1 nil (caddr (car x)) lamp)) w)
                 (implies (and (consp (caddr (car x)))
                               (equal (car (caddr (car x))) 'return-last))
                          (termp (mv-nth 1 (remove-guard-holders1 nil (cadddr (caddr (car x))) lamp)) w)))
            (termp (mv-nth 1 (remove-guard-holders1 nil x lamp)) w))
   :hints (("Goal" :expand ((remove-guard-holders1 nil x lamp))
            :use (:instance subsetp-equal-of-free-vars-in-term-of-mv-nth-1-of-remove-guard-holders1
                            (term (caddr (car x)))
                            (changedp0 nil))
            :in-theory (disable take quote-listp last cons-term
                                subsetp-equal-of-free-vars-in-term-of-mv-nth-1-of-remove-guard-holders1)))))

(local
 (defthm termp-flag
   (if flg
       (implies (and (termp x w)
                     (remove-guard-holders1-arities-okp w))
                (termp (mv-nth 1 (remove-guard-holders1 nil x lamp)) w))
     (implies (and (term-listp x w)
                   (remove-guard-holders1-arities-okp w))
              (term-listp (mv-nth 1 (remove-guard-holders1-lst x lamp)) w)))
   :rule-classes nil
   :hints (("Goal" :induct (induct-remove-guard-holders1 flg x)
            :expand ((remove-guard-holders1-lst x lamp))
            :in-theory (disable last take quote-listp)))))

(defthm termp-of-mv-nth-1-of-remove-guard-holders1
  (implies (and (termp term w)
                (remove-guard-holders1-arities-okp w))
           (termp (mv-nth 1 (remove-guard-holders1 changedp0 term lamp)) w))
  :hints (("Goal" :use (:instance termp-flag (flg t) (x term)))))

(defthm term-listp-of-mv-nth-1-of-remove-guard-holders1-lst
  (implies (and (term-listp lst w)
                (remove-guard-holders1-arities-okp w))
           (term-listp (mv-nth 1 (remove-guard-holders1-lst lst lamp)) w))
  :hints (("Goal" :use (:instance termp-flag (flg nil) (x lst)))))

;; Consequences of termp:

(defthm no-nils-in-termp-of-mv-nth-1-of-remove-guard-holders1
  (implies (and (termp term w)
                (remove-guard-holders1-arities-okp w))
           (no-nils-in-termp (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))))
  :hints (("Goal" :use (:instance no-nils-in-termp-when-termp
                                  (term (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))))
           :in-theory (disable no-nils-in-termp-when-termp))))

(defthm lambdas-closed-in-termp-of-mv-nth-1-of-remove-guard-holders1
  (implies (and (termp term w)
                (remove-guard-holders1-arities-okp w))
           (lambdas-closed-in-termp (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))))
  :hints (("Goal" :use (:instance lambdas-closed-in-termp-when-termp
                                  (term (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))))
           :in-theory (disable lambdas-closed-in-termp-when-termp))))

(defthm no-duplicate-lambda-formals-in-termp-of-mv-nth-1-of-remove-guard-holders1
  (implies (and (termp term w)
                (remove-guard-holders1-arities-okp w))
           (no-duplicate-lambda-formals-in-termp (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))))
  :hints (("Goal" :use (:instance no-duplicate-lambda-formals-in-termp-when-termp
                                  (term (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))))
           :in-theory (disable no-duplicate-lambda-formals-in-termp-when-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What remove-guard-holders1 is for: the result contains no guard holders
;; (calls of RETURN-LAST, MV-LIST, THE-CHECK, CONS-WITH-HINT, FROM-DF, DF0, or
;; DF1), except inside calls of HIDE, which remove-guard-holders1 may leave
;; alone (depending on the attachment to
;; remove-guard-holders-blocked-by-hide-p).  This requires that the term
;; have only calls of TO-DF with one argument (as in any TERMP).

(defconst *guard-holders-removed-by-remove-guard-holders1*
  '(return-last mv-list the-check cons-with-hint from-df df0 df1))

(mutual-recursion
 (defun guard-holder-free-termp (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil))
   (cond ((variablep term) t)
         ((fquotep term) t)
         ((eq (ffn-symb term) 'hide) t)
         ((member-eq (ffn-symb term) *guard-holders-removed-by-remove-guard-holders1*) nil)
         (t (and (guard-holder-free-termsp (fargs term))
                 (if (flambdap (ffn-symb term))
                     (guard-holder-free-termp (lambda-body (ffn-symb term)))
                   t)))))
 (defun guard-holder-free-termsp (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       t
     (and (guard-holder-free-termp (car terms))
          (guard-holder-free-termsp (cdr terms))))))

(verify-guards guard-holder-free-termp)

(local (make-flag guard-holder-free-termp))

(local
 (defthm guard-holder-free-termsp-of-append
   (equal (guard-holder-free-termsp (append x y))
          (and (guard-holder-free-termsp x)
               (guard-holder-free-termsp y)))
   :hints (("Goal" :in-theory (enable append)))))

(local
 (defthm guard-holder-free-termsp-of-take
   (implies (and (guard-holder-free-termsp terms)
                 (<= n (len terms)))
            (guard-holder-free-termsp (take n terms)))
   :hints (("Goal" :in-theory (enable take)))))

(local
 (defthm guard-holder-free-termp-of-car
   (implies (guard-holder-free-termsp terms)
            (guard-holder-free-termp (car terms)))))

(local
 (defthm guard-holder-free-termp-of-cons-term
   (implies (and (guard-holder-free-termsp args)
                 (not (member-equal fn *guard-holders-removed-by-remove-guard-holders1*))
                 (implies (consp fn)
                          (guard-holder-free-termp (caddr fn))))
            (guard-holder-free-termp (cons-term fn args)))
   :hints (("Goal" :use cons-term-cases
            :in-theory (disable cons-term)))))

(local
 (defthm guard-holder-free-termp-of-cons-term-of-hide
   (guard-holder-free-termp (cons-term 'hide args))
   :hints (("Goal" :use (:instance cons-term-cases (fn 'hide))
            :in-theory (disable cons-term)))))

(local (make-flag subcor-var))

(local
 (defthm guard-holder-free-termp-of-subcor-var1
   (implies (and (guard-holder-free-termsp terms)
                 (symbolp var))
            (guard-holder-free-termp (subcor-var1 vars terms var)))
   :hints (("Goal" :induct (subcor-var1 vars terms var)
            :in-theory (enable subcor-var1)))))

(local
 (defthm-flag-subcor-var
   (defthm guard-holder-free-termp-of-subcor-var
     (implies (and (guard-holder-free-termp form)
                   (guard-holder-free-termsp terms))
              (guard-holder-free-termp (subcor-var vars terms form)))
     :flag subcor-var)
   (defthm guard-holder-free-termsp-of-subcor-var-lst
     (implies (and (guard-holder-free-termsp forms)
                   (guard-holder-free-termsp terms))
              (guard-holder-free-termsp (subcor-var-lst vars terms forms)))
     :flag subcor-var-lst)
   :hints (("Goal" :expand ((guard-holder-free-termp form))
            :in-theory (disable cons-term subcor-var1-in-terms-of-cdr-assoc)))))

(local
 (defthm mv-nth-1-of-remove-guard-holders1-lst-when-unchanged
   (implies (and (not (mv-nth 0 (remove-guard-holders1-lst lst lamp)))
                 (unary-to-df-callsp-lst lst)
                 (true-listp lst))
            (equal (mv-nth 1 (remove-guard-holders1-lst lst lamp))
                   lst))
   :hints (("Goal" :use remove-guard-holders1-lst-changedp-contract))))

(local
 (defthm guard-holder-free-case-non-lambda
   (implies (and (consp x)
                 (not (equal 'quote (car x)))
                 (not (consp (car x)))
                 (pseudo-termp x)
                 (unary-to-df-callsp x)
                 (implies (member-equal (car x) '(return-last mv-list the-check))
                          (guard-holder-free-termp (mv-nth 1 (remove-guard-holders1 nil (car (last (cdr x))) lamp))))
                 (implies (member-equal (car x) '(cons-with-hint to-df from-df))
                          (guard-holder-free-termp (mv-nth 1 (remove-guard-holders1 nil (cadr x) lamp))))
                 (implies (equal (car x) 'cons-with-hint)
                          (guard-holder-free-termp (mv-nth 1 (remove-guard-holders1 nil (caddr x) lamp))))
                 (implies (not (member-equal (car x) '(return-last mv-list the-check cons-with-hint to-df from-df)))
                          (guard-holder-free-termsp (mv-nth 1 (remove-guard-holders1-lst (cdr x) lamp)))))
            (guard-holder-free-termp (mv-nth 1 (remove-guard-holders1 nil x lamp))))
   :hints (("Goal" :expand ((remove-guard-holders1 nil x lamp)
                            (guard-holder-free-termp x))
            :in-theory (disable take quote-listp last cons-term)))))

(local
 (defthm guard-holder-free-case-lambda
   (implies (and (consp x)
                 (consp (car x))
                 (pseudo-termp x)
                 (unary-to-df-callsp x)
                 (guard-holder-free-termsp (mv-nth 1 (remove-guard-holders1-lst (cdr x) lamp)))
                 (implies (consp (cdr x))
                          (guard-holder-free-termp (mv-nth 1 (remove-guard-holders1 nil (cadr x) lamp))))
                 (guard-holder-free-termp (mv-nth 1 (remove-guard-holders1 nil (caddr (car x)) lamp)))
                 (implies (and (consp (caddr (car x)))
                               (equal (car (caddr (car x))) 'return-last))
                          (guard-holder-free-termp (mv-nth 1 (remove-guard-holders1 nil (cadddr (caddr (car x))) lamp)))))
            (guard-holder-free-termp (mv-nth 1 (remove-guard-holders1 nil x lamp))))
   :hints (("Goal" :expand ((remove-guard-holders1 nil x lamp)
                            (guard-holder-free-termp x))
            :use ((:instance remove-guard-holders1-lst-changedp-contract
                             (lst (cdr x)))
                  (:instance remove-guard-holders1-changedp-contract
                             (term (caddr (car x)))
                             (changedp0 nil)))
            :in-theory (disable take quote-listp last cons-term)))))

(local
 (defthm guard-holder-free-flag
   (if flg
       (implies (and (pseudo-termp x)
                     (unary-to-df-callsp x))
                (guard-holder-free-termp (mv-nth 1 (remove-guard-holders1 nil x lamp))))
     (implies (and (pseudo-term-listp x)
                   (unary-to-df-callsp-lst x))
              (guard-holder-free-termsp (mv-nth 1 (remove-guard-holders1-lst x lamp)))))
   :rule-classes nil
   :hints (("Goal" :induct (induct-remove-guard-holders1 flg x)
            :expand ((remove-guard-holders1-lst x lamp))
            :in-theory (disable last take quote-listp)))))

(defthm guard-holder-free-termp-of-mv-nth-1-of-remove-guard-holders1
  (implies (and (pseudo-termp term)
                (unary-to-df-callsp term))
           (guard-holder-free-termp (mv-nth 1 (remove-guard-holders1 changedp0 term lamp))))
  :hints (("Goal" :use (:instance guard-holder-free-flag (flg t) (x term)))))

(defthm guard-holder-free-termsp-of-mv-nth-1-of-remove-guard-holders1-lst
  (implies (and (pseudo-term-listp lst)
                (unary-to-df-callsp-lst lst))
           (guard-holder-free-termsp (mv-nth 1 (remove-guard-holders1-lst lst lamp))))
  :hints (("Goal" :use (:instance guard-holder-free-flag (flg nil) (x lst)))))

;; The hypothesis about TO-DF is needed for the CHANGEDP contract: see
;; remove-guard-holders1-changedp-needs-unary-to-df in
;; remove-guard-holders1-properties-tests.lisp.  (This doesn't indicate a bug,
;; since translated terms have correct arities.)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The same properties for remove-guard-holders-weak, which ACL2 calls (it
;; just returns the term computed by remove-guard-holders1):

(defthm subsetp-equal-of-free-vars-in-term-of-remove-guard-holders-weak
  (implies (and (termp term w)
                (remove-guard-holders1-arities-okp w))
           (subsetp-equal (free-vars-in-term (remove-guard-holders-weak term lamp))
                          (free-vars-in-term term)))
  :hints (("Goal" :in-theory (enable remove-guard-holders-weak))))

(defthm termp-of-remove-guard-holders-weak
  (implies (and (termp term w)
                (remove-guard-holders1-arities-okp w))
           (termp (remove-guard-holders-weak term lamp) w))
  :hints (("Goal" :in-theory (enable remove-guard-holders-weak))))

(defthm guard-holder-free-termp-of-remove-guard-holders-weak
  (implies (and (pseudo-termp term)
                (unary-to-df-callsp term))
           (guard-holder-free-termp (remove-guard-holders-weak term lamp)))
  :hints (("Goal" :in-theory (enable remove-guard-holders-weak))))
