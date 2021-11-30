; Utilities to merge terms into dags, with no simplification or evaluation
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This version does not handle embedded dags, resolve ifs, or evaluate ground terms.
;; See also merge-term-into-dag-array-basic.lisp.

(include-book "dag-array-builders2")
(include-book "kestrel/typed-lists-light/all-consp" :dir :system)
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp2" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system)) ;why does this break a proof below?
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

(local (in-theory (enable integerp-when-natp)))

(local (in-theory (disable consp-from-len-cheap
                           use-all-consp-for-car
                           USE-ALL-CONSP
                           USE-ALL-CONSP-2
                           NTH-WHEN-NOT-CONSP-CHEAP
                           NTH-WHEN-ZP-CHEAP
                           ALL-CONSP-WHEN-NOT-CONSP
                           NAT-LISTP
                           ALL-DARGP-LESS-THAN-WHEN-ALL-< ;limit?
                           ALL-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP-LIST
                           NTH-WHEN-<=-LEN-CHEAP
                           default-+-2
                           default-car
                           default-cdr
                           quote-lemma-for-all-dargp-less-than-gen-alt
                           symbol-alistp ;don't induct
                           wf-dagp-expander
                           wf-dagp
                           member-equal
                           use-all-<-for-car
                           all-dargp-less-than-when-<-of-largest-non-quotep
                           ;;all-dargp-less-than-when-all-consp
                           strip-cdrs
                           )))

;;todo: this stuff is duplicated -- pull out into var-darg-alist book:

(defthmd true-listp-of-nth-1-of-nth-0-when-pseudo-termp
  (implies (and (pseudo-termp term)
                ;; (consp (nth 0 term))
                )
           (true-listp (nth 1 (nth 0 term))))
  :hints (("Goal" :expand (pseudo-termp term)
           :cases ((consp (nth 0 term)))
           :in-theory (enable pseudo-termp))))

(defthm lookup-equal-forward-to-assoc-equal
  (implies (lookup-equal key alist)
           (assoc-equal key alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable lookup-equal))))

;dup
(defthm assoc-equal-when-lookup-equal-cheap
  (implies (lookup-equal term var-replacement-alist)
           (assoc-equal term var-replacement-alist))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (enable lookup-equal))))

;dup
(defthm dargp-less-than-of-lookup-equal
  (implies (and (lookup-equal term var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist)
                                                dag-len))
           (dargp-less-than (lookup-equal term var-replacement-alist) dag-len))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthmd consp-of-lookup-equal-when-all-myquotep-of-strip-cdrs
  (implies (and (all-myquotep (strip-cdrs var-replacement-alist))
                (lookup-equal term var-replacement-alist))
           (consp (lookup-equal term var-replacement-alist)))
  :hints (("Goal" :in-theory (enable lookup-equal strip-cdrs strip-cdrs assoc-equal))))

;; (thm
;;  (implies (and (pseudo-termp term)
;;                (posp n)
;;                (not (equal 'quote (nth 0 term))))
;;           (pseudo-termp (nth n term)))
;;  :hints (("Goal" :in-theory (e/d (pseudo-termp nth) (NTH-OF-CDR)))))

;dup, needed?
(defthm dargp-of-lookup-equal-when-all-dargp-of-strip-cdrs
  (implies (all-dargp (strip-cdrs alist))
           (iff (dargp (lookup-equal var alist))
                (assoc-equal var alist)))
  :hints (("Goal" :induct t
           :in-theory (e/d (all-dargp lookup-equal strip-cdrs)
                           (myquotep)))))

;dup
(defthmd not-equal-of-len-and-1-when-dargp
  (implies (dargp x)
           (not (equal (len x) 1)))
  :hints (("Goal" :in-theory (enable dargp myquotep))))

;; TODO: Consider handling other versions of IF top-down.
;; TODO: Include subst in the name since this also substitutes for vars.
(mutual-recursion
 ;; This one can replace vars in term using var-replacement-alist (helps us deal with lambdas).
 ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
 ;; where nodenum-or-quotep is equivalent to the term passed in, and nodes already in the dag remain unchanged (and the aux. data structures have been updated, of course)
 (defund merge-term-into-dag-array-simple (term
                                           var-replacement-alist ; maps vars in TERM to quoteps or nodenums in DAG-ARRAY
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                           )
   (declare (xargs :guard (and (pseudo-termp term)
                               (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (symbol-alistp var-replacement-alist)
                               (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len))
                   :verify-guards nil ; see below
                   ))
   (if (variablep term)
       ;;it's a variable, so look up its possible replacement:
       (let ((nodenum-or-quotep (lookup-eq term var-replacement-alist)))
         (if nodenum-or-quotep
             (mv (erp-nil) nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           ;; no substitution applied to this var:
           (add-variable-to-dag-array-with-name term dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           ;; term is a quoted constant:
           (mv (erp-nil) term dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
         ;; term is a function call:
         (let* ((args (fargs term)))
           ;;begin by adding the args to the dag: (expensive to cons this up, if they are ground terms?)
           (mv-let
             (erp arg-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (merge-terms-into-dag-array-simple args var-replacement-alist
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                )
             (if erp
                 (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               (if (consp fn) ;tests for ((lambda <formals> <body>) ...<actuals>...) ;move this case up?
                   (let* ((formals (lambda-formals fn))
                          (body (lambda-body fn)))
                     (merge-term-into-dag-array-simple body
                                                       (pairlis$-fast formals arg-nodenums-or-quoteps) ;save this consing?
                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                       ))
                 ;; normal function call:
                 (add-function-call-expr-to-dag-array-with-name fn arg-nodenums-or-quoteps
                                                                dag-array dag-len dag-parent-array
                                                                dag-constant-alist dag-variable-alist
                                                                dag-array-name dag-parent-array-name)))))))))

 ;; Returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist), where nodenums-or-quoteps are equivalent to the terms passed in.
 ;; TODO: Consider using a changep flag to avoid reconsing the list?
 (defund merge-terms-into-dag-array-simple (terms
                                            var-replacement-alist
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                            )
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (true-listp terms)
                               (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (symbol-alistp var-replacement-alist)
                               (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len))))
   (if (endp terms)
       (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
     (b* (((mv erp car-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-term-into-dag-array-simple (first terms) var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             ))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
          ((mv erp cdr-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-terms-into-dag-array-simple (rest terms) var-replacement-alist
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                              ))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
       (mv (erp-nil)
           (cons car-nodenum-or-quotep cdr-nodenums-or-quoteps)
           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))

(make-flag merge-term-into-dag-array-simple)

(defthm-flag-merge-term-into-dag-array-simple
  (defthm natp-of-mv-nth-3-of-merge-term-into-dag-array-simple
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-term-into-dag-array-simple
                              term var-replacement-alist dag-array dag-len dag-parent-array
                              dag-constant-alist dag-variable-alist
                              dag-array-name dag-parent-array-name
                              ))))
    :flag merge-term-into-dag-array-simple)
  (defthm natp-of-mv-nth-3-of-merge-terms-into-dag-array-simple
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-terms-into-dag-array-simple
                              terms var-replacement-alist
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                              ))))
    :flag merge-terms-into-dag-array-simple)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array-simple merge-terms-into-dag-array-simple) (natp)))))

(defthm-flag-merge-term-into-dag-array-simple
  (defthm dag-variable-alistp-of-mv-nth-6-of-merge-term-into-dag-array-simple
    (implies (and (pseudo-termp term)
                  (dag-variable-alistp dag-variable-alist)
                  (natp dag-len))
             (dag-variable-alistp (mv-nth 6 (merge-term-into-dag-array-simple
                                             term var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             ))))
    :flag merge-term-into-dag-array-simple)
  (defthm dag-variable-alistp-of-mv-nth-6-of-merge-terms-into-dag-array-simple
    (implies (and (pseudo-term-listp terms)
                  (dag-variable-alistp dag-variable-alist)
                  (natp dag-len))
             (dag-variable-alistp (mv-nth 6 (merge-terms-into-dag-array-simple
                                             terms var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             ))))
    :flag merge-terms-into-dag-array-simple)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array-simple merge-terms-into-dag-array-simple) ()))))

(defthm-flag-merge-term-into-dag-array-simple
  (defthm merge-term-into-dag-array-simple-return-type
    (implies (and (pseudo-termp term)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))))
             (and (dargp-less-than (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))
                                   (mv-nth 3 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name )))
                  (wf-dagp dag-array-name
                           (mv-nth 2 (merge-term-into-dag-array-simple
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      ))
                           (mv-nth 3 (merge-term-into-dag-array-simple
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      ))
                           dag-parent-array-name
                           (mv-nth 4 (merge-term-into-dag-array-simple
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      ))
                           (mv-nth 5 (merge-term-into-dag-array-simple
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      ))
                           (mv-nth 6 (merge-term-into-dag-array-simple
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      )))
                  (<= dag-len
                      (mv-nth 3 (merge-term-into-dag-array-simple
                                 term
                                 var-replacement-alist
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 )))
                  ;; (<= (mv-nth 3 (merge-term-into-dag-array-simple
                  ;;                term
                  ;;                var-replacement-alist
                  ;;                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                  ;;                ))
                  ;;     2147483646)

                  ))
    :flag merge-term-into-dag-array-simple)
  (defthm merge-terms-into-dag-array-simple-return-type
    (implies (and (pseudo-term-listp terms)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-terms-into-dag-array-simple terms var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))))
             (and (true-listp (mv-nth 1 (merge-terms-into-dag-array-simple
                                         terms
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                         )))
                  (equal (len (mv-nth 1 (merge-terms-into-dag-array-simple
                                         terms
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                         )))
                         (len terms))
                  (all-dargp (mv-nth 1 (merge-terms-into-dag-array-simple
                                                   terms
                                                   var-replacement-alist
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                   )))
                  (all-dargp-less-than (mv-nth 1 (merge-terms-into-dag-array-simple
                                                             terms
                                                             var-replacement-alist
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                             ))
                                                  (mv-nth 3 (merge-terms-into-dag-array-simple
                                                             terms
                                                             var-replacement-alist
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                             )))
                  (wf-dagp dag-array-name
                           (mv-nth 2 (merge-terms-into-dag-array-simple
                                      terms
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      ))
                           (mv-nth 3 (merge-terms-into-dag-array-simple
                                      terms
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      ))
                           dag-parent-array-name
                           (mv-nth 4 (merge-terms-into-dag-array-simple
                                      terms
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      ))
                           (mv-nth 5 (merge-terms-into-dag-array-simple
                                      terms
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      ))
                           (mv-nth 6 (merge-terms-into-dag-array-simple
                                      terms
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      )))
                  (<= dag-len
                      (mv-nth 3 (merge-terms-into-dag-array-simple
                                 terms
                                 var-replacement-alist
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 )))
                  ;; (<= (mv-nth 3 (merge-terms-into-dag-array-simple
                  ;;                terms
                  ;;                var-replacement-alist
                  ;;                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                  ;;                ))
                  ;;     2147483646)
                  ))
    :flag merge-terms-into-dag-array-simple)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-term-into-dag-array-simple merge-terms-into-dag-array-simple car-becomes-nth-of-0)
                           (natp dargp pseudo-term-listp pseudo-termp)))))

(defthm merge-term-into-dag-array-simple-return-type-corollary
  (implies (and (<= bound dag-len)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))))
           (<= bound
               (mv-nth 3 (merge-term-into-dag-array-simple
                          term
                          var-replacement-alist
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                          ))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type))))

(defthm merge-term-into-dag-array-simple-return-type-linear
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))))
           (<= dag-len
               (mv-nth 3 (merge-term-into-dag-array-simple
                          term
                          var-replacement-alist
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                          ))))
  :rule-classes :linear
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type))))

(defthm dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-simple
  (implies (and (<= (mv-nth 3 (merge-term-into-dag-array-simple
                               term
                               var-replacement-alist
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                               ))
                    bound)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))))
           (DARGP-LESS-THAN
            (mv-nth 1 (merge-term-into-dag-array-simple
                       term
                       var-replacement-alist
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                       ))
            bound))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type))))

(defthm dargp-of-mv-nth-1-of-merge-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))))
           (dargp (mv-nth 1 (merge-term-into-dag-array-simple
                             term
                             var-replacement-alist
                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                             ))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-simple
                               dargp))))

(defthm merge-term-into-dag-array-simple-return-type-corollary3
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name )))
                (not (consp (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))))
                )
           (< (mv-nth 1 (merge-term-into-dag-array-simple
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         ))
              (mv-nth 3 (merge-term-into-dag-array-simple
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         ))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-simple
                               MERGE-TERM-INTO-DAG-ARRAY-SIMPLE-RETURN-TYPE-COROLLARY))))

(defthm merge-term-into-dag-array-simple-return-type-corollary3-gen
  (implies (and (<= (mv-nth 3 (merge-term-into-dag-array-simple
                               term
                               var-replacement-alist
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                               ))
                    bound)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name )))
                (not (consp (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))))
                )
           (< (mv-nth 1 (merge-term-into-dag-array-simple
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         ))
              bound))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type-corollary3)
           :in-theory (disable merge-term-into-dag-array-simple-return-type-corollary3))))

(defthm merge-term-into-dag-array-simple-return-type-corollary4
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name )))
                (not (consp (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))))
                )
           (natp (mv-nth 1 (merge-term-into-dag-array-simple
                            term
                            var-replacement-alist
                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                            ))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type
                               dargp-of-mv-nth-1-of-merge-term-into-dag-array-simple
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-simple))))

(verify-guards merge-term-into-dag-array-simple
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-term-into-dag-array-simple merge-terms-into-dag-array-simple car-becomes-nth-of-0
                                                      not-equal-of-len-and-1-when-dargp
                                                      <-of-nth-when-all-dargp-less-than
                                                      true-listp-of-nth-1-of-nth-0-when-pseudo-termp
                                                      ALL-MYQUOTEP-WHEN-ALL-DARGP)
                           (natp dargp pseudo-term-listp pseudo-termp)))))

(defthm wf-dagp-of-merge-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                ;;no error:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name ))))
           (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (merge-term-into-dag-array-simple
              term
              var-replacement-alist
              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
              )
             (declare (ignore erp nodenum-or-quotep))
             (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type))))

(defthm wf-dagp-of-merge-terms-into-dag-array-simple
  (implies (and (pseudo-term-listp terms)
                (true-listp terms)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                (not (mv-nth 0 (merge-terms-into-dag-array-simple
                                terms
                                var-replacement-alist
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                ))))
           (mv-let (erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (merge-terms-into-dag-array-simple
              terms
              var-replacement-alist
              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
              )
             (declare (ignore erp nodenums-or-quoteps))
             (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :use (:instance merge-terms-into-dag-array-simple-return-type)
           :in-theory (disable merge-terms-into-dag-array-simple-return-type))))

(defthm-flag-merge-term-into-dag-array-simple
  (defthm true-listp-of-mv-nth-1-of-merge-terms-into-dag-array-simple-dummy
    t
    :rule-classes nil
    :flag merge-term-into-dag-array-simple)
  (defthm true-listp-of-mv-nth-1-of-merge-terms-into-dag-array-simple
    (true-listp (mv-nth 1 (merge-terms-into-dag-array-simple
                           terms var-replacement-alist
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                           )))
    :rule-classes :type-prescription
    :flag merge-terms-into-dag-array-simple)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array-simple merge-terms-into-dag-array-simple) (natp)))))

;; handle the case of a lambda whose body is a var
(defthm-flag-merge-term-into-dag-array-simple
  (defthm posp-of-mv-nth-3-of-merge-term-into-dag-array-simple
    (implies (and (natp dag-len)
                  (pseudo-termp term)
                  ;;(not (variablep term)) ;note this
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                  ;; no error:
                  (not (mv-nth 0 (merge-term-into-dag-array-simple
                                  term
                                  var-replacement-alist
                                  dag-array dag-len dag-parent-array
                                  dag-constant-alist dag-variable-alist
                                  dag-array-name dag-parent-array-name
                                  )))
                  ;; returns a nodenum, not a quotep:
                  (not (consp (mv-nth 1 (merge-term-into-dag-array-simple
                                         term
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array
                                         dag-constant-alist dag-variable-alist
                                         dag-array-name dag-parent-array-name
                                         )))))
             ;; the length can't be 0 after merging in the term
             (posp (mv-nth 3 (merge-term-into-dag-array-simple
                              term
                              var-replacement-alist
                              dag-array dag-len dag-parent-array
                              dag-constant-alist dag-variable-alist
                              dag-array-name dag-parent-array-name
                              ))))
    :flag merge-term-into-dag-array-simple)
  (defthm posp-of-mv-nth-3-of-merge-term-into-dag-array-simple-fake-helper
    t
    :rule-classes nil
    :flag merge-terms-into-dag-array-simple)
  :hints (("Goal" :in-theory (e/d ( ;merge-term-into-dag-array-simple
                                   merge-terms-into-dag-array-simple
                                   consp-of-lookup-equal-when-all-myquotep-of-strip-cdrs)
                                  (natp))
           :expand ((MERGE-TERM-INTO-DAG-ARRAY-SIMPLE TERM VAR-REPLACEMENT-ALIST
                                                     DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY
                                                     DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST
                                                     DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                                     )
                    (MERGE-TERM-INTO-DAG-ARRAY-SIMPLE TERM var-replacement-alist DAG-ARRAY 0 DAG-PARENT-ARRAY
                                                     DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST
                                                     DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                                     )))))
