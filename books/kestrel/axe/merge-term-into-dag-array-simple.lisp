; Utilities to merge terms into dags, with no simplification or evaluation
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This version does not handle embedded dags, resolve ifs, or evaluate ground terms.
;; See also merge-term-into-dag-array-basic.lisp.

(include-book "tools/flag" :dir :system)
(include-book "dag-array-builders2")
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/pairlis-dollar-fast" :dir :system)
(include-book "make-dag-indices")
(include-book "supporting-nodes")
(include-book "dag-array-builders") ; for empty-dag-array ; todo: factor out
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
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))
(local (include-book "kestrel/terms-light/all-vars1" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))

(local (in-theory (e/d (integerp-when-natp)
                       (consp-from-len-cheap
                        nth-when-not-consp-cheap
                        nth-when-zp-cheap
                        nat-listp
                        bounded-darg-listp-when-all-< ;limit?
                        all-<-of-alen1-when-pseudo-dag-arrayp-list
                        nth-when-<=-len-cheap
                        default-+-2
                        default-car
                        default-cdr
                        quote-lemma-for-bounded-darg-listp-gen-alt
                        symbol-alistp ;don't induct
                        wf-dagp-expander
                        wf-dagp
                        member-equal
                        use-all-<-for-car
                        bounded-darg-listp-when-<-of-largest-non-quotep
                        ;;bounded-darg-listp-when-all-consp
                        strip-cdrs
                        ;; for speed:
                        pseudo-termp))))

;move!
(defthm dargp-less-than-of-car-of-car-and-len
  (implies (pseudo-dagp dag)
           (dargp-less-than (car (car dag)) (len dag)))
  :hints (("Goal" :in-theory (enable dargp-less-than pseudo-dagp))))

;;todo: this stuff is duplicated -- pull out into var-darg-alist book:

(defthmd true-listp-of-nth-1-of-nth-0-when-pseudo-termp
  (implies (and (pseudo-termp term)
                ;; (consp (nth 0 term))
                )
           (true-listp (nth 1 (nth 0 term))))
  :hints (("Goal" :expand (pseudo-termp term)
           :cases ((consp (nth 0 term)))
           :in-theory (enable pseudo-termp
                              nth-of-0
                              nth-when-not-consp-cheap))))

;dup
(defthm dargp-less-than-of-lookup-equal
  (implies (and (lookup-equal term var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist)
                                                dag-len))
           (dargp-less-than (lookup-equal term var-replacement-alist) dag-len))
  :hints (("Goal" :in-theory (enable lookup-equal strip-cdrs))))

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
(defthm dargp-of-lookup-equal-when-darg-listp-of-strip-cdrs
  (implies (darg-listp (strip-cdrs alist))
           (iff (dargp (lookup-equal var alist))
                (assoc-equal var alist)))
  :hints (("Goal" :induct t
           :in-theory (e/d (darg-listp lookup-equal strip-cdrs)
                           (myquotep)))))

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
                               (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len))
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
           ;;begin by adding the args to the dag:
           ;; TODO: Consider adding them in reverse order, to make XOR nests more likely to be commuted right (larger nodenums first):
           (mv-let
             (erp arg-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (merge-terms-into-dag-array-simple args var-replacement-alist
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
             (if erp
                 (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               (if (consp fn) ;tests for ((lambda <formals> <body>) ...<actuals>...)
                   (let* ((formals (lambda-formals fn))
                          (body (lambda-body fn)))
                     (merge-term-into-dag-array-simple body
                                                       (pairlis$-fast formals arg-nodenums-or-quoteps) ;save this consing?
                                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                 ;; normal function call:
                 (add-function-call-expr-to-dag-array-with-name fn arg-nodenums-or-quoteps
                                                                dag-array dag-len dag-parent-array
                                                                dag-constant-alist dag-variable-alist
                                                                dag-array-name dag-parent-array-name)))))))))

 ;; Returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist), where nodenums-or-quoteps are equivalent to the terms passed in.
 ;; TODO: Consider using a changep flag to avoid reconsing the list?
 (defund merge-terms-into-dag-array-simple (terms
                                            var-replacement-alist
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (true-listp terms)
                               (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (symbol-alistp var-replacement-alist)
                               (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len))))
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
                              dag-array-name dag-parent-array-name))))
    :flag merge-term-into-dag-array-simple)
  (defthm natp-of-mv-nth-3-of-merge-terms-into-dag-array-simple
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-terms-into-dag-array-simple
                              terms var-replacement-alist
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
    :flag merge-terms-into-dag-array-simple)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array-simple merge-terms-into-dag-array-simple) (natp)))))

(defthm-flag-merge-term-into-dag-array-simple
  (defthm dag-variable-alistp-of-mv-nth-6-of-merge-term-into-dag-array-simple
    (implies (and (pseudo-termp term)
                  (dag-variable-alistp dag-variable-alist)
                  (natp dag-len))
             (dag-variable-alistp (mv-nth 6 (merge-term-into-dag-array-simple
                                             term var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
    :flag merge-term-into-dag-array-simple)
  (defthm dag-variable-alistp-of-mv-nth-6-of-merge-terms-into-dag-array-simple
    (implies (and (pseudo-term-listp terms)
                  (dag-variable-alistp dag-variable-alist)
                  (natp dag-len))
             (dag-variable-alistp (mv-nth 6 (merge-terms-into-dag-array-simple
                                             terms var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
    :flag merge-terms-into-dag-array-simple)
  :hints (("Goal" :in-theory (enable merge-term-into-dag-array-simple merge-terms-into-dag-array-simple))))

(defthm-flag-merge-term-into-dag-array-simple
  (defthm merge-term-into-dag-array-simple-return-type
    (implies (and (pseudo-termp term)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
             (and (dargp-less-than (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                                   (mv-nth 3 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
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
                  ;;     *max-1d-array-length*)

                  ))
    :flag merge-term-into-dag-array-simple)
  (defthm merge-terms-into-dag-array-simple-return-type
    (implies (and (pseudo-term-listp terms)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-terms-into-dag-array-simple terms var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
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
                  (darg-listp (mv-nth 1 (merge-terms-into-dag-array-simple
                                                   terms
                                                   var-replacement-alist
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                   )))
                  (bounded-darg-listp (mv-nth 1 (merge-terms-into-dag-array-simple
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
                  ;;     *max-1d-array-length*)
                  ))
    :flag merge-terms-into-dag-array-simple)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-term-into-dag-array-simple merge-terms-into-dag-array-simple car-becomes-nth-of-0)
                           (natp dargp pseudo-term-listp)))))

;; avoids bound from dargp-less-than
(defthm dargp-of-mv-nth-1-of-merge-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type dargp))))

;; generalizes the bound
(defthm dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-simple
  (implies (and (<= (mv-nth 3 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                    bound)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (dargp-less-than (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                            bound))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type))))

;drop?
(defthm merge-term-into-dag-array-simple-return-type-corollary4
  (implies (and (not (consp (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))) ; not a quotep
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (natp (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type
                               dargp-of-mv-nth-1-of-merge-term-into-dag-array-simple
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-simple))))

;generalizes the bound
(defthm merge-term-into-dag-array-simple-return-type-corollary
  (implies (and (<= bound dag-len)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (<= bound
               (mv-nth 3 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type))))

(defthm merge-term-into-dag-array-simple-return-type-linear
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (<= dag-len
               (mv-nth 3 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :rule-classes :linear
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type))))

;; the nodenum returned is less than the final dag length
;do we need this variant?
(defthm merge-term-into-dag-array-simple-return-type-corollary3
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                ;; did not return a constant:
                (not (consp (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
                )
           (< (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
              (mv-nth 3 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
           :in-theory (disable merge-term-into-dag-array-simple-return-type
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-simple
                               merge-term-into-dag-array-simple-return-type-corollary))))

;generalizes the bound
(defthm merge-term-into-dag-array-simple-return-type-corollary3-gen
  (implies (and (<= (mv-nth 3 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
                    bound)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
                (not (consp (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
                )
           (< (mv-nth 1 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
              bound))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type-corollary3)
           :in-theory (disable merge-term-into-dag-array-simple-return-type-corollary3))))

(verify-guards merge-term-into-dag-array-simple
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-term-into-dag-array-simple merge-terms-into-dag-array-simple car-becomes-nth-of-0
                                                      not-equal-of-len-and-1-when-dargp
                                                      <-of-nth-when-bounded-darg-listp
                                                      true-listp-of-nth-1-of-nth-0-when-pseudo-termp
                                                      ALL-MYQUOTEP-WHEN-DARG-LISTP)
                           (natp dargp pseudo-term-listp)))))

;; ;; how does this differ from the return type theorem?
;; (defthm wf-dagp-of-merge-term-into-dag-array-simple
;;   (implies (and (pseudo-termp term)
;;                 (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
;;                 (symbol-alistp var-replacement-alist)
;;                 (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
;;                 ;;no error:
;;                 (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
;;            (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;              (merge-term-into-dag-array-simple
;;               term
;;               var-replacement-alist
;;               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
;;               )
;;              (declare (ignore erp nodenum-or-quotep))
;;              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
;;   :hints (("Goal" :use (:instance merge-term-into-dag-array-simple-return-type)
;;            :in-theory (disable merge-term-into-dag-array-simple-return-type))))

;; (defthm wf-dagp-of-merge-terms-into-dag-array-simple
;;   (implies (and (pseudo-term-listp terms)
;;                 (true-listp terms)
;;                 (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
;;                 (symbol-alistp var-replacement-alist)
;;                 (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
;;                 (not (mv-nth 0 (merge-terms-into-dag-array-simple
;;                                 terms
;;                                 var-replacement-alist
;;                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
;;                                 ))))
;;            (mv-let (erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
;;              (merge-terms-into-dag-array-simple
;;               terms
;;               var-replacement-alist
;;               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
;;               )
;;              (declare (ignore erp nodenums-or-quoteps))
;;              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
;;   :hints (("Goal" :use (:instance merge-terms-into-dag-array-simple-return-type)
;;            :in-theory (disable merge-terms-into-dag-array-simple-return-type))))

(defthm pseudo-dag-arrayp-of-merge-term-into-dag-array-simple
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no error:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
             (declare (ignore erp nodenum-or-quotep new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (pseudo-dag-arrayp dag-array-name new-dag-array new-dag-len)))
  :hints (("Goal" :use merge-term-into-dag-array-simple-return-type
           :in-theory (e/d (wf-dagp) (merge-term-into-dag-array-simple-return-type
                                      ;wf-dagp-of-merge-term-into-dag-array-simple
                                      )))))

(defthm pseudo-dag-arrayp-of-merge-term-into-dag-array-simple-gen
  (implies (and (natp n)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no error:
                (not (mv-nth 0 (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))))
           (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
             (merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
             (declare (ignore erp nodenum-or-quotep new-dag-parent-array new-dag-constant-alist new-dag-variable-alist))
             (implies (<= n new-dag-len)
                      (pseudo-dag-arrayp dag-array-name new-dag-array n))))
  :hints (("Goal" :use (pseudo-dag-arrayp-of-merge-term-into-dag-array-simple)
           :in-theory (disable pseudo-dag-arrayp-of-merge-term-into-dag-array-simple))))

(defthm pseudo-dag-arrayp-of-merge-terms-into-dag-array-simple
  (implies (and (pseudo-term-listp terms)
                (true-listp terms)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
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
             (declare (ignore erp nodenums-or-quoteps dag-parent-array dag-constant-alist dag-variable-alist))
             (pseudo-dag-arrayp dag-array-name dag-array dag-len)))
  :hints (("Goal" :use merge-terms-into-dag-array-simple-return-type
           :in-theory (disable merge-terms-into-dag-array-simple-return-type ;wf-dagp-of-merge-terms-into-dag-array-simple
                               merge-terms-into-dag-array-simple-return-type))))

(defthm alen1-of-of-merge-terms-into-dag-array-simple-parent-array
  (implies (and (pseudo-term-listp terms)
                (true-listp terms)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
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
             (declare (ignore erp nodenums-or-quoteps dag-len dag-constant-alist dag-variable-alist))
             (equal (alen1 dag-parent-array-name dag-parent-array)
                    (alen1 dag-array-name dag-array))))
  :hints (("Goal" :use merge-terms-into-dag-array-simple-return-type
           :in-theory (disable ;wf-dagp-of-merge-terms-into-dag-array-simple
                               merge-terms-into-dag-array-simple-return-type))))

(defthm bounded-dag-parent-arrayp-of-merge-terms-into-dag-array-simple
  (implies (and (pseudo-term-listp terms)
                (true-listp terms)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
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
             (declare (ignore erp nodenums-or-quoteps dag-array dag-constant-alist dag-variable-alist))
             (bounded-dag-parent-arrayp dag-parent-array-name dag-parent-array dag-len)))
  :hints (("Goal" :use merge-terms-into-dag-array-simple-return-type
           :in-theory (disable ;wf-dagp-of-merge-terms-into-dag-array-simple
                               merge-terms-into-dag-array-simple-return-type))))

(defthm-flag-merge-term-into-dag-array-simple
  (defthm true-listp-of-mv-nth-1-of-merge-terms-into-dag-array-simple-dummy
    :skip t
    :flag merge-term-into-dag-array-simple)
  (defthm true-listp-of-mv-nth-1-of-merge-terms-into-dag-array-simple
    (true-listp (mv-nth 1 (merge-terms-into-dag-array-simple terms var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))
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
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
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
    :skip t
    :flag merge-terms-into-dag-array-simple)
  :hints (("Goal" :in-theory (e/d ( ;merge-term-into-dag-array-simple
                                   merge-terms-into-dag-array-simple
                                   consp-of-lookup-equal-when-all-myquotep-of-strip-cdrs)
                                  (natp))
           :expand ((merge-term-into-dag-array-simple term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)
                    (merge-term-into-dag-array-simple term var-replacement-alist dag-array 0 dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; compare to compose-term-and-dag
;; This one replaces vars in term using var-replacement-alist.
;; Returns (mv erp dag-or-quotep).
;; If dag-or-quotep is a quotep, it essentially gets ignored as there are no nodes for the var-replacement-alist to mention.
;; Smashes the arrays 'dag-array and 'dag-parent-array.
(defund merge-term-into-dag-simple (term
                                    var-replacement-alist ; maps vars in TERM to quoteps or nodenums in DAG-ARRAY
                                    dag-or-quotep)
  (declare (xargs :guard (and (pseudo-termp term)
                              (or (myquotep dag-or-quotep)
                                  (and (pseudo-dagp dag-or-quotep)
                                       (<= (len dag-or-quotep) *max-1d-array-length*)))
                              (symbol-alistp var-replacement-alist)
                              (if (myquotep dag-or-quotep)
                                  (bounded-darg-listp (strip-cdrs var-replacement-alist) 0) ; simplify: they must all be constants
                                (bounded-darg-listp (strip-cdrs var-replacement-alist) (len dag-or-quotep))))
                  :guard-hints (("Goal" :in-theory (e/d (<-of-+-of-1-when-integers
                                                         empty-dag-array ;todo
                                                         )
                                                        (natp))))))
  (b* ((dag-array-name 'dag-array)               ; could pass in
       (dag-parent-array-name 'dag-parent-array) ; could pass in
       (slack-amount 100) ; could count the expressions in the term
       ((mv dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (if (myquotep dag-or-quotep)
            ;; No DAG yet, so we have to make one:
            (empty-dag-array slack-amount)
          (b* ((dag-len (len dag-or-quotep))
               (dag-array (make-dag-into-array dag-array-name dag-or-quotep slack-amount))
               ((mv dag-parent-array dag-constant-alist dag-variable-alist)
                (make-dag-indices dag-array-name dag-array dag-parent-array-name dag-len)))
            (mv dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
       ((mv erp nodenum-or-quotep dag-array & & & &)
        (merge-term-into-dag-array-simple term
                                          var-replacement-alist
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name))
       ((when erp) (mv erp dag-or-quotep)) ; just pass it back unchanged in the error case
       ((when (consp nodenum-or-quotep)) ; test for quotep
        (mv (erp-nil) nodenum-or-quotep))
       (dag (drop-non-supporters-array-with-name dag-array-name dag-array nodenum-or-quotep nil)))
    (mv (erp-nil) dag)))

(defthm merge-term-into-dag-simple-return-type
  (implies (and (not (mv-nth 0 (merge-term-into-dag-simple term var-replacement-alist dag-or-quotep))) ; no error
                (not (quotep (mv-nth 1 (merge-term-into-dag-simple term var-replacement-alist dag-or-quotep)))) ; we got a dag back
                (pseudo-termp term)
                (or (myquotep dag-or-quotep)
                    (and (pseudo-dagp dag-or-quotep)
                         (<= (len dag-or-quotep) *max-1d-array-length*)))
                (symbol-alistp var-replacement-alist)
                (if (myquotep dag-or-quotep)
                    (bounded-darg-listp (strip-cdrs var-replacement-alist) 0) ; simplify: they must all be constants
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) (len dag-or-quotep))))
           (and (pseudo-dagp (mv-nth 1 (merge-term-into-dag-simple term var-replacement-alist dag-or-quotep)))
                (<= (car (car (mv-nth 1 (merge-term-into-dag-simple term var-replacement-alist dag-or-quotep))))
                    *max-1d-array-index*)))
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-simple <-of-+-of-1-when-integers equal-of-quote-when-dargp) (natp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp dag-or-quotep).
(defund wrap-term-around-dag (term var dag-or-quotep)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp var)
                              (or (myquotep dag-or-quotep)
                                  (and (pseudo-dagp dag-or-quotep)
                                       (<= (len dag-or-quotep) *max-1d-array-length*))))
                  :guard-hints (("Goal" :in-theory (enable strip-cdrs
                                                           symbol-alistp
                                                           car-of-car-when-pseudo-dagp)))))
  (merge-term-into-dag-simple term
                              (acons var (if (myquotep dag-or-quotep) dag-or-quotep (top-nodenum dag-or-quotep)) nil)
                              dag-or-quotep))

(defthm wrap-term-around-dag-return-type
  (implies (and (not (quotep (mv-nth 1 (wrap-term-around-dag term var dag-or-quotep)))) ; not a constant
                (pseudo-termp term)
                (symbolp var)
                (or (myquotep dag-or-quotep)
                    (and (pseudo-dagp dag-or-quotep)
                         (<= (len dag-or-quotep) *max-1d-array-length*)))
                (not (mv-nth 0 (wrap-term-around-dag term var dag-or-quotep))) ; no error (drop?)
                )
           (pseudo-dagp (mv-nth 1 (wrap-term-around-dag term var dag-or-quotep))))
  :hints (("Goal" :in-theory (enable wrap-term-around-dag))))

(defthm wrap-term-around-dag-return-type-linear
  (implies (and (not (quotep (mv-nth 1 (wrap-term-around-dag term var dag-or-quotep)))) ; not a constant
                (pseudo-termp term)
                (symbolp var)
                (or (myquotep dag-or-quotep)
                    (and (pseudo-dagp dag-or-quotep)
                         (<= (len dag-or-quotep) *max-1d-array-length*)))
                (not (mv-nth 0 (wrap-term-around-dag term var dag-or-quotep))) ; no error (drop?)
                )
           (<= (car (car (mv-nth 1 (wrap-term-around-dag term var dag-or-quotep))))
               *max-1d-array-index*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable wrap-term-around-dag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Returns the new dag-or-quotep.  This version does not return an erp.
;; (defund wrap-term-around-dag! (term var dag-or-quotep)
;;   (mv-let (erp dag-or-quotep)
;;     (wrap-term-around-dag term var dag-or-quotep)
;;     (if erp
;;         (prog2$ (er hard? 'wrap-term-around-dag! "Error wrapping term around dag: ~x0." erp)
;;                 *nil* ; just return some constant
;;                 )
;;       dag-or-quotep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Ensures that VAR is a free var of TERM and that TERM contains no free vars except VAR and the EXTRA-VARS.
;; Returns (mv erp dag-or-quotep).
;; Similar to compose-term-and-dag-safe.
(defund wrap-term-around-dag-safe (term var dag-or-quotep extra-vars)
  (declare (xargs :guard (and (pseudo-termp term)
                              (symbolp var)
                              (or (myquotep dag-or-quotep)
                                  (and (pseudo-dagp dag-or-quotep)
                                       (<= (len dag-or-quotep) *max-1d-array-length*)))
                              (symbol-listp extra-vars))))
  (let ((term-vars (all-vars term)))
    (if (not (member-eq var term-vars))
        (prog2$ (er hard? 'wrap-term-around-dag-safe "Var to be replaced, ~x0, is not among the vars in the term ~x1." var term)
                (mv (erp-t) dag-or-quotep))
      (let ((expected-vars (cons var extra-vars)))
        (if (not (subsetp-eq term-vars expected-vars))
            (prog2$ (er hard? 'wrap-term-around-dag-safe "Term ~x0 contains unexpected vars ~x1." term (set-difference-eq term-vars expected-vars))
                    (mv (erp-t) dag-or-quotep))
          (wrap-term-around-dag term var dag-or-quotep))))))

(defthm wrap-term-around-dag-safe-return-type
  (implies (and (not (quotep (mv-nth 1 (wrap-term-around-dag-safe term var dag-or-quotep extra-vars)))) ; not a constant
                (pseudo-termp term)
                (symbolp var)
                (or (myquotep dag-or-quotep)
                    (and (pseudo-dagp dag-or-quotep)
                         (<= (len dag-or-quotep) *max-1d-array-length*)))
                (not (mv-nth 0 (wrap-term-around-dag-safe term var dag-or-quotep extra-vars))) ; no error (drop?)
                )
           (pseudo-dagp (mv-nth 1 (wrap-term-around-dag-safe term var dag-or-quotep extra-vars))))
  :hints (("Goal" :in-theory (enable wrap-term-around-dag-safe))))

(defthm wrap-term-around-dag-safe-return-type-linear
  (implies (and (not (quotep (mv-nth 1 (wrap-term-around-dag-safe term var dag-or-quotep extra-vars)))) ; not a constant
                (pseudo-termp term)
                (symbolp var)
                (or (myquotep dag-or-quotep)
                    (and (pseudo-dagp dag-or-quotep)
                         (<= (len dag-or-quotep) *max-1d-array-length*)))
                (not (mv-nth 0 (wrap-term-around-dag-safe term var dag-or-quotep extra-vars))) ; no error (drop?)
                )
           (<= (car (car (mv-nth 1 (wrap-term-around-dag-safe term var dag-or-quotep extra-vars))))
               *max-1d-array-index*))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (wrap-term-around-dag-safe) (myquotep)))))
