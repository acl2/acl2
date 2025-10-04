; Utilities to merge terms into dags (and to convert terms into dags).
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

;; This version uses the basic evaluator to evaluate ground terms.
;; This version does attempt to resolve IFs.
;; This version does not handle embedded dags.

;; See also merge-term-into-dag-array.
;; See also merge-term-into-dag-array-simple.lisp.

;; TODO: Add support for BOOLIF, BVIF, and BV-ARRAY-IF.

(include-book "dag-array-builders2")
(include-book "kestrel/typed-lists-light/all-consp" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "evaluator-basic")
(include-book "tools/flag" :dir :system)
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
(local (include-book "kestrel/alists-light/lookup-equal" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

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

(defthmd true-listp-of-nth-1-of-nth-0-when-pseudo-termp
  (implies (and (pseudo-termp term)
                ;; (consp (nth 0 term))
                )
           (true-listp (nth 1 (nth 0 term))))
  :hints (("Goal" :expand (pseudo-termp term)
           :cases ((consp (nth 0 term)))
           :in-theory (enable pseudo-termp nth-of-0
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

;; TODO: Consider handling other versions of IF top-down.
;; TODO: Include subst in the name since this also substitutes for vars.
(mutual-recursion
 ;; This one can replace vars in term using var-replacement-alist (helps us deal with lambdas).
 ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
 ;; where nodenum-or-quotep is equivalent to the term passed in, and nodes already in the dag remain unchanged (and the aux. data structures have been updated, of course)
 (defund merge-term-into-dag-array-basic (term
                                          var-replacement-alist ; maps vars in TERM to quoteps or nodenums in DAG-ARRAY
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                          interpreted-function-alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (symbol-alistp var-replacement-alist)
                               (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                               (interpreted-function-alistp interpreted-function-alist))
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
           (if (and (eq 'if fn) ; todo: handle other IFs?
                    ;; ensure there are enough args:
                    (consp (cdr (cdr args))))
               (mv-let (erp test-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 (merge-term-into-dag-array-basic (first args) var-replacement-alist
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist)
                 (if erp
                     (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                   (if (consp test-nodenum-or-quotep) ;tests for quotep
                       ;;the test was resolved:
                       (merge-term-into-dag-array-basic (if (unquote test-nodenum-or-quotep) (second args) (third args)) var-replacement-alist
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                        interpreted-function-alist)
                     ;;could not resolve the test:
                     (mv-let (erp then-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                       (merge-term-into-dag-array-basic (second args) var-replacement-alist
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                        interpreted-function-alist)
                       (if erp
                           (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                         (mv-let (erp else-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                           (merge-term-into-dag-array-basic (third args) var-replacement-alist
                                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                            interpreted-function-alist)
                           (if erp
                               (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                             ;;treat it like a normal function call (we know it's not a ground term because the if-test is not a constant)
                             (progn$ ;(cw "Adding (~x0 : ~x1).~%" fn arg-nodenums-or-quoteps)
                              (add-function-call-expr-to-dag-array-with-name fn (list test-nodenum-or-quotep then-nodenum-or-quotep else-nodenum-or-quotep)
                                                                             dag-array dag-len dag-parent-array
                                                                             dag-constant-alist dag-variable-alist
                                                                             dag-array-name dag-parent-array-name)))))))))
             ;;begin by adding the args to the dag: (expensive to cons this up, if they are ground terms?)
             (mv-let
               (erp arg-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               (merge-terms-into-dag-array-basic args var-replacement-alist
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                 interpreted-function-alist)
               (if erp
                   (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 (if (consp fn) ;tests for ((lambda <formals> <body>) ...<actuals>...) ;move this case up?
                     (let* ((formals (lambda-formals fn))
                            (body (lambda-body fn)))
                       (merge-term-into-dag-array-basic body
                                                        (pairlis$-fast formals arg-nodenums-or-quoteps) ;save this consing?
                                                        dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                        interpreted-function-alist))
                   ;; normal function call:
                   (if (not (all-consp arg-nodenums-or-quoteps)) ;; test for args being quoted constants
                       ;; it's not a ground term, so just add it to the dag:
                       (add-function-call-expr-to-dag-array-with-name fn arg-nodenums-or-quoteps
                                                                      dag-array dag-len dag-parent-array
                                                                      dag-constant-alist dag-variable-alist
                                                                      dag-array-name dag-parent-array-name)
                     ;; it's a ground term:
                     (b* (((mv erp val)
                           (apply-axe-evaluator-basic-to-quoted-args fn arg-nodenums-or-quoteps interpreted-function-alist))
                          ((when erp)
                           (if (call-of :unknown-function erp)
                               ;;no error, but could not evaluate (todo: print a warning?)
                               (add-function-call-expr-to-dag-array-with-name fn arg-nodenums-or-quoteps
                                                                              dag-array dag-len dag-parent-array
                                                                              dag-constant-alist dag-variable-alist
                                                                              dag-array-name dag-parent-array-name)
                             ;; anything else non-nil is a true error:
                             (mv (erp-t) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))
                       ;; no error evaluating:
                       (mv (erp-nil) (enquote val) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))))))))))))

 ;; Returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist), where nodenums-or-quoteps are equivalent to the terms passed in.
 ;; TODO: Consider using a changep flag to avoid reconsing the list?
 (defund merge-terms-into-dag-array-basic (terms
                                           var-replacement-alist
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                           interpreted-function-alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (true-listp terms)
                               (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (symbol-alistp var-replacement-alist)
                               (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                               (interpreted-function-alistp interpreted-function-alist))))
   (if (endp terms)
       (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
     (b* (((mv erp car-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-term-into-dag-array-basic (first terms) var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
          ((mv erp cdr-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-terms-into-dag-array-basic (rest terms) var-replacement-alist
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                       interpreted-function-alist))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
       (mv (erp-nil)
           (cons car-nodenum-or-quotep cdr-nodenums-or-quoteps)
           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))

(make-flag merge-term-into-dag-array-basic)

(defthm-flag-merge-term-into-dag-array-basic
  (defthm natp-of-mv-nth-3-of-merge-term-into-dag-array-basic
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-term-into-dag-array-basic
                              term var-replacement-alist dag-array dag-len dag-parent-array
                              dag-constant-alist dag-variable-alist
                              dag-array-name dag-parent-array-name
                              interpreted-function-alist))))
    :flag merge-term-into-dag-array-basic)
  (defthm natp-of-mv-nth-3-of-merge-terms-into-dag-array-basic
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-terms-into-dag-array-basic
                              terms var-replacement-alist
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                              interpreted-function-alist))))
    :flag merge-terms-into-dag-array-basic)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array-basic merge-terms-into-dag-array-basic) (natp)))))

;; (defthm-flag-merge-term-into-dag-array-basic
;;   (defthm integerp-of-mv-nth-3-of-merge-term-into-dag-array-basic
;;     (implies (integerp dag-len)
;;              (integerp (mv-nth 3 (merge-term-into-dag-array-basic
;;                               term var-replacement-alist dag-array dag-len dag-parent-array
;;                               dag-constant-alist dag-variable-alist
;;                               dag-array-name dag-parent-array-name
;;                               interpreted-function-alist))))
;;     :flag merge-term-into-dag-array-basic)
;;   (defthm integerp-of-mv-nth-3-of-merge-terms-into-dag-array-basic
;;     (implies (integerp dag-len)
;;              (integerp (mv-nth 3 (merge-terms-into-dag-array-basic
;;                               terms var-replacement-alist
;;                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
;;                               interpreted-function-alist))))
;;     :flag merge-terms-into-dag-array-basic)
;;   :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array-basic merge-terms-into-dag-array-basic) (natp)))))

(defthm-flag-merge-term-into-dag-array-basic
  (defthm dag-variable-alistp-of-mv-nth-6-of-merge-term-into-dag-array-basic
    (implies (and (pseudo-termp term)
                  (dag-variable-alistp dag-variable-alist)
                  (natp dag-len))
             (dag-variable-alistp (mv-nth 6 (merge-term-into-dag-array-basic
                                             term var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist))))
    :flag merge-term-into-dag-array-basic)
  (defthm dag-variable-alistp-of-mv-nth-6-of-merge-terms-into-dag-array-basic
    (implies (and (pseudo-term-listp terms)
                  (dag-variable-alistp dag-variable-alist)
                  (natp dag-len))
             (dag-variable-alistp (mv-nth 6 (merge-terms-into-dag-array-basic
                                             terms var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist))))
    :flag merge-terms-into-dag-array-basic)
  :hints (("Goal" :in-theory (enable merge-term-into-dag-array-basic merge-terms-into-dag-array-basic))))

(defthm-flag-merge-term-into-dag-array-basic
  (defthm merge-term-into-dag-array-basic-return-type
    (implies (and (pseudo-termp term)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
             (and (dargp-less-than (mv-nth 1 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))
                                   (mv-nth 3 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                  (wf-dagp dag-array-name
                           (mv-nth 2 (merge-term-into-dag-array-basic
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 3 (merge-term-into-dag-array-basic
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           dag-parent-array-name
                           (mv-nth 4 (merge-term-into-dag-array-basic
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 5 (merge-term-into-dag-array-basic
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 6 (merge-term-into-dag-array-basic
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist)))
                  (<= dag-len
                      (mv-nth 3 (merge-term-into-dag-array-basic
                                 term
                                 var-replacement-alist
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 interpreted-function-alist)))
                  ;; (<= (mv-nth 3 (merge-term-into-dag-array-basic
                  ;;                term
                  ;;                var-replacement-alist
                  ;;                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                  ;;                interpreted-function-alist))
                  ;;     *max-1d-array-length*)

                  ))
    :flag merge-term-into-dag-array-basic)
  (defthm merge-terms-into-dag-array-basic-return-type
    (implies (and (pseudo-term-listp terms)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-terms-into-dag-array-basic terms var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
             (and (true-listp (mv-nth 1 (merge-terms-into-dag-array-basic
                                         terms
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                         interpreted-function-alist)))
                  (equal (len (mv-nth 1 (merge-terms-into-dag-array-basic
                                         terms
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                         interpreted-function-alist)))
                         (len terms))
                  (darg-listp (mv-nth 1 (merge-terms-into-dag-array-basic
                                                   terms
                                                   var-replacement-alist
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                   interpreted-function-alist)))
                  (bounded-darg-listp (mv-nth 1 (merge-terms-into-dag-array-basic
                                                             terms
                                                             var-replacement-alist
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                             interpreted-function-alist))
                                                  (mv-nth 3 (merge-terms-into-dag-array-basic
                                                             terms
                                                             var-replacement-alist
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                             interpreted-function-alist)))
                  (wf-dagp dag-array-name
                           (mv-nth 2 (merge-terms-into-dag-array-basic
                                      terms
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 3 (merge-terms-into-dag-array-basic
                                      terms
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           dag-parent-array-name
                           (mv-nth 4 (merge-terms-into-dag-array-basic
                                      terms
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 5 (merge-terms-into-dag-array-basic
                                      terms
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 6 (merge-terms-into-dag-array-basic
                                      terms
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist)))
                  (<= dag-len
                      (mv-nth 3 (merge-terms-into-dag-array-basic
                                 terms
                                 var-replacement-alist
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 interpreted-function-alist)))
                  ;; (<= (mv-nth 3 (merge-terms-into-dag-array-basic
                  ;;                terms
                  ;;                var-replacement-alist
                  ;;                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                  ;;                interpreted-function-alist))
                  ;;     *max-1d-array-length*)
                  ))
    :flag merge-terms-into-dag-array-basic)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-term-into-dag-array-basic merge-terms-into-dag-array-basic car-becomes-nth-of-0)
                           (natp dargp pseudo-term-listp pseudo-termp)))))

(defthm merge-term-into-dag-array-basic-return-type-corollary
  (implies (and (<= bound dag-len)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (<= bound
               (mv-nth 3 (merge-term-into-dag-array-basic
                          term
                          var-replacement-alist
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                          interpreted-function-alist))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type)
           :in-theory (disable merge-term-into-dag-array-basic-return-type))))

(defthm merge-term-into-dag-array-basic-return-type-linear
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (<= dag-len
               (mv-nth 3 (merge-term-into-dag-array-basic
                          term
                          var-replacement-alist
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                          interpreted-function-alist))))
  :rule-classes :linear
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type)
           :in-theory (disable merge-term-into-dag-array-basic-return-type))))

(defthm mv-nth-3-of-merge-term-into-dag-array-basic-bound-linear
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (<= (mv-nth 3 (merge-term-into-dag-array-basic
                          term
                          var-replacement-alist
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                          interpreted-function-alist))
               *max-1d-array-length*))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type)
           :in-theory (e/d (wf-dagp) (merge-term-into-dag-array-basic-return-type)))))

(defthm dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-basic
  (implies (and (<= (mv-nth 3 (merge-term-into-dag-array-basic
                               term
                               var-replacement-alist
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                               interpreted-function-alist))
                    bound)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (DARGP-LESS-THAN
            (mv-nth 1 (merge-term-into-dag-array-basic
                       term
                       var-replacement-alist
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                       interpreted-function-alist))
            bound))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type)
           :in-theory (disable merge-term-into-dag-array-basic-return-type))))

(defthm dargp-of-mv-nth-1-of-merge-term-into-dag-array-basic
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (dargp (mv-nth 1 (merge-term-into-dag-array-basic
                             term
                             var-replacement-alist
                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                             interpreted-function-alist))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type)
           :in-theory (disable merge-term-into-dag-array-basic-return-type
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-basic
                               dargp))))

(defthm merge-term-into-dag-array-basic-return-type-corollary3
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (not (consp (mv-nth 1 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
                )
           (< (mv-nth 1 (merge-term-into-dag-array-basic
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         interpreted-function-alist))
              (mv-nth 3 (merge-term-into-dag-array-basic
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         interpreted-function-alist))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type)
           :in-theory (disable merge-term-into-dag-array-basic-return-type
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-basic
                               MERGE-TERM-INTO-DAG-ARRAY-BASIC-RETURN-TYPE-COROLLARY))))

(defthm merge-term-into-dag-array-basic-return-type-corollary3-gen
  (implies (and (<= (mv-nth 3 (merge-term-into-dag-array-basic
                               term
                               var-replacement-alist
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                               interpreted-function-alist))
                    bound)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (not (consp (mv-nth 1 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
                )
           (< (mv-nth 1 (merge-term-into-dag-array-basic
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         interpreted-function-alist))
              bound))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type-corollary3)
           :in-theory (disable merge-term-into-dag-array-basic-return-type-corollary3))))


(defthm merge-term-into-dag-array-basic-return-type-corollary6
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (not (consp (mv-nth 1 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
                )
           (< (mv-nth 1 (merge-term-into-dag-array-basic
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         interpreted-function-alist))
              *max-1d-array-length*))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type-corollary3-gen
                                  (bound *max-1d-array-length*)
                                  )
           :in-theory (disable merge-term-into-dag-array-basic-return-type
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-basic
                               MERGE-TERM-INTO-DAG-ARRAY-BASIC-RETURN-TYPE-COROLLARY
                               merge-term-into-dag-array-basic-return-type-corollary3-gen))))

;use consp as the normal form
(defthm merge-term-into-dag-array-basic-return-type-corollary4
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (equal (natp (mv-nth 1 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                  (not (consp (mv-nth 1 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type)
           :in-theory (disable merge-term-into-dag-array-basic-return-type
                               dargp-of-mv-nth-1-of-merge-term-into-dag-array-basic
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-basic))))

;use consp as the normal form
(defthm merge-term-into-dag-array-basic-return-type-corollary4b
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (equal (integerp (mv-nth 1 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                  (not (consp (mv-nth 1 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type)
           :in-theory (disable merge-term-into-dag-array-basic-return-type
                               dargp-of-mv-nth-1-of-merge-term-into-dag-array-basic
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-basic))))

(defthm merge-term-into-dag-array-basic-return-type-corollary5
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
           ;     (not (consp (mv-nth 1 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
                )
           (<= 0 (mv-nth 1 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type)
           :in-theory (disable merge-term-into-dag-array-basic-return-type
                               dargp-of-mv-nth-1-of-merge-term-into-dag-array-basic
                               dargp-less-than-of-mv-nth-1-of-merge-term-into-dag-array-basic))))

(verify-guards merge-term-into-dag-array-basic
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-term-into-dag-array-basic merge-terms-into-dag-array-basic car-becomes-nth-of-0
                                                      not-equal-of-len-and-1-when-dargp
                                                      <-of-nth-when-bounded-darg-listp
                                                      true-listp-of-nth-1-of-nth-0-when-pseudo-termp
                                                      ALL-MYQUOTEP-WHEN-DARG-LISTP)
                           (natp dargp pseudo-term-listp pseudo-termp)))))

(defthm wf-dagp-of-merge-term-into-dag-array-basic
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no error:
                (not (mv-nth 0 (merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (mv-let (erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (merge-term-into-dag-array-basic
              term
              var-replacement-alist
              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
              interpreted-function-alist)
             (declare (ignore erp nodenum-or-quotep))
             (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-basic-return-type)
           :in-theory (disable merge-term-into-dag-array-basic-return-type))))

(defthm wf-dagp-of-merge-terms-into-dag-array-basic
  (implies (and (pseudo-term-listp terms)
                (true-listp terms)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                (interpreted-function-alistp interpreted-function-alist)
                (not (mv-nth 0 (merge-terms-into-dag-array-basic
                                terms
                                var-replacement-alist
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                interpreted-function-alist))))
           (mv-let (erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (merge-terms-into-dag-array-basic
              terms
              var-replacement-alist
              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
              interpreted-function-alist)
             (declare (ignore erp nodenums-or-quoteps))
             (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)))
  :hints (("Goal" :use (:instance merge-terms-into-dag-array-basic-return-type)
           :in-theory (disable merge-terms-into-dag-array-basic-return-type))))

(defthm merge-terms-into-dag-array-basic-return-type-linear
    (implies (and (pseudo-term-listp terms)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-terms-into-dag-array-basic terms var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
             (<= dag-len
                      (mv-nth 3 (merge-terms-into-dag-array-basic
                                 terms
                                 var-replacement-alist
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 interpreted-function-alist))))
  :rule-classes :linear
  :hints (("Goal" :use merge-terms-into-dag-array-basic-return-type
           :in-theory (disable merge-terms-into-dag-array-basic-return-type))))

(defthm pseudo-dag-arrayp-after-merge-terms-into-dag-array-basic
  (implies (and (pseudo-term-listp terms)
                (true-listp terms)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                (interpreted-function-alistp interpreted-function-alist)
                (not (mv-nth 0 (merge-terms-into-dag-array-basic
                                terms
                                var-replacement-alist
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                interpreted-function-alist))))
           (mv-let (erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (merge-terms-into-dag-array-basic
              terms
              var-replacement-alist
              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
              interpreted-function-alist)
             (declare (ignore erp nodenums-or-quoteps dag-parent-array dag-constant-alist dag-variable-alist))
             (pseudo-dag-arrayp dag-array-name dag-array dag-len)))
  :hints (("Goal" :use (:instance wf-dagp-of-merge-terms-into-dag-array-basic)
           :in-theory (disable WF-DAGP-OF-MERGE-TERMS-INTO-DAG-ARRAY-BASIC
                               merge-terms-into-dag-array-basic-return-type))))

(defthm-flag-merge-term-into-dag-array-basic
  (defthm true-listp-of-mv-nth-1-of-merge-terms-into-dag-array-basic-dummy
    t
    :rule-classes nil
    :flag merge-term-into-dag-array-basic)
  (defthm true-listp-of-mv-nth-1-of-merge-terms-into-dag-array-basic
    (true-listp (mv-nth 1 (merge-terms-into-dag-array-basic
                           terms var-replacement-alist
                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                           interpreted-function-alist)))
    :rule-classes :type-prescription
    :flag merge-terms-into-dag-array-basic)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array-basic merge-terms-into-dag-array-basic) (natp)))))

;; handle the case of a lambda whose body is a var
(defthm-flag-merge-term-into-dag-array-basic
  (defthm posp-of-mv-nth-3-of-merge-term-into-dag-array-basic
    (implies (and (natp dag-len)
                  (pseudo-termp term)
                  ;;(not (variablep term)) ;note this
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                  (interpreted-function-alistp interpreted-function-alist)
                  ;; no error:
                  (not (mv-nth 0 (merge-term-into-dag-array-basic
                                  term
                                  var-replacement-alist
                                  dag-array dag-len dag-parent-array
                                  dag-constant-alist dag-variable-alist
                                  dag-array-name dag-parent-array-name
                                  interpreted-function-alist)))
                  ;; returns a nodenum, not a quotep:
                  (not (consp (mv-nth 1 (merge-term-into-dag-array-basic
                                         term
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array
                                         dag-constant-alist dag-variable-alist
                                         dag-array-name dag-parent-array-name
                                         interpreted-function-alist)))))
             ;; the length can't be 0 after merging in the term
             (posp (mv-nth 3 (merge-term-into-dag-array-basic
                              term
                              var-replacement-alist
                              dag-array dag-len dag-parent-array
                              dag-constant-alist dag-variable-alist
                              dag-array-name dag-parent-array-name
                              interpreted-function-alist))))
    :flag merge-term-into-dag-array-basic)
  (defthm posp-of-mv-nth-3-of-merge-term-into-dag-array-basic-fake-helper
    t
    :rule-classes nil
    :flag merge-terms-into-dag-array-basic)
  :hints (("Goal" :in-theory (e/d (;merge-term-into-dag-array-basic
                                   merge-terms-into-dag-array-basic
                                   consp-of-lookup-equal-when-all-myquotep-of-strip-cdrs
                                   car-becomes-nth-of-0)
                                  (natp))
           :expand ((merge-term-into-dag-array-basic term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)
                    (merge-term-into-dag-array-basic term var-replacement-alist dag-array 0 dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))))
