; DAG builders that depend on the evaluator
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also simpler functions for making dags, such as
;; make-term-into-dag-simple and make-term-into-dag-basic.

(include-book "dagify0")
(include-book "evaluator") ; brings in skip-proofs (try the basic evaluator?)
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/utilities/pseudo-termp2" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars2" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system)) ;why does this break a proof below?
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
;(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
;(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
;(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))
;(local (include-book "kestrel/alists-light/lookup-equal" :dir :system))

;; (local (in-theory (disable member-equal
;;                            subsetp-equal
;;                            ;; axe-treep
;;                            axe-tree-listp
;;                            ;; for speed:
;;                            largest-non-quotep-bound
;;                            largest-non-quotep-bound-alt
;;                            myquotep
;;                            ;; mv-nth-of-if
;;                            symbol-alistp ;don't induct
;;                            )))

(local (in-theory (disable consp-from-len-cheap
                           axe-tree-listp-when-pseudo-term-listp
                           ;;list::nth-with-large-index-2
                           ;cdr-non-nil
                           ;nth1-when-not-cdr
                           ;list::nth-with-large-index
                           bounded-darg-listp-when-<-of-largest-non-quotep
                           dargp-less-than
                           dargp
                           default-cdr
                           default-car
                           ;weak-dagp-aux ;todo uncomment, but that breaks some proofs
                           symbol-alistp ;prevent induction
                           nat-listp ;for speed
                           pseudo-dag-arrayp
                           true-listp-of-nth-1-of-nth-0-when-axe-treep
                           ;CAR-OF-CAR-WHEN-PSEUDO-TERMP  ;; try
                           )))

;(local (in-theory (enable caadr-when-consecutivep-of-strip-cars)))

(local (in-theory (enable consp-of-cdr
                          bounded-renaming-entriesp-of-aset1-special-gen
                          <-of-lookup-equal-when-bounded-darg-listp-of-strip-cdrs)))

;dup
(local
  (defthm bounded-darg-listp-of-strip-cdrs-of-cdr
    (implies (bounded-darg-listp (strip-cdrs alist) bound)
             (bounded-darg-listp (strip-cdrs (cdr alist)) bound))))

;;use elsewhere?
(defund-inline evaluatable-fn-and-argsp (fn arg-nodenums-or-quoteps interpreted-function-alist)
  (declare (xargs :guard (and ;(symbolp fn)
                          (darg-listp arg-nodenums-or-quoteps)
                          (symbol-alistp interpreted-function-alist))))
  (and (all-consp arg-nodenums-or-quoteps) ;all args must be quoted constants
       (or (member-eq fn *axe-evaluator-functions*)
           (eq fn 'dag-val-with-axe-evaluator) ;fixme add to *axe-evaluator-functions*? or use a different list? fixme add the other generated fn names?
           (assoc-eq fn interpreted-function-alist))))

(defthm all-myquotep-when-evaluatable-fn-and-argsp
  (implies (and (evaluatable-fn-and-argsp fn arg-nodenums-or-quoteps interpreted-function-alist)
                (darg-listp arg-nodenums-or-quoteps))
           (all-myquotep arg-nodenums-or-quoteps))
  :hints (("Goal" :in-theory (enable evaluatable-fn-and-argsp all-myquotep-when-darg-listp))))

;todo: make local
(defthm alistp-of-set-difference-equal
  (implies (alistp x)
           (alistp (set-difference-equal x y))))

;;use elsewhere?
;; recoginize a suitable call of the form (dag-val-with-axe-evaluator dag alist interpreted-function-alist array-depth).
(defund-inline call-of-dag-val-with-axe-evaluator-with-inlineable-dagp (fn arg-nodenums-or-quoteps interpreted-function-alist)
  (declare (xargs :guard (and ;(symbolp fn)
                          (darg-listp arg-nodenums-or-quoteps)
                          (symbol-alistp interpreted-function-alist))
                  :guard-hints (("Goal" :in-theory (enable car-becomes-nth-of-0)))
                  ))
  (and (eq 'dag-val-with-axe-evaluator fn)
       (= 4 (len arg-nodenums-or-quoteps))
       ;; it's of the form: (dag-val-with-axe-evaluator DAG ALIST INTERPRETED-FUNCTION-ALIST ARRAY-DEPTH)
       (if (consp (first arg-nodenums-or-quoteps)) ;the dag to inline -- could it ever be the nodenum of a quotep?
           t
         (prog2$ (cw "(WARNING: Found a call to dag-val-with-axe-evaluator, but the dag isn't a quoted constant.)~%") ;print more?
                 nil))
       (not (consp (second arg-nodenums-or-quoteps)))  ;todo: handle the case of a constant alist? ;uncomment?
       (if (pseudo-dagp (unquote (first arg-nodenums-or-quoteps)))
           t
         (prog2$ (cw "(WARNING Found a call to dag-val-with-axe-evaluator, but the dag is ill-formed.)~%") ;print more?
                 nil))
       (<= (len (unquote (first arg-nodenums-or-quoteps))) *max-1d-array-length*)
       ;;the interpreted-function-alist for the embedded dag must be consistent with the one passed in: - or maybe the dag only includes built in fns?  what if its the nodenum of a quotep?
       (consp (third arg-nodenums-or-quoteps))
       (interpreted-function-alistp (unquote (third arg-nodenums-or-quoteps)))
       (if (subsetp-equal (unquote (third arg-nodenums-or-quoteps))
                          interpreted-function-alist)
           t
         (let ((difference (set-difference-equal (unquote (third arg-nodenums-or-quoteps)) interpreted-function-alist)))
           (prog2$ (cw "(WARNING: Found a call to dag-val-with-axe-evaluator, but the interpreted-function-alist isn't a subset of the one passed in.  Thus, we are not inlining.  Offending entries: ~x0.  Corresponding entries in alist: ~x1)~%"
                       difference ;(set-difference-eq (strip-cars (unquote (third arg-nodenums-or-quoteps))) (strip-cars interpreted-function-alist))
                       (lookup-eq-lst (strip-cars difference) interpreted-function-alist)
                       )
                   nil)))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-0
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (consp (nth 0 arg-nodenums-or-quoteps)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

;; (defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-0b
;;   (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
;;            (equal (len (nth 0 arg-nodenums-or-quoteps))
;;                   2))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-1
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (consp (cadr (first arg-nodenums-or-quoteps))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-2
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (weak-dagp-aux (cadr (first arg-nodenums-or-quoteps))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-3
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (equal (len arg-nodenums-or-quoteps) 4))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-4
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (not (consp (nth 1 arg-nodenums-or-quoteps))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp))))

;the bottom node of the embedded dag is 0
(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-5
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (equal (nth 0 (nth (+ -1 (len (nth 1 (nth 0 arg-nodenums-or-quoteps))))
                              (nth 1 (nth 0 arg-nodenums-or-quoteps))))
                  0))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp
                                     car-becomes-nth-of-0))))

;; top nodenum is a nat
(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-6
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (natp (nth 0 (nth 0 (nth 1 (nth 0 arg-nodenums-or-quoteps))))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp
                                     car-becomes-nth-of-0))))

;; top nodenum is bounded
(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-7
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (not (< *max-1d-array-index*
                   (nth 0 (nth 0 (nth 1 (nth 0 arg-nodenums-or-quoteps)))))))
  :rule-classes (:forward-chaining :linear)
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp
                                     car-becomes-nth-of-0))))

(defthm call-of-dag-val-with-axe-evaluator-with-inlineable-dag-forward-8
  (implies (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
           (pseudo-dagp (nth 1 (nth 0 arg-nodenums-or-quoteps))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable call-of-dag-val-with-axe-evaluator-with-inlineable-dagp
                                     car-becomes-nth-of-0))))

(defthm dargp-less-than-of-lookup-equal
  (implies (and (lookup-equal term var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist)
                                                dag-len))
           (dargp-less-than (lookup-equal term var-replacement-alist) dag-len))
  :hints (("Goal" :in-theory (enable lookup-equal))))

(defthm symbol-listp-of-cadr-of-car-when-pseudo-termp-cheap ;the ;lambda vars
  (implies (and (pseudo-termp term)
                (consp (car term)))
           (symbol-listp (cadr (car term))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move?
;; TODO: Consider handling other versions of IF top-down.
(mutual-recursion
 ;;This one replaces the vars in term using var-replacement-alist.
 ;;TERM is a tree over variables and quoteps (fixme and nodenums, currently - fixme)
 ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
 ;; where nodenum-or-quotep is equivalent to the term passed in, and nodes already in the dag passed in remain unchanged (and the aux. data structures have been updated, of course)
 (defund merge-term-into-dag-array (term
                                   var-replacement-alist ;maps all vars in TERM to quoteps or nodenums in dag-array
                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                   interpreted-function-alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (symbol-alistp var-replacement-alist)
                               (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                               (interpreted-function-alistp interpreted-function-alist))
                   :guard-hints (("Goal" :in-theory (disable merge-term-into-dag-array)))
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
           (if (eq 'if fn) ;fixme handle other IFs?
               (mv-let (erp test-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 (merge-term-into-dag-array (first args) var-replacement-alist
                                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                            interpreted-function-alist)
                 (if erp
                     (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                   (if (consp test-nodenum-or-quotep) ;tests for quotep
                       ;;the test was resolved:
                       (merge-term-into-dag-array (if (unquote test-nodenum-or-quotep) (second args) (third args)) var-replacement-alist
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist)
                     ;;could not resolve the test:
                     (mv-let (erp then-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                       (merge-term-into-dag-array (second args) var-replacement-alist
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist)
                       (if erp
                           (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                         (mv-let (erp else-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                           (merge-term-into-dag-array (third args) var-replacement-alist
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
               (merge-terms-into-dag-array args var-replacement-alist
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                           interpreted-function-alist)
               (if erp
                   (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                 ;;check for the special case of a call to dag-val-with-axe-evaluator where we can inline the dag:
                 (if (call-of-dag-val-with-axe-evaluator-with-inlineable-dagp fn arg-nodenums-or-quoteps interpreted-function-alist)
                     ;;term is a call of dag-val-with-axe-evaluator, and we can inline its embedded dag:
                     (b* ((quoted-dag (first arg-nodenums-or-quoteps))
                          (dag (unquote quoted-dag))
                          (vars (dag-vars dag))
                          (alist-nodenum (second arg-nodenums-or-quoteps)) ;todo: handle a constant alist
                          ((mv erp variable-node-alist-for-dag dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                           (make-nodes-for-vars-with-name vars alist-nodenum dag-array dag-len dag-parent-array
                                                          dag-constant-alist dag-variable-alist nil dag-array-name dag-parent-array-name))
                          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
                          ((mv erp renaming-array dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                           (merge-embedded-dag-into-dag-array (reverse-list dag)
                                                              variable-node-alist-for-dag
                                                              dag-array dag-len dag-parent-array
                                                              dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                              (make-empty-array 'renaming-array-for-merge-embedded-dag-into-dag-array (+ 1 (top-nodenum dag))) ; nil ;the translation-alist
                                                              interpreted-function-alist))
                          ;;fixme are the aux data structures updated right?
                          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
                       (mv (erp-nil)
                           (aref1 'renaming-array-for-merge-embedded-dag-into-dag-array renaming-array (top-nodenum dag)) ;(lookup (top-nodenum dag) translation-alist)
                           dag-array dag-len dag-parent-array
                           dag-constant-alist dag-variable-alist))
                   (if (consp fn) ;tests for ((lambda <formals> <body>) ...<actuals>...) ;move this case up?
                       (let* ((formals (lambda-formals fn))
                              (body (lambda-body fn)))
                         (merge-term-into-dag-array body
                                                    (pairlis$-fast formals arg-nodenums-or-quoteps) ;save this consing?
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                    interpreted-function-alist))
                     ;; normal function call:
                     (if (evaluatable-fn-and-argsp fn arg-nodenums-or-quoteps interpreted-function-alist)
                         ;;it's a ground term:
                         (mv (erp-nil)
                             (enquote (apply-axe-evaluator-to-quoted-args fn arg-nodenums-or-quoteps interpreted-function-alist 0))
                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
                       ;;not a ground term; just add it to the dag:
                       (progn$ ;(cw "Adding (~x0 : ~x1).~%" fn arg-nodenums-or-quoteps)
                        (add-function-call-expr-to-dag-array-with-name fn arg-nodenums-or-quoteps
                                                                             dag-array dag-len dag-parent-array
                                                                             dag-constant-alist dag-variable-alist
                                                                             dag-array-name dag-parent-array-name)))))))))))))

 ;;TERMS are trees with variables, nodenums (new!), and quoteps at the leaves
 ;; Returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;fixme use a changep flag to not recons the list of the terms are constants
 (defund merge-terms-into-dag-array (terms
                                    var-replacement-alist
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                    interpreted-function-alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (symbol-alistp var-replacement-alist)
                               (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                               (interpreted-function-alistp interpreted-function-alist))))
   (if (endp terms)
       (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
     (b* (((mv erp car-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-term-into-dag-array (first terms) var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
          ((mv erp cdr-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-terms-into-dag-array (rest terms) var-replacement-alist
                                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                       interpreted-function-alist))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
       (mv (erp-nil)
           (cons car-nodenum-or-quotep cdr-nodenums-or-quoteps)
           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))

(make-flag merge-term-into-dag-array)

(defthm-flag-merge-term-into-dag-array
  (defthm natp-of-mv-nth-3-of-merge-term-into-dag-array-2 ;dup? with something generated by def-dag-builder-theorems
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-term-into-dag-array
                              term var-replacement-alist dag-array dag-len dag-parent-array
                              dag-constant-alist dag-variable-alist
                              dag-array-name dag-parent-array-name
                              interpreted-function-alist))))
    :flag merge-term-into-dag-array)
  (defthm natp-of-mv-nth-3-of-merge-terms-into-dag-array-2 ;dup?
    (implies (natp dag-len)
             (natp (mv-nth 3 (merge-terms-into-dag-array
                              terms var-replacement-alist
                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                              interpreted-function-alist))))
    :flag merge-terms-into-dag-array)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array merge-terms-into-dag-array) (natp)))))

(defthm-flag-merge-term-into-dag-array
  (defthmd <=-of-mv-nth-3-of-merge-term-into-dag-array-2 ;dup? with something generated by def-dag-builder-theorems
    (implies (natp dag-len)
             (<= dag-len (mv-nth 3 (merge-term-into-dag-array
                                    term var-replacement-alist dag-array dag-len dag-parent-array
                                    dag-constant-alist dag-variable-alist
                                    dag-array-name dag-parent-array-name
                                    interpreted-function-alist))))
    :flag merge-term-into-dag-array)
  (defthmd <=-of-mv-nth-3-of-merge-terms-into-dag-array-2 ;dup?
    (implies (natp dag-len)
             (<= dag-len (mv-nth 3 (merge-terms-into-dag-array
                                    terms var-replacement-alist
                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                    interpreted-function-alist))))
    :flag merge-terms-into-dag-array)
  :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array merge-terms-into-dag-array) (natp)))))

(defthmd <=-of-mv-nth-3-of-merge-term-into-dag-array-2-linear ;dup? with something generated by def-dag-builder-theorems
  (implies (natp dag-len)
           (<= dag-len (mv-nth 3 (merge-term-into-dag-array
                                  term var-replacement-alist dag-array dag-len dag-parent-array
                                  dag-constant-alist dag-variable-alist
                                  dag-array-name dag-parent-array-name
                                  interpreted-function-alist))))
  :rule-classes :linear
  :hints (("Goal" :use <=-of-mv-nth-3-of-merge-term-into-dag-array-2)))

(defthmd <=-of-mv-nth-3-of-merge-terms-into-dag-array-2-linear ;dup?
  (implies (natp dag-len)
           (<= dag-len (mv-nth 3 (merge-terms-into-dag-array
                                  terms var-replacement-alist
                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                  interpreted-function-alist))))
  :rule-classes :linear
  :hints (("Goal" :use <=-of-mv-nth-3-of-merge-terms-into-dag-array-2)))

(defthmd <=-of-mv-nth-3-of-merge-term-into-dag-array-2-gen ;dup? with something generated by def-dag-builder-theorems
  (implies (and (natp dag-len)
                (<= bound dag-len))
           (<= bound (mv-nth 3 (merge-term-into-dag-array
                                term var-replacement-alist dag-array dag-len dag-parent-array
                                dag-constant-alist dag-variable-alist
                                dag-array-name dag-parent-array-name
                                interpreted-function-alist))))
  :hints (("Goal" :use (:instance <=-of-mv-nth-3-of-merge-term-into-dag-array-2)
           :in-theory (disable <=-of-mv-nth-3-of-merge-term-into-dag-array-2))))

(defthmd <=-of-mv-nth-3-of-merge-terms-into-dag-array-2-gen ;dup?
  (implies (and (natp dag-len)
                (<= bound dag-len))
           (<= bound (mv-nth 3 (merge-terms-into-dag-array
                                terms var-replacement-alist
                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                interpreted-function-alist))))
  :hints (("Goal" :use (:instance  <=-of-mv-nth-3-of-merge-terms-into-dag-array-2)
           :in-theory (disable  <=-of-mv-nth-3-of-merge-terms-into-dag-array-2))))

;drop?
(defthm-flag-merge-term-into-dag-array
  (defthm dag-constant-alistp-of-mv-nth-5-of-merge-term-into-dag-array
    (implies (and (dag-constant-alistp dag-constant-alist)
                  (natp dag-len))
             (dag-constant-alistp (mv-nth 5 (merge-term-into-dag-array
                                             term var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist))))
    :flag merge-term-into-dag-array)
  (defthm dag-constant-alistp-of-mv-nth-5-of-merge-terms-into-dag-array
    (implies (and (dag-constant-alistp dag-constant-alist)
                  (natp dag-len))
             (dag-constant-alistp (mv-nth 5 (merge-terms-into-dag-array
                                             terms var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist))))
    :flag merge-terms-into-dag-array)
    :hints (("Goal" :in-theory (e/d (merge-term-into-dag-array merge-terms-into-dag-array) ()))))

;drop?
(defthm-flag-merge-term-into-dag-array
  (defthm dag-variable-alistp-of-mv-nth-6-of-merge-term-into-dag-array
    (implies (and (pseudo-termp term)
                  (dag-variable-alistp dag-variable-alist)
                  (natp dag-len))
             (dag-variable-alistp (mv-nth 6 (merge-term-into-dag-array
                                             term var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist))))
    :flag merge-term-into-dag-array)
  (defthm dag-variable-alistp-of-mv-nth-6-of-merge-terms-into-dag-array
    (implies (and (pseudo-term-listp terms)
                  (dag-variable-alistp dag-variable-alist)
                  (natp dag-len))
             (dag-variable-alistp (mv-nth 6 (merge-terms-into-dag-array
                                             terms var-replacement-alist
                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                             interpreted-function-alist))))
    :flag merge-terms-into-dag-array)
  :hints (("Goal" :expand ((MERGE-TERM-INTO-DAG-ARRAY TERM VAR-REPLACEMENT-ALIST
                                                      DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY
                                                      DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST
                                                      DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
                                                      INTERPRETED-FUNCTION-ALIST))
                  :in-theory (e/d (merge-term-into-dag-array
                                   merge-terms-into-dag-array
                                   ;call-of-dag-val-with-axe-evaluator-with-inlineable-dagp ;somewhat slow. why didn't the forward-chaining rules suffice?
                                   )
                                  ()))))

(local (in-theory (disable use-all-<-for-car
                           bounded-darg-listp-when-<-of-largest-non-quotep
                           ;;bounded-darg-listp-when-all-consp
                           )))

(set-case-split-limitations 'nil)
(set-case-split-limitations '(10 10))

(local (in-theory (disable consp-from-len-cheap
                           ;use-all-consp-for-car
                           default-+-2 default-cdr
                           quote-lemma-for-bounded-darg-listp-gen-alt)))

;; (thm
;;  (implies (and (pseudo-termp term)
;;                (posp n)
;;                (not (equal 'quote (nth 0 term))))
;;           (pseudo-termp (nth n term)))
;;  :hints (("Goal" :in-theory (e/d (pseudo-termp nth) (NTH-OF-CDR)))))

(defthm-flag-merge-term-into-dag-array
  (defthm merge-term-into-dag-array-return-type
    (implies (and (pseudo-termp term)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
             (and (dargp-less-than (mv-nth 1 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))
                                              (mv-nth 3 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                  ;could prove later, as a corollary?
                  (dargp (mv-nth 1 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))

                  (wf-dagp dag-array-name
                           (mv-nth 2 (merge-term-into-dag-array
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 3 (merge-term-into-dag-array
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           dag-parent-array-name
                           (mv-nth 4 (merge-term-into-dag-array
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 5 (merge-term-into-dag-array
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist))
                           (mv-nth 6 (merge-term-into-dag-array
                                      term
                                      var-replacement-alist
                                      dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                      interpreted-function-alist)))
                  (<= dag-len
                      (mv-nth 3 (merge-term-into-dag-array
                                 term
                                 var-replacement-alist
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 interpreted-function-alist)))))
    :flag merge-term-into-dag-array)
  (defthm merge-terms-into-dag-array-return-type
    (implies (and (pseudo-term-listp terms)
                  (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (symbol-alistp var-replacement-alist)
                  (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                  ;;no errors:
                  (not (mv-nth 0 (merge-terms-into-dag-array terms var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
             (and (true-listp (mv-nth 1 (merge-terms-into-dag-array
                                         terms
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                         interpreted-function-alist)))
                  (equal (len (mv-nth 1 (merge-terms-into-dag-array
                                         terms
                                         var-replacement-alist
                                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                         interpreted-function-alist)))
                         (len terms))
                  (darg-listp (mv-nth 1 (merge-terms-into-dag-array
                                                   terms
                                                   var-replacement-alist
                                                   dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                   interpreted-function-alist)))
                  (bounded-darg-listp (mv-nth 1 (merge-terms-into-dag-array
                                                             terms
                                                             var-replacement-alist
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                             interpreted-function-alist))
                                                  (mv-nth 3 (merge-terms-into-dag-array
                                                             terms
                                                             var-replacement-alist
                                                             dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                             interpreted-function-alist)))
                  (wf-dagp dag-array-name
                           (mv-nth 2 (merge-terms-into-dag-array
                                                terms
                                                var-replacement-alist
                                                dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                interpreted-function-alist))
                           (mv-nth 3 (merge-terms-into-dag-array
                                                 terms
                                                 var-replacement-alist
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                 interpreted-function-alist))
                           dag-parent-array-name
                           (mv-nth 4 (merge-terms-into-dag-array
                                                 terms
                                                 var-replacement-alist
                                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                 interpreted-function-alist))
                           (mv-nth 5 (merge-terms-into-dag-array
                                                  terms
                                                  var-replacement-alist
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist))
                           (mv-nth 6 (merge-terms-into-dag-array
                                                  terms
                                                  var-replacement-alist
                                                  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                  interpreted-function-alist)))

                  (<= dag-len
                      (mv-nth 3 (merge-terms-into-dag-array
                                 terms
                                 var-replacement-alist
                                 dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                 interpreted-function-alist)))))
    :flag merge-terms-into-dag-array)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-term-into-dag-array merge-terms-into-dag-array car-becomes-nth-of-0 ;wf-dagp
                                                      )
                           (natp dargp pseudo-term-listp pseudo-termp)))))

;; todo: def-dag-builder-theorems has trouble with this
(DEFTHM BOUND-ON-MV-NTH-3-OF-MERGE-TERM-INTO-DAG-ARRAY-3
  (IMPLIES
   (AND
    (WF-DAGP DAG-ARRAY-NAME DAG-ARRAY DAG-LEN
             DAG-PARENT-ARRAY-NAME DAG-PARENT-ARRAY
             DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST)
    ;; ;; needed?:
    ;; (not (MV-NTH 0
    ;;              (MERGE-TERM-INTO-DAG-ARRAY TERM VAR-REPLACEMENT-ALIST
    ;;                                         DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY
    ;;                                         DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST
    ;;                                         DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME
    ;;                                         INTERPRETED-FUNCTION-ALIST)))
    (PSEUDO-TERMP TERM)
    (SYMBOL-ALISTP VAR-REPLACEMENT-ALIST)
    (BOUNDED-DARG-LISTP (STRIP-CDRS VAR-REPLACEMENT-ALIST)
                                    DAG-LEN)
    (INTERPRETED-FUNCTION-ALISTP INTERPRETED-FUNCTION-ALIST)
    (NATP DAG-LEN))
   (<= DAG-LEN (MV-NTH 3 (MERGE-TERM-INTO-DAG-ARRAY TERM VAR-REPLACEMENT-ALIST DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME INTERPRETED-FUNCTION-ALIST))))
  :RULE-CLASSES
  ((:LINEAR
    :TRIGGER-TERMS
    ((MV-NTH 3 (MERGE-TERM-INTO-DAG-ARRAY TERM VAR-REPLACEMENT-ALIST DAG-ARRAY DAG-LEN DAG-PARENT-ARRAY DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST DAG-ARRAY-NAME DAG-PARENT-ARRAY-NAME INTERPRETED-FUNCTION-ALIST)))))
  :HINTS (("Goal" :in-theory (enable <=-of-mv-nth-3-of-merge-term-into-dag-array-2))))

(def-dag-builder-theorems
  (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)
  (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
  :hyps ((wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist) ;should I have to give this?
         (pseudo-termp term)
         (symbol-alistp var-replacement-alist)
         (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
         (interpreted-function-alistp interpreted-function-alist))
  :recursivep nil
  :hyps-everywhere t
  :hints (("Goal" ;:expand (merge-tree-into-dag-array tree var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)
;           :in-theory (disable wf-dagp)
           :use (:instance merge-tree-into-dag-array-return-type)
           ))
  :dag-parent-array-name dag-parent-array-name
  :dag-array-name dag-array-name)

; drop some of these?:

(defthm merge-term-into-dag-array-return-type-corollary
  (implies (and (<= bound dag-len)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (<= bound
               (mv-nth 3 (merge-term-into-dag-array
                          term
                          var-replacement-alist
                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                          interpreted-function-alist))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-return-type)
           :in-theory (e/d () (merge-term-into-dag-array-return-type)))))

(defthm merge-term-into-dag-array-return-type-corollary2
  (implies (and (<= (mv-nth 3 (merge-term-into-dag-array
                               term
                               var-replacement-alist
                               dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                               interpreted-function-alist)) bound)
                (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)

                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
           (DARGP-LESS-THAN
            (mv-nth 1 (merge-term-into-dag-array
                       term
                       var-replacement-alist
                       dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                       interpreted-function-alist))
            bound))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-return-type)
           :in-theory (e/d (wf-dagp) (merge-term-into-dag-array-return-type)))))

(defthm merge-term-into-dag-array-return-type-corollary3
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (not (consp (mv-nth 1 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
                )
           (< (mv-nth 1 (merge-term-into-dag-array
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         interpreted-function-alist))
              (mv-nth 3 (merge-term-into-dag-array
                         term
                         var-replacement-alist
                         dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                         interpreted-function-alist))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-return-type)
           :in-theory (e/d (wf-dagp) (merge-term-into-dag-array-return-type
                               MERGE-TERM-INTO-DAG-ARRAY-RETURN-TYPE-COROLLARY2
                               MERGE-TERM-INTO-DAG-ARRAY-RETURN-TYPE-COROLLARY)))))

(defthm merge-term-into-dag-array-return-type-corollary4
  (implies (and (pseudo-termp term)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)

                (symbol-alistp var-replacement-alist)
                (bounded-darg-listp (strip-cdrs var-replacement-alist) dag-len)
                ;;no errors:
                (not (mv-nth 0 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)))
                (not (consp (mv-nth 1 (merge-term-into-dag-array term var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))))
                )
           (natp (mv-nth 1 (merge-term-into-dag-array
                            term
                            var-replacement-alist
                            dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                            interpreted-function-alist))))
  :hints (("Goal" :use (:instance merge-term-into-dag-array-return-type)
           :in-theory (e/d (wf-dagp) (merge-term-into-dag-array-return-type)))))

(verify-guards merge-term-into-dag-array
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-term-into-dag-array merge-terms-into-dag-array car-becomes-nth-of-0
                                                      not-equal-of-len-and-1-when-dargp
                                                      call-of-dag-val-with-axe-evaluator-with-inlineable-dagp
                                                      <-of-nth-when-bounded-darg-listp
                                                      true-listp-of-nth-1-of-nth-0-when-axe-treep
                                                      ;wf-dagp
                                                      ;wf-dagp-expander
                                                      )
                           (natp dargp pseudo-term-listp pseudo-termp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; does not translate the term
;todo: reduce to take wlrd instead of state?
(defun dag-or-term-to-term (item state)
  (declare (xargs :stobjs state))
  (if (eq nil item) ; we assume nil is the constant nil, not an empty DAG
      *nil*
    (if (weak-dagp item)
        (let ((dag-fns (dag-fns item)))
          (if (not (function-symbolsp dag-fns (w state)))
              (er hard? 'dag-or-term-to-term "Some unknown functions among those in DAG: ~X01." dag-fns nil)
            ;; we embed a DAG in a call to dag-val-with-axe-evaluator, to avoid
            ;; explosion in the term size:
            `(dag-val-with-axe-evaluator ',item
                                         ,(make-acons-nest (dag-vars item))
                                         ',(make-interpreted-function-alist (get-non-built-in-supporting-fns-list dag-fns *axe-evaluator-functions* (w state)) (w state))
                                         '0 ;array depth (not very important)
                                         )))
      item)))
