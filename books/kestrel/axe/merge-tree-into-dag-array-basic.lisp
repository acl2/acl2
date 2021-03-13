; Merging an axe-tree into a DAG
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This version does not support embedded dags

(include-book "dag-array-builders2")
(include-book "interpreted-function-alistp")
(include-book "axe-trees")
;(include-book "def-dag-builder-theorems")
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(mutual-recursion
 ;;TREE is a tree over variables, nodenums in the dag, and quoteps
 ;;variable names are shared between TREE and DAG-ARRAY, except those changed by the var-replacement-alist
 ;; Returns (mv erp nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
 ;; where nodenum-or-quotep is equivalent to the tree passed in, and nodes already in the dag passed in remain unchanged (and the aux. data structures have been updated, of course)
 ;; todo: when this is called on a term, we could instead call a simpler version that only works on terms
 (defund merge-tree-into-dag-array-basic (tree
                                          var-replacement-alist ;maps vars in the term to nodenums/quoteps
                                          dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                          interpreted-function-alist)
   (declare (xargs :guard (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (axe-treep tree)
                               (bounded-axe-treep tree dag-len)
                               (symbol-alistp var-replacement-alist)
                               (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                               ;;(<= (+ (len vars) dag-len) 2147483645)
                               (interpreted-function-alistp interpreted-function-alist))
                   :verify-guards nil ;; done below
                   ))
   (if (atom tree)
       (if (symbolp tree)
           (let ((match (assoc-eq tree var-replacement-alist)))
             (if match
                 (mv (erp-nil) (cdr match) dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               ;; tree is a variable:
               (add-variable-to-dag-array-with-name tree dag-array dag-len
                                                    dag-parent-array ;;just passed through (slow?)
                                                    dag-constant-alist ;;just passed through (slow?)
                                                    dag-variable-alist dag-array-name dag-parent-array-name)))
         ;; tree is a nodenum:
         (mv (erp-nil) tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
     (let ((fn (ffn-symb tree)))
       (if (eq 'quote fn)
           ;; tree is a quoted constant:
           (mv (erp-nil) tree dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
         ;; tree is a function call:
         (let* ((args (fargs tree)))
           ;;begin by adding the args to the dag:
           (mv-let
             (erp arg-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (merge-trees-into-dag-array-basic args var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist)
             (if erp
                 (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
               ;;check for the special case of a call to dag-val-with-axe-evaluator where we can inline the dag:
               ;;todo: maybe call call-of-dag-val-with-axe-evaluator-with-inlineable-dagp here?
               (if (consp fn) ;tests for ((lambda <formals> <body>) ...<actuals>...) ;move this case up? ;; TODO: Can lambdas appear?
                   (merge-tree-into-dag-array-basic (lambda-body fn)
                                                    (pairlis$-fast (lambda-formals fn) arg-nodenums-or-quoteps) ;save this consing?
                                                    dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                                    interpreted-function-alist)
                 ;;normal function call:
                 ;;ffixme what about ground terms?
                 ;;maybe move the dag-val-with-inlineable-dagp case into add-function-call-expr-to-dag-array-with-name?
                 (add-function-call-expr-to-dag-array-with-name fn arg-nodenums-or-quoteps
                                                                dag-array dag-len dag-parent-array
                                                                dag-constant-alist dag-variable-alist
                                                                dag-array-name dag-parent-array-name)))))))))

 ;;TREES are trees with variables, nodenums (new!), and quoteps at the leaves
 ;;returns (mv erp nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
 (defund merge-trees-into-dag-array-basic (trees
                                           var-replacement-alist
                                           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name
                                           interpreted-function-alist)
   (declare (xargs :guard (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                               (true-listp trees)
                               (all-axe-treep trees)
                               (all-bounded-axe-treep trees dag-len)
                               (symbol-alistp var-replacement-alist)
                               (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                               ;;(<= (+ (len vars) dag-len) 2147483645)
                               (interpreted-function-alistp interpreted-function-alist))))
   (if (endp trees)
       (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
     (b* (((mv erp car-nodenum-or-quotep dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-tree-into-dag-array-basic (first trees) var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))
          ((when erp) (mv erp nil  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
          ((mv erp cdr-nodenums-or-quoteps dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
           (merge-trees-into-dag-array-basic (rest trees) var-replacement-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist dag-array-name dag-parent-array-name interpreted-function-alist))
          ((when erp) (mv erp nil  dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))
       (mv (erp-nil)
           (cons car-nodenum-or-quotep cdr-nodenums-or-quoteps)
           dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))))

(make-flag merge-tree-into-dag-array-basic)

(defthm-flag-merge-tree-into-dag-array-basic
  (defthm merge-tree-into-dag-array-basic-return-type
    (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (axe-treep tree)
                  (bounded-axe-treep tree dag-len)
                  (symbol-alistp var-replacement-alist)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                  ;;(<= (+ (len vars) dag-len) 2147483645)
                  (interpreted-function-alistp interpreted-function-alist))
             (mv-let (erp nodenum-or-quotep new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
               (merge-tree-into-dag-array-basic tree var-replacement-alist
                                                dag-array dag-len dag-parent-array
                                                dag-constant-alist dag-variable-alist
                                                dag-array-name dag-parent-array-name
                                                interpreted-function-alist)
               (implies (not erp)
                        (and (wf-dagp dag-array-name new-dag-array new-dag-len dag-parent-array-name new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                             (dargp-less-than nodenum-or-quotep new-dag-len)
                             (<= dag-len new-dag-len)))))
    :flag merge-tree-into-dag-array-basic)
  (defthm merge-trees-into-dag-array-basic-return-type
    (implies (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (true-listp trees)
                  (all-axe-treep trees)
                  (all-bounded-axe-treep trees dag-len)
                  (symbol-alistp var-replacement-alist)
                  (all-dargp-less-than (strip-cdrs var-replacement-alist) dag-len)
                  ;;(<= (+ (len vars) dag-len) 2147483645)
                  (interpreted-function-alistp interpreted-function-alist))
             (mv-let (erp nodenums-or-quoteps new-dag-array new-dag-len new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
               (merge-trees-into-dag-array-basic trees var-replacement-alist
                                                 dag-array dag-len dag-parent-array
                                                 dag-constant-alist dag-variable-alist
                                                 dag-array-name dag-parent-array-name
                                                 interpreted-function-alist)
               (implies (not erp)
                        (and (wf-dagp dag-array-name new-dag-array new-dag-len dag-parent-array-name new-dag-parent-array new-dag-constant-alist new-dag-variable-alist)
                             (all-dargp-less-than nodenums-or-quoteps new-dag-len)
                             (true-listp nodenums-or-quoteps)
                             (<= dag-len new-dag-len)
                             (equal (len nodenums-or-quoteps) (len trees))))))
    :flag merge-trees-into-dag-array-basic)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (merge-tree-into-dag-array-basic
                            merge-trees-into-dag-array-basic)
                           (mv-nth
                            myquotep)))))

(verify-guards merge-tree-into-dag-array-basic)
