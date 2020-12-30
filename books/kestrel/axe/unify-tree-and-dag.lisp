; This book deals with matching axe-trees against (parts of) dag-arrays.
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

;; TODO: Add support for failing fast if the skeleton is wrong.

(include-book "dag-arrays")
(include-book "axe-trees")
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))

;; (local (in-theory (enable member-equal-becomes-memberp)))

(local (in-theory (disable symbol-alistp strip-cdrs)))

;move
(defthm dargp-of-lookup-equal-when-all-dargp-of-strip-cdrs
  (implies (all-dargp (strip-cdrs alist))
           (iff (dargp (lookup-equal var alist))
                (assoc-equal var alist)))
  :hints (("Goal" :induct t
           :in-theory (e/d (all-dargp lookup-equal strip-cdrs)
                           (myquotep)))))

(defthm dargp-less-than-of-car-when-all-dargp-less-than
  (implies (all-dargp-less-than items bound)
           (equal (dargp-less-than (car items) bound)
                  (consp items)))
  :hints (("Goal" :in-theory (enable all-dargp-less-than))))

;doesn't support lambdas
;fixme could use a single RV if we used :fail (which is not an alist) to signal failure?
(mutual-recursion
 ;; tree (e.g., a hyp with some free vars to be bound) has leaves that are quoteps, nodenums (from vars already bound), and free vars
 ;; returns (mv successp alist), where if successp is non-nil, then alist extends alist-acc with (compatible) bindings for the free vars
 ;; if successp is nil, the alist returned is irrelevant
 ;; the alist returned (and alist-acc) map variables to nodenums or quoteps
 ;; The guard would be simpler if we could pass in dag-len, but we don't want to pass that around.
 (defund unify-tree-with-dag-node (tree nodenum-or-quotep dag-array alist-acc)
   (declare (xargs :guard (and (axe-treep tree)
                               (dargp nodenum-or-quotep)
                               (if (natp nodenum-or-quotep)
                                   (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep))
                                 t)
                               (symbol-alistp alist-acc))
                   :verify-guards nil ;done below
                   ))
   (if (symbolp tree) ;it's a variable:
       (let ((binding (assoc-eq tree alist-acc)))
         (if binding
             ;;bindings must match:
             (mv (equal (cdr binding) nodenum-or-quotep)
                 alist-acc)
           ;;make a new binding:
           (mv t (acons-fast tree nodenum-or-quotep alist-acc))))
     (if (consp tree)
         (let ((fn (ffn-symb tree)))
           (if (eq fn 'quote)
               (mv (equal tree nodenum-or-quotep) ;todo: what if nodenum-or-quotep is the nodenum of a quotep?
                   alist-acc)
             ;;regular function call:
             (if (consp nodenum-or-quotep)
                 ;; a quotep doesn't match with a function call:
                 (mv nil nil)
               ;;NODENUM-OR-QUOTEP must be a nodenum:
               (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
                 (if (call-of fn expr) ;doesn't support lambdas
                     (unify-trees-with-dag-nodes (fargs tree) (dargs expr) dag-array alist-acc)
                   (mv nil nil))))))
       ;;tree must be a nodenum:
       (mv (equal tree nodenum-or-quotep) ; TODO: Use eql or = here?
           alist-acc))))

 ;; rename unify-trees-with-dag-nodes
 ;; returns (mv successp alist), where if successp is non-nil, then alist extends alist-acc with (compatible) bindings for the free vars
 ;; The guard would be simpler if we could pass in dag-len, but we don't want to pass that around.
 (defund unify-trees-with-dag-nodes (tree-lst nodenum-or-quotep-lst dag-array alist-acc)
   (declare (xargs :guard (and (all-axe-treep tree-lst)
                               (true-listp tree-lst)
                               (all-dargp nodenum-or-quotep-lst)
                               (true-listp nodenum-or-quotep-lst)
                               (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep nodenum-or-quotep-lst)))
                               (symbol-alistp alist-acc))))
   (if (endp tree-lst)
       (mv t alist-acc)
     (if (not (consp nodenum-or-quotep-lst))
         (prog2$ (er hard? 'unify-trees-with-dag-nodes "Arity mismatch.")
                 (mv nil nil))
       (mv-let (car-successp alist-acc)
         (unify-tree-with-dag-node (first tree-lst) (first nodenum-or-quotep-lst) dag-array alist-acc)
         (if (not car-successp)
             (mv nil nil)
           (unify-trees-with-dag-nodes (rest tree-lst) (rest nodenum-or-quotep-lst) dag-array alist-acc)))))))

(make-flag unify-tree-with-dag-node)

(defthm-flag-unify-tree-with-dag-node
  (defthm symbol-alistp-of-mv-nth-1-of-unify-tree-with-dag-node
    (implies (symbol-alistp alist-acc)
             (symbol-alistp (mv-nth 1 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc))))
    :flag unify-tree-with-dag-node)
  (defthm symbol-alistp-of-mv-nth-1-of-unify-trees-with-dag-nodes
    (implies (symbol-alistp alist-acc)
             (symbol-alistp (mv-nth 1 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc))))
    :flag unify-trees-with-dag-nodes)
    :hints (("Goal" :expand ((unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc)
                             (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc)))))

(verify-guards unify-tree-with-dag-node)

(defthm-flag-unify-tree-with-dag-node
  (defthm alistp-of-unify-tree-with-dag-node
    (implies (alistp alist-acc)
             (alistp (mv-nth 1 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc))))
    :flag unify-tree-with-dag-node)
  (defthm alistp-of-for-unify-trees-with-dag-nodes
    (implies (alistp alist-acc)
             (alistp (mv-nth 1 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc))))
    :flag unify-trees-with-dag-nodes)
  :hints (("Goal" :in-theory (enable unify-trees-with-dag-nodes unify-tree-with-dag-node))))

;; see all-vars1 but that one has an accumulator.  also, this works on axe-trees!
(mutual-recursion
 (defun tree-vars (tree)
   (declare (xargs :guard (axe-treep tree)))
   (if (atom tree)
       (if (symbolp tree)
           (list tree)
         ;; tree is a nodenum:
         nil)
     (if (fquotep tree)
         nil
       (tree-vars-lst (fargs tree)))))
 (defun tree-vars-lst (trees)
   (declare (xargs :guard (all-axe-treep trees)))
   (if (atom trees)
       nil
     (append (tree-vars (first trees))
             (tree-vars-lst (rest trees))))))

(defthm-flag-unify-tree-with-dag-node
  (defthm unify-tree-with-dag-node-mono
    (implies (and ;; (axe-treep tree)
              ;; (natp dag-len)
              ;; (dargp-less-than nodenum-or-quotep dag-len)
              ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
              ;; (symbol-alistp alist-acc)
              (member-equal x (strip-cars alist-acc))
              (mv-nth 0 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc))
              ;;(symbolp x)
              )
             (member-equal x (strip-cars (mv-nth 1 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc)))))
    :flag unify-tree-with-dag-node)
  (defthm unify-trees-with-dag-nodes-mono
    (implies (and ;; (all-axe-treep tree-lst)
              ;; (natp dag-len)
              ;; (true-listp tree-lst)
              ;; (all-dargp-less-than nodenum-or-quotep-lst dag-len)
              ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
              ;; (symbol-alistp alist-acc)
              ;; (equal (len tree-lst)
              ;;        (len nodenum-or-quotep-lst))
              (member-equal x (strip-cars alist-acc))
              (mv-nth 0 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc))
              ;;(symbolp x)
              )
             (member-equal x (strip-cars (mv-nth 1 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc)))))
    :flag unify-trees-with-dag-nodes)
  :hints (("Goal" :in-theory (enable unify-trees-with-dag-nodes unify-tree-with-dag-node))))

(defthm-flag-unify-tree-with-dag-node
  (defthm unify-tree-with-dag-node-mono2
    (implies (and ;; (axe-treep tree)
              ;; (natp dag-len)
              ;; (dargp-less-than nodenum-or-quotep dag-len)
              ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
              ;; (symbol-alistp alist-acc)
              (subsetp-equal x (strip-cars alist-acc))
              (mv-nth 0 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc))
              ;(symbolp x)
              )
             (subsetp-equal x (strip-cars (mv-nth 1 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc)))))
    :flag unify-tree-with-dag-node)
  (defthm unify-trees-with-dag-nodes-mono2
    (implies (and ;; (all-axe-treep tree-lst)
              ;; (natp dag-len)
              ;; (true-listp tree-lst)
              ;; (all-dargp-less-than nodenum-or-quotep-lst dag-len)
              ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
              ;; (symbol-alistp alist-acc)
              ;; (equal (len tree-lst)
              ;;        (len nodenum-or-quotep-lst))
              (subsetp-equal x (strip-cars alist-acc))

              (mv-nth 0 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc))
;(symbolp x)
              )
             (subsetp-equal x
                            (strip-cars (mv-nth 1 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc)))))
    :flag unify-trees-with-dag-nodes)
  :hints (("Goal" :in-theory (enable unify-trees-with-dag-nodes unify-tree-with-dag-node))))

(defthm-flag-unify-tree-with-dag-node
  (defthm unify-tree-with-dag-node-binds-all-vars
    (implies (and (axe-treep tree)
                  ;; (natp dag-len)
                  ;; (dargp-less-than nodenum-or-quotep dag-len)
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (symbol-alistp alist-acc)
                  (mv-nth 0 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc)))
             (subsetp-equal (tree-vars tree)
                            (strip-cars (mv-nth 1 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc)))))
    :flag unify-tree-with-dag-node)
  (defthm unify-trees-with-dag-nodes-binds-all-vars
    (implies (and (all-axe-treep tree-lst)
                  ;; (natp dag-len)
                  ;; (true-listp tree-lst)
                  ;; (all-dargp-less-than nodenum-or-quotep-lst dag-len)
                  ;; (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (symbol-alistp alist-acc)
                  (mv-nth 0 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc)))
             (subsetp-equal (tree-vars-lst tree-lst)
                            (strip-cars (mv-nth 1 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc)))))
    :flag unify-trees-with-dag-nodes)
  :hints (("Goal" :in-theory (enable unify-trees-with-dag-nodes unify-tree-with-dag-node))))

(defthm-flag-unify-tree-with-dag-node
  (defthm all-dargp-of-strip-cdrs-of-mv-nth-1-of-unify-tree-with-dag-node
    (implies (and (axe-treep tree)
                  (dargp nodenum-or-quotep)
                  (if (natp nodenum-or-quotep)
                      (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep))
                    t)
                  (all-dargp (strip-cdrs alist-acc))
                  (mv-nth 0 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc)))
             (all-dargp (strip-cdrs (mv-nth 1 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc)))))
    :flag unify-tree-with-dag-node)
  (defthm all-dargp-of-strip-cdrs-of-mv-nth-1-of-unify-trees-with-dag-nodes
    (implies (and (all-axe-treep tree-lst)
                  (true-listp tree-lst)
                  (all-dargp nodenum-or-quotep-lst)
                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep nodenum-or-quotep-lst)))
                  (all-dargp (strip-cdrs alist-acc))
                  (mv-nth 0 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc)))
             (all-dargp (strip-cdrs (mv-nth 1 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc)))))
    :flag unify-trees-with-dag-nodes)
  :hints (("Goal" :in-theory (enable unify-trees-with-dag-nodes unify-tree-with-dag-node))))

(defthm-flag-unify-tree-with-dag-node
  (defthm all-dargp-less-than-of-strip-cdrs-of-mv-nth-1-of-unify-tree-with-dag-node
    (implies (and (axe-treep tree)
                  (if (natp nodenum-or-quotep)
                      (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep))
                    t)
                  (integerp dag-len)
                  (dargp-less-than nodenum-or-quotep dag-len)
                  (all-dargp-less-than (strip-cdrs alist-acc) dag-len)
                  (mv-nth 0 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc)))
             (all-dargp-less-than (strip-cdrs (mv-nth 1 (unify-tree-with-dag-node tree nodenum-or-quotep dag-array alist-acc)))
                                             dag-len))
    :flag unify-tree-with-dag-node)
  (defthm all-dargp-less-than-of-strip-cdrs-of-mv-nth-1-of-unify-trees-with-dag-nodes
    (implies (and (all-axe-treep tree-lst)
                  (true-listp tree-lst)
                  (all-dargp-less-than nodenum-or-quotep-lst dag-len)
                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep nodenum-or-quotep-lst)))
                  (integerp dag-len)
                  (all-dargp-less-than (strip-cdrs alist-acc) dag-len)
                  (mv-nth 0 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc)))
             (all-dargp-less-than (strip-cdrs (mv-nth 1 (unify-trees-with-dag-nodes tree-lst nodenum-or-quotep-lst dag-array alist-acc)))
                                             dag-len))
    :flag unify-trees-with-dag-nodes)
  :hints (("Goal" :in-theory (enable unify-trees-with-dag-nodes unify-tree-with-dag-node))))
