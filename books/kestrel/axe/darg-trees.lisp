; Trees whose leaves are DAG function arguments ("dargs")
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/flag" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system) ;for myquotep
(include-book "kestrel/utilities/polarity" :dir :system)
;(include-book "all-dargp")
;(include-book "dargp-less-than")
(include-book "bounded-darg-listp")
(include-book "axe-trees")
(include-book "dag-array-builders")
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

;; Darg-trees are like pseudo-terms but with integers (nodenums in some DAG) at
;; the leaves instead of variable.  Constants can also appear at the leaves.
;; TODO: Also make bounded-darg-treep.
(mutual-recursion
 (defun darg-treep (tree)
   (declare (xargs :guard t))
   (if (atom tree)
       (natp tree) ; a nodenum
     (let ((fn (ffn-symb tree)))
       (if (eq fn 'quote)
           ;; a quoted constant;
           (and (= 1 (len (fargs tree)))
                (true-listp (fargs tree)))
         ;; the application of a function symbol or lambda to args that are darg-trees:
         (let ((args (fargs tree)))
           ;; TODO: Can we require the lambda to be closed?
           (and (darg-tree-listp args)
                (or (symbolp fn)
                    (and (true-listp fn)
                         (equal (len fn) 3)
                         (eq (car fn) 'lambda)
                         (symbol-listp (lambda-formals fn))
                         ;; lambda-body is a regular pseudo-term, not a darg-tree:
                         (pseudo-termp (lambda-body fn))
                         (equal (len (lambda-formals fn))
                                (len args))))))))))
 (defun darg-tree-listp (trees)
   (declare (xargs :guard t))
   (if (atom trees)
       (null trees)
     (and (darg-treep (first trees))
          (darg-tree-listp (rest trees))))))

(defund-inline darg-tree-is-nodenump (tree)
  (declare (xargs :guard (darg-treep tree)))
  (atom tree))

(defund-inline darg-tree-is-quotep (tree)
  (declare (xargs :guard (darg-treep tree)))
  (and (consp tree)
       (eq 'quote (ffn-symb tree))))

(defund-inline darg-tree-is-callp (tree)
  (declare (xargs :guard (darg-treep tree)))
  (and (consp tree)
       (not (eq 'quote (ffn-symb tree)))))

(defund-inline darg-tree-quote-val (tree)
  (declare (xargs :guard (and (darg-treep tree)
                              (darg-tree-is-quotep tree))
                  :guard-hints (("Goal" :in-theory (enable darg-tree-is-quotep)))))
  (unquote tree))

(defund-inline darg-tree-call-fn (tree)
  (declare (xargs :guard (and (darg-treep tree)
                              (darg-tree-is-callp tree))
                  :guard-hints (("Goal" :in-theory (enable darg-tree-is-callp)))))
  (ffn-symb tree))

(defund-inline darg-tree-call-args (tree)
  (declare (xargs :guard (and (darg-treep tree)
                              (darg-tree-is-callp tree))
                  :guard-hints (("Goal" :in-theory (enable darg-tree-is-callp)))))
  (fargs tree))

;; (defthm darg-treep-redef
;;   (equal (darg-treep tree)
;;          (or (natp tree)
;;              (myquotp tree)
;;              (let ((args (fargs tree)))
;;                ;; TODO: Can we require the lambda to be closed?
;;                (and (darg-tree-listp args)
;;                     (or (symbolp fn)
;;                         (and (true-listp fn)
;;                              (equal (len fn) 3)
;;                              (eq (car fn) 'lambda)
;;                              (symbol-listp (lambda-formals fn))
;;                              ;; lambda-body is a regular pseudo-term, not a darg-tree:
;;                              (pseudo-termp (lambda-body fn))
;;                              (equal (len (lambda-formals fn))
;;                                     (len args))))))))
;;   :rule-classes :definition)

(make-flag darg-treep)

(defthm-flag-darg-treep
  (defthm darg-tree-listp-forward-to-true-listp
    (implies (darg-tree-listp trees)
             (true-listp trees))
    :rule-classes :forward-chaining
    :flag darg-tree-listp)
  :skip-others t)

;; Darg-trees are also axe-trees
(defthm-flag-darg-treep
  (defthm axe-treep-when-darg-treep
    (implies (darg-treep tree)
             (axe-treep tree))
    :flag darg-treep)
  (defthm axe-tree-listp-when-darg-tree-listp
    (implies (darg-tree-listp trees)
             (axe-tree-listp trees))
    :flag darg-tree-listp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
 ;; Adds all vars to the dag, turning the TERM into a darg-tree, with nodenums where the variables were.
 ;; Requires the dag-array to be named 'dag-array and the dag-parent-array to be named 'dag-parent-array.
 ;; Returns (mv erp darg-tree dag-array dag-len dag-parent-array dag-variable-alist).
 (defun pseudo-term-to-darg-tree (term
                                  dag-array dag-len dag-parent-array
                                  ;; dag-constant-alist ; not changed
                                  dag-variable-alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                               (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                               (equal (alen1 'dag-array dag-array)
                                      (alen1 'dag-parent-array dag-parent-array))
                               (bounded-dag-variable-alistp dag-variable-alist dag-len))
                   :verify-guards nil ; done below
                   ))
   (if (variablep term)
       (add-variable-to-dag-array term dag-array dag-len dag-parent-array dag-variable-alist)
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           (mv (erp-nil) term dag-array dag-len dag-parent-array dag-variable-alist)
         ;; function call (maybe a lambda):
         (b* (((mv erp arg-trees dag-array dag-len dag-parent-array dag-variable-alist)
               (pseudo-terms-to-darg-trees (fargs term) dag-array dag-len dag-parent-array dag-variable-alist))
              ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-variable-alist)))
           (mv (erp-nil)
               (cons (ffn-symb term) ; no need to fix up a lambda
                     arg-trees)
               dag-array dag-len dag-parent-array dag-variable-alist))))))

 ;; Returns (mv erp darg-trees dag-array dag-len dag-parent-array dag-variable-alist).
 (defun pseudo-terms-to-darg-trees (terms
                                    dag-array dag-len dag-parent-array
                                    ;; dag-constant-alist ; not changed
                                    dag-variable-alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                               (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                               (equal (alen1 'dag-array dag-array)
                                      (alen1 'dag-parent-array dag-parent-array))
                               (bounded-dag-variable-alistp dag-variable-alist dag-len))))
   (if (endp terms)
       (mv (erp-nil) nil dag-array dag-len dag-parent-array dag-variable-alist)
     (b* (((mv erp darg-tree dag-array dag-len dag-parent-array dag-variable-alist)
           (pseudo-term-to-darg-tree (first terms) dag-array dag-len dag-parent-array dag-variable-alist))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-variable-alist))
          ((mv erp darg-trees dag-array dag-len dag-parent-array dag-variable-alist)
           (pseudo-terms-to-darg-trees (rest terms) dag-array dag-len dag-parent-array dag-variable-alist))
          ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-variable-alist)))
       (mv (erp-nil)
           (cons darg-tree darg-trees)
           dag-array dag-len dag-parent-array dag-variable-alist)))))

(make-flag pseudo-term-to-darg-tree)

(defthm-flag-pseudo-term-to-darg-tree
  (defthm len-of-mv-nth-1-of-pseudo-terms-to-darg-trees
    (implies (not (mv-nth 0 (pseudo-terms-to-darg-trees terms dag-array dag-len dag-parent-array dag-variable-alist)))
             (equal (len (mv-nth 1 (pseudo-terms-to-darg-trees terms dag-array dag-len dag-parent-array dag-variable-alist)))
                    (len terms)))
    :flag pseudo-terms-to-darg-trees)
  :skip-others t)

(defthm-flag-pseudo-term-to-darg-tree
  (defthm pseudo-term-to-darg-tree-return-type
    (implies (and (pseudo-termp term)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                  (equal (alen1 'dag-array dag-array)
                         (alen1 'dag-parent-array dag-parent-array))
                  (bounded-dag-variable-alistp dag-variable-alist dag-len))
             (mv-let (erp darg-tree dag-array dag-len dag-parent-array dag-variable-alist)
               (pseudo-term-to-darg-tree term dag-array dag-len dag-parent-array dag-variable-alist)
               (implies (not erp)
                        (and (darg-treep darg-tree)
                             (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                             (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                             (equal (alen1 'dag-parent-array dag-parent-array)
                                    (alen1 'dag-array dag-array))
                             (bounded-dag-variable-alistp dag-variable-alist dag-len)))))
    :flag pseudo-term-to-darg-tree)
  (defthm pseudo-terms-to-darg-trees-return-type
    (implies (and (pseudo-term-listp terms)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                  (equal (alen1 'dag-array dag-array)
                         (alen1 'dag-parent-array dag-parent-array))
                  (bounded-dag-variable-alistp dag-variable-alist dag-len))
             (mv-let (erp darg-trees dag-array dag-len dag-parent-array dag-variable-alist)
               (pseudo-terms-to-darg-trees terms dag-array dag-len dag-parent-array dag-variable-alist)
               (implies (not erp)
                        (and (darg-tree-listp darg-trees)
                             (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                             (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                             (equal (alen1 'dag-parent-array dag-parent-array)
                                    (alen1 'dag-array dag-array))
                             (bounded-dag-variable-alistp dag-variable-alist dag-len)))))
    :flag pseudo-terms-to-darg-trees))

(verify-guards pseudo-term-to-darg-tree)

(defthm-flag-pseudo-term-to-darg-tree
  (defthm darg-treep-of-mv-nth-1-of-pseudo-term-to-darg-tree
    (implies (and (pseudo-termp term)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                  (equal (alen1 'dag-array dag-array)
                         (alen1 'dag-parent-array dag-parent-array))
                  (bounded-dag-variable-alistp dag-variable-alist dag-len))
             (mv-let (erp darg-tree dag-array dag-len dag-parent-array dag-variable-alist)
               (pseudo-term-to-darg-tree term dag-array dag-len dag-parent-array dag-variable-alist)
               (declare (ignore dag-array dag-len dag-parent-array dag-variable-alist))
               (implies (not erp)
                        (darg-treep darg-tree))))
    :flag pseudo-term-to-darg-tree)
  (defthm darg-tree-listp-of-mv-nth-1-of-pseudo-terms-to-darg-trees
    (implies (and (pseudo-term-listp terms)
                  (pseudo-dag-arrayp 'dag-array dag-array dag-len)
                  (dag-parent-arrayp 'dag-parent-array dag-parent-array)
                  (equal (alen1 'dag-array dag-array)
                         (alen1 'dag-parent-array dag-parent-array))
                  (bounded-dag-variable-alistp dag-variable-alist dag-len))
             (mv-let (erp darg-trees dag-array dag-len dag-parent-array dag-variable-alist)
               (pseudo-terms-to-darg-trees terms dag-array dag-len dag-parent-array dag-variable-alist)
               (declare (ignore dag-array dag-len dag-parent-array dag-variable-alist))
               (implies (not erp)
                        (darg-tree-listp darg-trees))))
    :flag pseudo-terms-to-darg-trees))
