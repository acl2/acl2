; Trees whose leaves are DAG function arguments ("dargs")
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "darg-trees")

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
