; More material on contexts
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

;; This book contains context-related material used by the Equivalence Checker but not the Rewriter.

(include-book "contexts")
(local (include-book "kestrel/acl2-arrays/acl2-arrays" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))

;could make tail rec
(defund get-not-done-nodes (nodenums done-array)
  (declare (xargs :guard (and (array1p 'done-array-for-context done-array)
                              (nat-listp nodenums)
                              (all-< nodenums (alen1 'done-array-for-context done-array)))))
  (if (endp nodenums)
      nil
    (let ((nodenum (first nodenums)))
      (if (aref1 'done-array-for-context done-array nodenum)
          (get-not-done-nodes (rest nodenums) done-array)
        (cons nodenum (get-not-done-nodes (rest nodenums) done-array))))))

(local
  (defthm nat-listp-of-get-not-done-nodes
    (implies (nat-listp nodenums)
             (nat-listp (get-not-done-nodes nodenums done-array)))
    :hints (("Goal" :in-theory (enable get-not-done-nodes)))))

(local
  (defthm all-<-of-get-not-done-nodes
    (implies (all-< nodenums val)
             (all-< (get-not-done-nodes nodenums done-array) val))
    :hints (("Goal" :in-theory (enable get-not-done-nodes)))))

;;fixme what if there is a node with no parents?!
;fills in CONTEXT-ARRAY for the nodenums in WORKLIST and all of their ancestors
(defun make-context-array-for-ancestors (count worklist dag-array-name dag-array dag-len dag-parent-array context-array done-array)
  (declare (xargs :measure (nfix (+ 1 count))
                  :guard (and (integerp count) ; may go down to -1
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (nat-listp worklist)
                              (all-< worklist dag-len)
                              (dag-parent-arrayp 'dag-parent-array-for-context dag-parent-array)
                              (equal (alen1 'dag-parent-array-for-context dag-parent-array)
                                     dag-len)
                              (bounded-dag-parent-entriesp (+ -1 dag-len) 'dag-parent-array-for-context dag-parent-array dag-len)
                              (context-arrayp 'context-array context-array dag-len) ; needed for set-context-of-nodenum
                              (array1p 'done-array-for-context done-array)
                              (equal (alen1 'done-array-for-context done-array)
                                     dag-len))
                  :guard-hints (("Goal" :in-theory (enable dag-parent-arrayp <-of-+-of-1-strengthen-2)))))
  (if (not (natp count))
      (prog2$ (er hard? 'make-context-array-for-ancestors "Limit reached.")
              context-array)
    (if (endp worklist)
        context-array
      (let ((nodenum (first worklist)))
        (if (aref1 'done-array-for-context done-array nodenum)
            ;; this node is already done:
            (make-context-array-for-ancestors (+ -1 count) (rest worklist) dag-array-name dag-array dag-len dag-parent-array context-array done-array)
          ;;node isn't done yet (and isn't the top node since that one is always done):
          (let* ((parent-nodenums (aref1 'dag-parent-array-for-context dag-parent-array nodenum))
                 (not-done-parents (get-not-done-nodes parent-nodenums done-array)))
            (if not-done-parents
                ;; do the parents first (will reprocess this node after the parents are done):
                (make-context-array-for-ancestors (+ -1 count) (append not-done-parents worklist) dag-array-name dag-array dag-len dag-parent-array context-array done-array)
              ;;all parents are done, so now we can handle this node:
              (make-context-array-for-ancestors (+ -1 count)
                                                (rest worklist) dag-array-name dag-array dag-len dag-parent-array
                                                (set-context-of-nodenum nodenum parent-nodenums dag-array-name dag-array dag-len context-array)
                                                (aset1 'done-array-for-context done-array nodenum t)))))))))

(local
  (defthm make-context-array-for-ancestors-return-type
    (implies (and (integerp count) ; may go down to -1
                  (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (nat-listp worklist)
                  (all-< worklist dag-len)
                  (dag-parent-arrayp 'dag-parent-array-for-context dag-parent-array)
                  (equal (alen1 'dag-parent-array-for-context dag-parent-array)
                         dag-len)
                  (bounded-dag-parent-entriesp (+ -1 dag-len) 'dag-parent-array-for-context dag-parent-array dag-len)
                  (context-arrayp 'context-array context-array dag-len) ; needed for set-context-of-nodenum
                  (array1p 'done-array-for-context done-array)
                  (equal (alen1 'done-array-for-context done-array)
                         dag-len))
             (and (array1p 'context-array (make-context-array-for-ancestors count worklist dag-array-name dag-array dag-len dag-parent-array context-array done-array))
                  (equal (alen1 'context-array (make-context-array-for-ancestors count worklist dag-array-name dag-array dag-len dag-parent-array context-array done-array))
                         (alen1 'context-array context-array))))
    :hints (("Goal" :in-theory (enable make-context-array-for-ancestors)))))

;returns the context for NODENUM (to compute it, this first computes the contexts for all of its ancestors)
;would be faster if we could pass in a parent array instead of making it here
;smashes 'context-array and 'dag-parent-array-for-context and 'done-array-for-context
(defun get-context-for-nodenum (nodenum dag-array-name dag-array
                                        dag-len ; better would be to pass the top-nodenum since that context computation starts there?
                                        )
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (posp dag-len)
                              (natp nodenum)
                              (< nodenum dag-len))))
  (let* ((dag-parent-array (make-minimal-dag-parent-array-with-name dag-len dag-array-name dag-array 'dag-parent-array-for-context)) ; todo: only compute parents for nodes above nodenum?
         ;; Top node has no context (only the value for top-nodenum here will actually be used):
         (context-array (make-empty-array-with-default 'context-array dag-len (true-context)))
         (top-nodenum (+ -1 dag-len))
         (done-array (make-empty-array 'done-array-for-context dag-len))
         (done-array (aset1 'done-array-for-context done-array top-nodenum t)) ; mark top node as done
         (context-array (make-context-array-for-ancestors 1000000000
                                                          (list nodenum) ;initial worklist
                                                          dag-array-name
                                                          dag-array
                                                          dag-len
                                                          dag-parent-array
                                                          context-array
                                                          done-array)))
    (aref1 'context-array context-array nodenum)))
