; More material on contexts
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

;; This book contains context-related material used by the Equivalence Checker but not the Rewriter.

;; TODO: Deal with skip-proofs

;; TODO: Need to handle the presence of :default in this kind of context array

(include-book "kestrel/axe/contexts" :dir :system)
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;could make tail rec
;rename?
(defund get-not-done-nodes (nodenums context-array)
  (declare (xargs :guard (and (array1p 'context-array context-array)
                              (true-listp nodenums)
                              (all-natp nodenums)
                              (all-< nodenums (alen1 'context-array context-array)))))
  (if (endp nodenums)
      nil
    (let* ((nodenum (first nodenums))
           (context (aref1 'context-array context-array nodenum)))
      (if (eq :default context)
          (cons nodenum (get-not-done-nodes (rest nodenums) context-array))
        (get-not-done-nodes (rest nodenums) context-array)))))

(defthm all-natp-of-get-not-done-nodes
  (implies (all-natp nodenums)
           (all-natp (get-not-done-nodes nodenums context-array)))
  :hints (("Goal" :in-theory (enable get-not-done-nodes))))

(defthm all-<-of-get-not-done-nodes
  (implies (all-< nodenums val)
           (all-< (get-not-done-nodes nodenums context-array) val))
  :hints (("Goal" :in-theory (enable get-not-done-nodes))))

;;fixme what if there is a node with no parents?!
;fills in CONTEXT-ARRAY for the nodenums in WORKLIST and all of their ancestors
(defun make-context-array-for-ancestors (count worklist dag-array-name dag-array dag-len top-nodenum dag-parent-array context-array)
  (declare (xargs :measure (nfix (+ 1 count))
                  :guard (and (integerp count)
                              (natp top-nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< top-nodenum dag-len)
                              (true-listp worklist)
                              (all-natp worklist)
                              (all-< worklist (+ 1 top-nodenum))
                              (dag-parent-arrayp 'dag-parent-array-for-context dag-parent-array)
                              (equal (alen1 'dag-parent-array-for-context dag-parent-array)
                                     (alen1 dag-array-name dag-array))
                              (bounded-dag-parent-entriesp top-nodenum 'dag-parent-array-for-context dag-parent-array (+ 1 top-nodenum))
                              (context-arrayp 'context-array context-array dag-len))
                  :guard-hints (("Goal" :in-theory (enable dag-parent-arrayp <-of-+-of-1-strengthen-2)))))
  (if (not (natp count))
      (prog2$ (er hard? 'make-context-array-for-ancestors "Limit reached.")
              context-array)
    (if (endp worklist)
        context-array
      (let* ((nodenum (first worklist))
             (context (aref1 'context-array context-array nodenum)))
        (if (not (eq :default context))
            ;;this node is already done
            (make-context-array-for-ancestors (+ -1 count) (rest worklist) dag-array-name dag-array dag-len top-nodenum dag-parent-array context-array)
          (if (eql nodenum top-nodenum)
              ;;it's the top node:
              (make-context-array-for-ancestors (+ -1 count) (rest worklist) dag-array-name dag-array dag-len top-nodenum dag-parent-array
                                                (aset1 'context-array context-array nodenum (true-context))) ;don't know any context preds for the top node
            ;;node isn't done yet (and isn't the top node):
            (let* ((parent-nodenums (aref1 'dag-parent-array-for-context dag-parent-array nodenum))
                   (not-done-parents (get-not-done-nodes parent-nodenums context-array)))
              (if not-done-parents
                  ;; do the parents first (will reprocess this node after the parents are done):
                  (make-context-array-for-ancestors (+ -1 count) (append not-done-parents worklist) dag-array-name dag-array dag-len top-nodenum dag-parent-array context-array)
                ;;all parents are done:
                (make-context-array-for-ancestors (+ -1 count)
                                                  (rest worklist) dag-array-name dag-array dag-len top-nodenum dag-parent-array
                                                  (set-context-of-nodenum nodenum parent-nodenums dag-array-name dag-array dag-len context-array))))))))))

;returns the context for NODENUM (to compute it, this first computes the contexts for all of its ancestors)
;would be faster if we could pass in a parent array instead of making it here
;smashes 'context-array
(defun get-context-for-nodenum (nodenum dag-array-name dag-array dag-len ;tag-array2
                                        )
;  (declare (ignore tag-array2)) ;we could perhaps use this to not consider context nodes that we still think are probably equal to other things?  maybe this all is fast enough now that we don't need to do that
  (declare (xargs :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (posp dag-len)
                              (natp nodenum)
                              ;(< nodenum dag-len)
                              )
                  :verify-guards nil ;perhaps not true, due to the use of default
                  ))
  (let* ((dag-parent-array (make-dag-parent-array-with-name dag-len dag-array-name dag-array 'dag-parent-array-for-context)) ;ffixme only compute parents for nodes above nodenum?
         (context-array (make-empty-array-with-default 'context-array dag-len :default)) ;todo: using :default here makes it not a valid context-array!
         (context-array (make-context-array-for-ancestors 1000000000
                                                          (list nodenum) ;initial worklist
                                                          dag-array-name
                                                          dag-array
                                                          dag-len
                                                          (+ -1 dag-len) ;top nodenum
                                                          dag-parent-array
                                                          context-array)))
    (aref1 'context-array context-array nodenum)))

(skip-proofs (verify-guards get-context-for-nodenum)) ;need properties of MAKE-CONTEXT-ARRAY-FOR-ANCESTORS
