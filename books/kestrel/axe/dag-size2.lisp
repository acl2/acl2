; DAG size tools dealing only with relevant nodes
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

;; This book deals with computing the size of some, but not necessarily all,
;; nodes in a DAG.  See also dag-size.lisp.

(include-book "dag-arrays")
(include-book "numeric-lists")
(include-book "worklist-array")
(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "all-dargp")
(local (include-book "merge-sort-less-than-rules"))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(in-theory (disable bounded-dag-exprp)) ;move?

(local (in-theory (enable not-<-of-car-when-all-<)))

;todo: rename to aref1-list?
;not tail-rec..
(defund lookup-lst-array (array-name array indices)
  (declare (xargs :guard (and (all-natp indices)
                              (true-listp indices)
                              (array1p array-name array)
                              (all-< indices (alen1 array-name array))
                              )))
  (if (endp indices)
      nil
    (cons (aref1 array-name array (car indices))
          (lookup-lst-array array-name array (cdr indices)))))

(defund sum-list-tail-aux (lst acc)
  (declare (xargs :guard (and (true-listp lst)
                              ;(all-integerp lst)
                              (acl2-numberp acc))))
  (if (endp lst)
      acc
    (sum-list-tail-aux (rest lst)
                       (+ (fix (first lst)) ;todo: avoid the fix (but we'll need to show that the entries in the size array are ok)
                          acc))))

(defthm integerp-of-sum-list-tail-aux
  (implies (and (all-integerp vals)
                (integerp acc))
           (integerp (sum-list-tail-aux vals acc)))
  :hints (("Goal" :in-theory (enable sum-list-tail-aux all-integerp))))

(defund sum-list-tail (lst)
  (declare (xargs :guard (and (true-listp lst)
;                              (all-integerp lst)  ;weaken
                              )))
  (sum-list-tail-aux lst 0))

(defthm integerp-of-sum-list-tail
  (implies (all-integerp vals)
           (integerp (sum-list-tail vals)))
  :hints (("Goal" :in-theory (enable sum-list-tail))))

;used for the size array
;; todo: consider using def-typed-acl2-array
(defun array-has-integer-valuesp (array-name array top-nodenum-to-check)
  (declare (xargs :measure (nfix (+ 1 top-nodenum-to-check))
                  :guard (and (array1p array-name array)
                              (integerp top-nodenum-to-check)
                              (< top-nodenum-to-check
                                 (alen1 array-name array)))))
  (if (not (natp top-nodenum-to-check))
      t
    (let ((expr (aref1 array-name array top-nodenum-to-check)))
      (and (integerp expr)
           (array-has-integer-valuesp array-name
                                      array (+ -1 top-nodenum-to-check))))))

(defthm array-has-integer-valuesp-of-aset1
  (implies (and (integerp val)
                (array-has-integer-valuesp array-name array top-nodenum-to-check)
                (< n (alen1 array-name array))
                (natp n)
                (< top-nodenum-to-check (alen1 array-name array))
                (integerp top-nodenum-to-check)
                (<= -1 top-nodenum-to-check)
                (array1p array-name array))
           (array-has-integer-valuesp array-name (aset1 array-name array n val) top-nodenum-to-check)))

(defthm integerp-of-aref1-when-array-has-integer-valuesp
  (implies (and (array-has-integer-valuesp array-name array top-nodenum-to-check)
                (natp index)
                (<= index top-nodenum-to-check)
                (natp top-nodenum-to-check))
           (integerp (aref1 array-name array index)))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors))))

(defthm all-integerp-of-lookup-lst-array
  (implies (and (array-has-integer-valuesp array-name array top-nodenum-to-check)
                (all-natp indices)
                (all-<= indices top-nodenum-to-check)
                (integerp top-nodenum-to-check)
                )
           (all-integerp (lookup-lst-array array-name array indices)))
  :hints (("Goal" :induct (lookup-lst-array array-name array indices)
           :in-theory (enable lookup-lst-array
                              not-negative-when-all-<=-and-all-natp)
           :do-not '(generalize eliminate-destructors))))

;; This version of the size machiney supports calculating the size for only
;; some of the nodes in a DAG.

;; The nodes in the worklist are always sorted.  We say we "examine" a node when
;; we add its not-already-examined children in sorted order before it on the
;; worklist.  They will be fully processed before we return to the node.  A
;; node affected by this algorithm in general moves through the following 4 states over time:
;;   1. untouched (not on worklist, unexamined)
;;   2. on worklist and unexamined (e.g., while smaller children of its parent are being processed)
;;   3. on worklist and examined (e.g., while its own children are being processed)
;;   4. done (no longer on worklist but marked as examined).
;; Keeping the worklist sorted means we avoid adding an item to it more than
;; once. (We avoid the case where we process a larger child that depends on a
;; smaller sibling before we process that sibling.)

;populates size-array with the size of every node in worklist (and every supporting node), but not necessarily all nodes
;; TODO: Consider combining the size-array and the worklist-array, since :examined is not a valid size.
;; TODO: Explicate the relationship between the worklist-array, size-array, and
;; worklist (for any :examined node, all its descendants are either on the
;; worklist or have a valid entry in the size-array).
(defund size-array-for-nodes-aux (worklist ;must be sorted
                                  dag-array-name dag-array dag-len
                                  size-array-name size-array ;; tracks the results being computed
                                  worklist-array ;; tracks the status of nodes (whether they are :examined)
                                  )
  (declare (xargs :guard (and (array1p size-array-name size-array) ;; need to say that it contains integers or nil
                              (array1p 'worklist-array worklist-array) ;maps nodes to :examined or nil
                              (true-listp worklist)
                              (all-natp worklist)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (<= (alen1 size-array-name size-array) dag-len)
                              (= (alen1 'worklist-array worklist-array)
                                 (alen1 size-array-name size-array))
                              (all-< worklist (alen1 'worklist-array worklist-array)))
                  ;;measure is: first, the number of examined nodes, then the length of the worklist
                  :measure (make-ord 1 (+ 1 (- (nfix (alen1 'worklist-array worklist-array))
                                               (num-examined-nodes (+ -1 (alen1 'worklist-array worklist-array))
                                                                   'worklist-array worklist-array)))
                                     (len worklist))
                  :guard-hints (("Goal" :do-not-induct t
                                 :do-not '(generalize eliminate-destructors)
                                 :in-theory (e/d ()
                                                 (consp-from-len-cheap
                                                  dag-exprp0))))))
  (if (or (endp worklist)
          ;; for termination:
          (not (and (mbt (array1p 'worklist-array worklist-array))
                    (mbt (all-natp worklist))
                    (mbt (all-< worklist (alen1 'worklist-array worklist-array))))))
      size-array
    (let* ((nodenum (first worklist))
           (expr (aref1 dag-array-name dag-array nodenum)))
      (if (or (variablep expr)
              (fquotep expr))
          ;;variables and constants have size 1
          (size-array-for-nodes-aux (rest worklist) dag-array-name dag-array dag-len
                                    size-array-name
                                    (aset1 size-array-name size-array nodenum 1)
                                    ;; We mark the node as "examined" so it doesn't get added again:
                                    (aset1 'worklist-array worklist-array nodenum :examined))
        ;; it's a function call:
        (let ((res (aref1 'worklist-array worklist-array nodenum)))
          (if (eq res :examined)
              ;; The node has been examined, and since we are back to handling
              ;; it again, we know that its children have already been examined
              ;; and their sizes computed. So now we can compute its size.
              ;; TODO: Use add-arg-sizes here?
              (let* ((args (dargs expr))
                     (nodenum-args (keep-atoms args)) ;; todo: avoid consing up this list?
                     (num-quotep-args (- (len args) (len nodenum-args)))
                     (arg-sizes (lookup-lst-array size-array-name size-array nodenum-args)) ;; todo: avoid consing up this list?
                     (arg-sum (sum-list-tail arg-sizes)))
                (size-array-for-nodes-aux (rest worklist)
                                          dag-array-name dag-array dag-len
                                          size-array-name
                                          ;; add the sizes of the children, add 1 for each constant arg, and add 1 for the node itself:
                                          (aset1 size-array-name size-array nodenum (+ 1 arg-sum num-quotep-args))
                                          worklist-array))
            ;; Node is on the worklist but unexamined.  Its children can't be
            ;; on the worklist, because this node is the smallest node in the
            ;; worklist (recall that the worklist is sorted).  So each child is
            ;; either untouched or done.  That is, this node's children have
            ;; not necessarily been processed, but if they've been examined,
            ;; they've been fully processed.
            (let* ((unexamined-args (get-unexamined-nodenum-args (dargs expr) worklist-array nil)) ;todo: combine these 2 steps
                   ;; TODO: optimize the case where unexamined-args is nil
                   (sorted-unexamined-args (merge-sort-< unexamined-args)))
              (size-array-for-nodes-aux (append sorted-unexamined-args worklist) ;still sorted
                                        dag-array-name dag-array dag-len
                                        size-array-name
                                        size-array
                                        (aset1 'worklist-array worklist-array nodenum :examined)))))))))

;; ;populates size-array with the size of every node in worklist (and every supporting node), but not necessarily all nodes
;; (defund size-array-for-nodes-aux (steps-left ;forces termination
;;                                   worklist dag-array-name dag-array dag-len size-array-name size-array)
;;   (declare (xargs :guard (and (array1p size-array-name size-array) ;; need to say that it contains integers or nil
;;                               (true-listp worklist)
;;                               (all-natp worklist)
;;                               (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                               ;;todo: weaken (allow the DAG to be bigger than the highest node we are working with)?:
;;                               (eql (alen1 dag-array-name dag-array)
;;                                    (alen1 size-array-name size-array))
;;                               (all-< worklist dag-len)
;;                               (natp steps-left))
;;                   :guard-hints (("Goal" :do-not-induct t
;;                                  ;; :use (:instance TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX
;;                                  ;;                 (N (CAR WORKLIST))
;;                                  ;;                 (DAG-ARRAY DAG-ARRAY)
;;                                  ;;                 (DAG-ARRAY-NAME DAG-ARRAY-NAME)
;;                                  ;;                 (TOP-NODENUM-TO-CHECK (+ -1 dag-len)))
;;                                  :do-not '(generalize eliminate-destructors)
;;                                  ;;:cases ((equal 0 dag-len))
;;                                  :in-theory (e/d () (CONSP-FROM-LEN-CHEAP
;;                                                      sum-list-tail ;consp-cdr
;;                                                      KEEP-ATOMS
;;                                                      MAXELEM
;;                                                      dag-exprp0
;;                                                      TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))))))
;;   (if (or (not (natp steps-left))
;;           (equal 0 steps-left))
;;       (prog2$ (er hard? 'size-array-for-nodes-aux "Reached step limit (should not happen).")
;;               size-array)
;;     (if (endp worklist)
;;         size-array
;;       (let* ((nodenum (first worklist)))
;;         (if (aref1 size-array-name size-array nodenum) ;already done:
;;             (size-array-for-nodes-aux (+ -1 steps-left) (rest worklist) dag-array-name dag-array dag-len size-array-name size-array)
;;           (let ((expr (aref1 dag-array-name dag-array nodenum)))
;;             (if (or (variablep expr)
;;                     (fquotep expr))
;;                 ;;variables and constants have size 1
;;                 (size-array-for-nodes-aux (+ -1 steps-left)
;;                                           (rest worklist) dag-array-name dag-array dag-len
;;                                           size-array-name
;;                                           (aset1 size-array-name size-array nodenum 1))
;;               ;;function call:
;;               (let* ((args (dargs expr))
;;                      (extended-worklist-or-nil (get-args-not-done args size-array-name size-array worklist nil)))
;;                 (if extended-worklist-or-nil
;;                     ;; Handle the arguments first (eventually we'll come back to this node):
;;                     (size-array-for-nodes-aux (+ -1 steps-left) extended-worklist-or-nil dag-array-name dag-array dag-len size-array-name size-array)
;;                   ;;all args are done:
;;                   (let* ((nodenums (keep-atoms args)) ;fixme don't bother to cons up this list?
;;                          (num-quotep-args (- (len args) (len nodenums)))
;;                          (arg-sizes (lookup-lst-array size-array-name size-array nodenums)) ;fixme don't bother to cons up this list?
;;                          (arg-sum (sum-list-tail arg-sizes)))
;;                     (size-array-for-nodes-aux (+ -1 steps-left)
;;                                               (rest worklist) dag-array-name dag-array dag-len
;;                                               size-array-name
;;                                               (aset1 size-array-name size-array nodenum (+ 1
;;                                                                                            arg-sum
;;                                                                                            num-quotep-args)))))))))))))

(defthm alen1-of-size-array-for-nodes-aux
  (implies (and (all-natp worklist)
                (true-listp worklist)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< worklist dag-len)
                (<= (alen1 size-array-name size-array) dag-len)
                )
           (equal (alen1 size-array-name (size-array-for-nodes-aux worklist dag-array-name dag-array dag-len size-array-name size-array worklist-array))
                  (alen1 size-array-name size-array)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable size-array-for-nodes-aux))))

(defthm array1p-of-size-array-for-nodes-aux
  (implies (and (all-natp worklist)
                (true-listp worklist)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< worklist (alen1 size-array-name size-array))
                (<= (alen1 size-array-name size-array)
                    dag-len)
                (array1p size-array-name size-array))
           (array1p size-array-name (size-array-for-nodes-aux worklist dag-array-name dag-array dag-len size-array-name size-array worklist-array)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable size-array-for-nodes-aux))))

;populates size-array with the size of every node in NODENUMS (and every supporting node), but not necessarily all nodes
(defund size-array-for-sorted-nodes (nodenums ;must be sorted
                                     dag-array-name dag-array dag-len size-array-name-to-use)
  (declare (xargs :guard (and (all-natp nodenums)
                              (true-listp nodenums)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (<= (alen1 dag-array-name dag-array)
                                  2147483646)
                              (all-< nodenums dag-len)
                              (consp nodenums) ;since we call maxelem
                              (symbolp size-array-name-to-use))))
  (b* ((worklist-array (make-empty-array 'worklist-array
                                         dag-len ;; todo: use this instead: (+ 1 max-nodenum) but change the guard of size-array-for-nodes-aux first.
                                         ))
       (size-array (make-empty-array size-array-name-to-use
                                     dag-len ;; todo: use this instead: (+ 1 max-nodenum) but change the guard of size-array-for-nodes-aux first.
                                     )))
    (size-array-for-nodes-aux nodenums ;initial worklist must be sorted
                              dag-array-name dag-array dag-len size-array-name-to-use size-array worklist-array)))

(defthm alen1-of-size-array-for-sorted-nodes
  (implies (and (all-natp nodenums)
                (true-listp nodenums)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< nodenums dag-len)
                (symbolp size-array-name-to-use)
                (posp dag-len))
           (equal (alen1 size-array-name-to-use (size-array-for-sorted-nodes nodenums dag-array-name dag-array dag-len size-array-name-to-use))
                  dag-len))
  :hints (("Goal" :in-theory (enable size-array-for-sorted-nodes))))

(defthm array1p-of-size-array-for-sorted-nodes
  (implies (and (all-natp nodenums)
                (true-listp nodenums)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< nodenums dag-len)
                (symbolp size-array-name-to-use)
                (posp dag-len))
           (array1p size-array-name-to-use
                    (size-array-for-sorted-nodes nodenums
                                                 dag-array-name
                                                 dag-array dag-len size-array-name-to-use)))
  :hints (("Goal" :in-theory (enable size-array-for-sorted-nodes))))

;populates size-array with the size of every node in NODENUMS (and every supporting node), but not necessarily all nodes
(defund size-array-for-nodes (nodenums dag-array-name dag-array dag-len size-array-name-to-use)
  (declare (xargs :guard (and (all-natp nodenums)
                              (true-listp nodenums)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (<= (alen1 dag-array-name dag-array)
                                  2147483646)
                              (all-< nodenums dag-len)
                              (consp nodenums) ;since we call maxelem
                              (symbolp size-array-name-to-use))))
  (size-array-for-sorted-nodes (merge-sort-< nodenums)
                               dag-array-name dag-array dag-len size-array-name-to-use))

;; (defund size-array-for-nodes (nodenums dag-array-name dag-array dag-len size-array-name-to-use)
;;   (declare (xargs :guard (and (all-natp nodenums)
;;                               (true-listp nodenums)
;;                               (pseudo-dag-arrayp dag-array-name dag-array dag-len)
;;                               (<= (alen1 dag-array-name dag-array)
;;                                   2147483646)
;;                               (all-< nodenums dag-len)
;;                               (consp nodenums) ;since we call maxelem
;;                               (symbolp size-array-name-to-use))))
;;   (b* ((max-nodenum (maxelem nodenums))
;;        (size-array (make-empty-array size-array-name-to-use
;;                                      (alen1 dag-array-name dag-array) ;; todo: use this instead: (+ 1 max-nodenum) but change the guard of size-array-for-nodes-aux first.
;;                                      ))
;;        (termination-bound (* 10 (+ 1 (if (consp nodenums) max-nodenum 1))) ;todo: think about this bound
;;                           ))
;;     (size-array-for-nodes-aux termination-bound nodenums dag-array-name dag-array dag-len size-array-name-to-use size-array)))

(defthm alen1-of-size-array-for-nodes
  (implies (and (all-natp nodenums)
                (true-listp nodenums)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< nodenums dag-len)
                (symbolp size-array-name-to-use)
                (posp dag-len))
           (equal (alen1 size-array-name-to-use (size-array-for-nodes nodenums dag-array-name dag-array dag-len size-array-name-to-use))
                  dag-len))
  :hints (("Goal" :in-theory (enable size-array-for-nodes))))

(defthm array1p-of-size-array-for-nodes
  (implies (and (all-natp nodenums)
                (true-listp nodenums)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< nodenums dag-len)
                (symbolp size-array-name-to-use)
                (posp dag-len))
           (array1p size-array-name-to-use
                    (size-array-for-nodes nodenums
                                          dag-array-name
                                          dag-array dag-len size-array-name-to-use)))
  :hints (("Goal" :in-theory (enable size-array-for-nodes))))

;; Return the size of node NODENUM in the DAG-ARRAY, which must be named
;; DAG-ARRAY-NAME.  Destroys 'size-array.  This should be pretty efficient, but
;; it does build an array.
(defund size-of-node (nodenum dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (array1p dag-array-name dag-array)
                              (<= (alen1 dag-array-name dag-array)
                                  2147483646)
                              (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (< nodenum dag-len))
                  :guard-hints (("Goal" :in-theory (enable)))))
  (let* ((size-array-name 'size-array)
         (size-array (size-array-for-nodes (list nodenum) dag-array-name dag-array dag-len size-array-name)))
    (aref1 size-array-name size-array nodenum)))
