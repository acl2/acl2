; Computing the depth of DAG nodes
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

(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "dag-arrays")
(include-book "kestrel/acl2-arrays/aset1-list" :dir :system)
(local (include-book "numeric-lists"))
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/natp" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

;replace the other
;or make local?
(defthm all-<-of-+-of-1-and-maxelem-gen
  (implies (consp items)
           (all-< items (+ 1 (maxelem items))))
  :hints (("Goal" :in-theory (enable all-<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For each node, we get either its depth wrt some starting set of nodes, or
;; nil meaning it doesn't support the starting set of nodes:
(def-typed-acl2-array depth-arrayp (or (natp val) (not val)))

;; todo: def-typed-acl2-array could geneate this
(local
  (defthm depth-arrayp-of-make-empty-array-gen
    (implies (and (<= len2 len)
                  (<= len *max-1d-array-length*)
                  (natp len2)
                  (posp len)
                  (symbolp array-name))
             (depth-arrayp array-name (make-empty-array array-name len) len2))
    :hints (("Goal" :use depth-arrayp-of-make-empty-array
             :in-theory (disable depth-arrayp-of-make-empty-array)))))

(local
  (defthm depth-arrayp-of-aset1-list
    (implies (and (depth-arrayp array-name array array-len)
                  (or (natp val) (not val))
                  (all-< indices array-len)
                  (all-natp indices))
             (depth-arrayp array-name (aset1-list array-name array indices val) array-len))
    :hints (("Goal" :in-theory (enable aset1-list)))))

(local
  (defthm type-of-aref1-when-depth-arrayp-aux-alt
    (implies (and (depth-arrayp-aux array-name array top-index)
                  (<= index top-index)
                  (natp index)
                  (integerp top-index)
                  (aref1 array-name array index))
             (natp (aref1 array-name array index)))
    :hints (("Goal" :induct (depth-arrayp-aux array-name array top-index)
             :in-theory (enable depth-arrayp-aux)))))

;; ;no free var
;; ;drop?
;; (local
;;   (defthm type-of-aref1-when-depth-arrayp-aux-alt2
;;     (implies (and (depth-arrayp-aux array-name array index)
;;                   (natp index)
;;                   (aref1 array-name array index))
;;              (natp (aref1 array-name array index)))
;;     :hints (("Goal" :induct (depth-arrayp-aux array-name array top-index)
;;              :in-theory (enable depth-arrayp-aux)))))

(defthm type-of-aref1-when-depth-arrayp-alt
  (implies (and (depth-arrayp array-name array array-len)
                (< index array-len)
                (natp index)
                (aref1 array-name array index))
           (natp (aref1 array-name array index)))
  :hints (("Goal" :use (:instance type-of-aref1-when-depth-arrayp-aux (top-index (+ -1 array-len)))
           :in-theory (e/d (depth-arrayp)
                           (type-of-aref1-when-depth-arrayp-aux)))))

;; ; no free var
;; (defthm type-of-aref1-when-depth-arrayp-alt2
;;   (implies (and (depth-arrayp array-name array (+ 1 index))
;;                 (natp index)
;;                 (aref1 array-name array index))
;;            (natp (aref1 array-name array index)))
;;   :hints (("Goal" :use (:instance type-of-aref1-when-depth-arrayp-aux (top-index (+ -1 array-len)))
;;            :in-theory (e/d (depth-arrayp)
;;                            (type-of-aref1-when-depth-arrayp-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund set-depths-of-nodenums-if-lower (depth-array-name depth-array depth-array-len dargs new-depth)
  (declare (xargs :guard (and (natp new-depth)
                              (natp depth-array-len)
                              (depth-arrayp depth-array-name depth-array depth-array-len)
                              (bounded-darg-listp dargs depth-array-len))
                  :guard-hints (("Goal"
                                 :use (:instance TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP
                                                 (array-name DEPTH-ARRAY-NAME)
                                                 (array DEPTH-ARRAY)
                                                 (num-valid-indices DEPTH-ARRAY-len)
                                                 (index (CAR DARGS)))
                                 :in-theory (e/d (DEPTH-ARRAYP) (TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP))))))
  (if (endp dargs)
      depth-array
    (let* ((darg (first dargs))
           (depth-array (if (atom darg)
                            ;;darg is a nodenum:
                            (let ((depth (aref1 depth-array-name depth-array darg)))
                              (if (or (not depth)
                                      (< new-depth depth))
                                  (aset1 depth-array-name depth-array darg new-depth)
                                depth-array))
                          ;;darg is a quoted constant, so skip it:
                          depth-array)))
      (set-depths-of-nodenums-if-lower depth-array-name depth-array depth-array-len (rest dargs) new-depth))))

(local
  (defthm depth-arrayp-of-set-depths-of-nodenums-if-lower
    (implies (and ; (<= depth-array-len depth-array-len2)
               (natp new-depth)
               (natp depth-array-len)
               (natp depth-array-len2)
               (depth-arrayp depth-array-name depth-array depth-array-len)
               (bounded-darg-listp dargs depth-array-len))
             (depth-arrayp depth-array-name (set-depths-of-nodenums-if-lower depth-array-name depth-array depth-array-len2 dargs new-depth) depth-array-len))
    :hints (("Goal" :in-theory (enable  set-depths-of-nodenums-if-lower)))))

(local
  (defthm array1p-of-set-depths-of-nodenums-if-lower
    (implies (and ;; (natp new-depth)
               ;; (natp depth-array-len)
               ;; (natp depth-array-len2)
               ;; (<= depth-array-len depth-array-len2)
               (array1p depth-array-name depth-array)
               (bounded-darg-listp dargs (alen1 depth-array-name depth-array))
               )
             (array1p depth-array-name (set-depths-of-nodenums-if-lower depth-array-name depth-array depth-array-len2 dargs new-depth)))
    :hints (("Goal" :in-theory (enable bounded-darg-listp set-depths-of-nodenums-if-lower)))))

(local
  (defthm alen1-of-set-depths-of-nodenums-if-lower
    (implies (and ; (natp new-depth)
               (natp depth-array-len)
               ;;(depth-arrayp depth-array-name depth-array depth-array-len)
               (bounded-darg-listp dargs depth-array-len))
             (equal (alen1 depth-array-name (set-depths-of-nodenums-if-lower depth-array-name depth-array depth-array-len dargs new-depth))
                    (alen1 depth-array-name depth-array)))
    :hints (("Goal" :in-theory (enable set-depths-of-nodenums-if-lower)))))

(local
  (defthm default-of-set-depths-of-nodenums-if-lower
    (implies (and ; (natp new-depth)
               (natp depth-array-len)
               ;;(depth-arrayp depth-array-name depth-array depth-array-len)
               (bounded-darg-listp dargs depth-array-len))
             (equal (default depth-array-name (set-depths-of-nodenums-if-lower depth-array-name depth-array depth-array-len dargs new-depth))
                    (default depth-array-name depth-array)))
    :hints (("Goal" :in-theory (enable set-depths-of-nodenums-if-lower)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv depth-array largest-depth).
;go from node n down, tagging each node with its depth
;nodes with no depth are irrelevant (that is, do not support the starting node(s))
;the depth of a node is set when processing its parents
;; TODO: Consider using a worklist
(defund make-depth-array-aux (n
                              dag-array-name
                              dag-array
                              depth-array-name
                              depth-array
                              dag-len
                              ;; num-nodes-to-translate;BOZO could pass this in for efficiency?
                              largest-depth
                              )
  (declare (xargs :measure (nfix (+ 1 n))
                  :guard (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (integerp n)
                              (<= -1 n)
                              (< n dag-len)
                              (depth-arrayp depth-array-name depth-array (+ 1 n))
                              (< n (alen1 depth-array-name depth-array))
                              (natp LARGEST-DEPTH))
                  :guard-hints (("Goal"
                                 :use (:instance TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP
                                                 (array-name DEPTH-ARRAY-NAME)
                                                 (array DEPTH-ARRAY)
                                                 (num-valid-indices (+ 1 n))
                                                 (index n))
                                 :in-theory (disable TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP)))))
  (if (not (natp n))
      (mv depth-array largest-depth)
    (let ((expr (aref1 dag-array-name dag-array n)))
      ;; if its a variable or a quote, its depth was set by its parents (if any), so there is nothing to do
      (if (or (variablep expr)
              (fquotep expr))
          (make-depth-array-aux (+ -1 n) dag-array-name dag-array depth-array-name depth-array dag-len largest-depth)
        ;;it's a function call, so update the depths of its children:
        (let ((depth (aref1 depth-array-name depth-array n)))
          (if (not depth)
              ;; irrelevant node, so skip it
              (make-depth-array-aux (+ -1 n) dag-array-name dag-array depth-array-name depth-array dag-len largest-depth)
            (let ((new-depth (+ 1 depth))) ;subtle point: if all args are constants, there won't actually be a child at depth new-depth (probably not worth checking)
              (make-depth-array-aux (+ -1 n)
                                    dag-array-name dag-array depth-array-name
                                    (set-depths-of-nodenums-if-lower depth-array-name depth-array (+ 1 n) (dargs expr) new-depth)
                                    dag-len
                                    (max largest-depth new-depth)))))))))

(local
  (defthm alen1-of-mv-nth-0-of-make-depth-array-aux
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
;                (<= -1 n)
                  (< n dag-len)
                  (depth-arrayp depth-array-name depth-array (+ 1 n))
                  (< n (alen1 depth-array-name depth-array)))
             (equal (alen1 depth-array-name (mv-nth 0 (make-depth-array-aux n dag-array-name dag-array depth-array-name depth-array dag-len largest-depth)))
                    (alen1 depth-array-name depth-array)))
    :hints (("Goal" :in-theory (e/d (make-depth-array-aux NATP-OF-+-OF-1) (natp))))))

(local
  (defthm array1p-of-mv-nth-0-of-make-depth-array-aux
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
;               (<= -1 n)
                  (< n dag-len)
                  (depth-arrayp depth-array-name depth-array (+ 1 n))
                  (< n (alen1 depth-array-name depth-array)))
             (array1p depth-array-name (mv-nth 0 (make-depth-array-aux n dag-array-name dag-array depth-array-name depth-array dag-len largest-depth))))
    :hints (("Goal" :in-theory (e/d (make-depth-array-aux natp-of-+-of-1) (natp))))))

(local
  (defthm depth-arrayp-of-mv-nth-0-of-make-depth-array-aux
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
                  (< n dag-len)
                  (depth-arrayp depth-array-name depth-array num)
                  (natp num)
                  (< n num))
             (depth-arrayp depth-array-name (mv-nth 0 (make-depth-array-aux n dag-array-name dag-array depth-array-name depth-array dag-len largest-depth)) num))
    :hints (("Goal" :expand (DEPTH-ARRAYP DEPTH-ARRAY-NAME DEPTH-ARRAY N)
             :in-theory (e/d (make-depth-array-aux natp-of-+-of-1)
                             (natp))))))

(local
  (defthm integerp-of-mv-nth-1-of-make-depth-array-aux
    (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                  (integerp n)
                  (< n dag-len)
                  (depth-arrayp depth-array-name depth-array (+ 1 n))
                  (integerp largest-depth))
             (integerp (mv-nth 1 (make-depth-array-aux n dag-array-name dag-array depth-array-name depth-array dag-len largest-depth))))
    :hints (("Goal" :expand (DEPTH-ARRAYP DEPTH-ARRAY-NAME DEPTH-ARRAY N)
             :in-theory (e/d (make-depth-array-aux natp-of-+-of-1 integerp-when-natp)
                             (natp))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv depth-array largest-depth). In the resulting depth-array, nodes that do not support any of the STARTING-NODES have a value of nil.
;; The depth of a node is length of the shortest path to it from one of the designated nodes.
;; TODO: Should we use depth 0 instead of 1 for the starting-nodes themselves?
(defund make-depth-array-for-nodes (starting-nodes dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (all-natp starting-nodes)
                              (true-listp starting-nodes)
                              (consp starting-nodes) ;or else the maxelem below is a problem
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              ;(all-< starting-nodes *max-1d-array-length*)
                              (all-< starting-nodes dag-len))))
  (let* ((max-nodenum (maxelem starting-nodes))
         (depth-array (make-empty-array 'depth-array (+ 1 max-nodenum)))
         ;; Set the depth of all the STARTING-NODES to 1:
         (depth-array (aset1-list 'depth-array depth-array starting-nodes 1)))
    (make-depth-array-aux max-nodenum dag-array-name dag-array 'depth-array depth-array dag-len 1)))

(defthm alen1-of-mv-nth-0-of-make-depth-array-for-nodes
  (implies (and (all-natp starting-nodes)
                (true-listp starting-nodes)
                (consp starting-nodes) ;or else the maxelem below is a problem
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< starting-nodes dag-len))
           (equal (alen1 'depth-array (mv-nth 0 (make-depth-array-for-nodes starting-nodes dag-array-name dag-array dag-len)))
                  (+ 1 (maxelem starting-nodes))))
  :hints (("Goal" :in-theory (enable make-depth-array-for-nodes))))

(defthm array1p-of-mv-nth-0-of-make-depth-array-for-nodes
  (implies (and (all-natp starting-nodes)
                (true-listp starting-nodes)
                (consp starting-nodes)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< starting-nodes dag-len))
           (array1p 'depth-array (mv-nth 0 (make-depth-array-for-nodes starting-nodes dag-array-name dag-array dag-len))))
  :hints (("Goal" :in-theory (enable make-depth-array-for-nodes))))

(defthm depth-arrayp-of-mv-nth-0-of-make-depth-array-for-nodes
  (implies (and (all-natp starting-nodes)
                (true-listp starting-nodes)
                (consp starting-nodes)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< starting-nodes dag-len))
           (depth-arrayp 'depth-array
                         (mv-nth 0 (make-depth-array-for-nodes starting-nodes dag-array-name dag-array dag-len))
                         (+ 1 (maxelem starting-nodes))))
  :hints (("Goal" :in-theory (enable make-depth-array-for-nodes))))

(defthm depth-arrayp-of-mv-nth-0-of-make-depth-array-for-nodes-gen
  (implies (and (<= len (+ 1 (maxelem starting-nodes)))
                (natp len)
                (all-natp starting-nodes)
                (true-listp starting-nodes)
                (consp starting-nodes)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< starting-nodes dag-len))
           (depth-arrayp 'depth-array
                         (mv-nth 0 (make-depth-array-for-nodes starting-nodes dag-array-name dag-array dag-len))
                         len))
  :hints (("Goal" :use depth-arrayp-of-mv-nth-0-of-make-depth-array-for-nodes
           :in-theory (disable depth-arrayp-of-mv-nth-0-of-make-depth-array-for-nodes))))

(defthm integerp-of-mv-nth-1-of-make-depth-array-for-nodes-gen
  (implies (and (all-natp starting-nodes)
                (true-listp starting-nodes)
                (consp starting-nodes)
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< starting-nodes dag-len))
           (integerp (mv-nth 1 (make-depth-array-for-nodes starting-nodes dag-array-name dag-array dag-len))))
  :hints (("Goal" :in-theory (enable make-depth-array-for-nodes))))
