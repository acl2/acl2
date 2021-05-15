; Computing the depth of DAG nodes
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

(include-book "kestrel/acl2-arrays/typed-acl2-arrays" :dir :system)
(include-book "dag-arrays")
(include-book "kestrel/acl2-arrays/aset1-list" :dir :system)
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(def-typed-acl2-array depth-arrayp (or (natp val) (not val)))

(DEFTHM TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP-AUX-alt
  (IMPLIES (AND (DEPTH-ARRAYP-AUX ARRAY-NAME ARRAY TOP-INDEX)
                (<= INDEX TOP-INDEX)
                (NATP INDEX)
                (INTEGERP TOP-INDEX)
                (AREF1 ARRAY-NAME ARRAY INDEX))
           (NATP (AREF1 ARRAY-NAME ARRAY INDEX)))
  :HINTS (("Goal" :INDUCT (DEPTH-ARRAYP-AUX ARRAY-NAME ARRAY TOP-INDEX)
           :IN-THEORY (ENABLE DEPTH-ARRAYP-AUX))))

(DEFTHM TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP-alt
  (IMPLIES (AND (DEPTH-ARRAYP ARRAY-NAME ARRAY ARRAY-LEN)
                (< INDEX ARRAY-LEN)
                (NATP INDEX)
                (AREF1 ARRAY-NAME ARRAY INDEX))
           (NATP (AREF1 ARRAY-NAME ARRAY INDEX)))
  :HINTS (("Goal" :USE (:INSTANCE TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP-AUX
                                  (TOP-INDEX (+ -1 ARRAY-LEN)))
           :IN-THEORY (E/D (DEPTH-ARRAYP)
                           (TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP-AUX)))))

;items are nodenums or quoteps
(defund set-depths-of-nodenums-if-lower (depth-array-name new-depth items depth-array depth-array-len)
  (declare (xargs :guard (and (natp new-depth)
                              (natp depth-array-len)
                              (depth-arrayp depth-array-name depth-array depth-array-len)
                              (all-dargp-less-than items depth-array-len)
                              (true-listp items))
                  :guard-hints (("Goal"
                                 :use (:instance TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP
                                                 (array-name DEPTH-ARRAY-NAME)
                                                 (array DEPTH-ARRAY)
                                                 (num-valid-nodes DEPTH-ARRAY-len)
                                                 (index (CAR ITEMS)))
                                 :in-theory (e/d (DEPTH-ARRAYP) (TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP))))))
  (if (endp items)
      depth-array
    (let ((item (first items)))
      (if (atom item)
          ;;item is a nodenum:
          (let ((depth (aref1 depth-array-name depth-array item)))
            (if (or (not depth)
                    (< new-depth depth))
                (set-depths-of-nodenums-if-lower depth-array-name new-depth (rest items) (aset1 depth-array-name depth-array item new-depth) depth-array-len)
              (set-depths-of-nodenums-if-lower depth-array-name new-depth (rest items) depth-array depth-array-len)))
        ;;item is a quoted constant, so skip it:
        (set-depths-of-nodenums-if-lower depth-array-name new-depth (rest items) depth-array depth-array-len)))))

(defthm depth-arrayp-of-set-depths-of-nodenums-if-lower
  (implies  (and (natp new-depth)
                 (natp depth-array-len)
                 (natp depth-array-len2)
                 (<= depth-array-len depth-array-len2)
                 (depth-arrayp depth-array-name depth-array depth-array-len)
                 (all-dargp-less-than items depth-array-len)
                 (true-listp items))
            (depth-arrayp depth-array-name (set-depths-of-nodenums-if-lower depth-array-name new-depth items depth-array depth-array-len2) depth-array-len))
  :hints (("Goal" :in-theory (enable  set-depths-of-nodenums-if-lower))))

(defthm alen1-of-set-depths-of-nodenums-if-lower
  (implies  (and (natp new-depth)
                 (natp depth-array-len)
                 (depth-arrayp depth-array-name depth-array depth-array-len)
                 (all-dargp-less-than items depth-array-len)
                 (true-listp items))
            (equal (alen1 depth-array-name (set-depths-of-nodenums-if-lower depth-array-name new-depth items depth-array depth-array-len))
                   (alen1 depth-array-name depth-array)))
  :hints (("Goal" :in-theory (enable set-depths-of-nodenums-if-lower))))

;; Returns (mv depth-array largest-depth)
;go from node n down, tagging each node with its depth
;nodes with no depth are irrelevant (that is, do not support the top node(s))
;the depth of a node is set when processing its parents
;fixme use a worklist?
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
                                                 (num-valid-nodes (+ 1 n))
                                                 (index n))
                                 :in-theory (e/d ()
                                                 (TYPE-OF-AREF1-WHEN-DEPTH-ARRAYP))))))
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
              ;;irrelevant node, so skip it
              (make-depth-array-aux (+ -1 n) dag-array-name dag-array depth-array-name depth-array dag-len largest-depth)
            (let ((new-depth (+ 1 depth))) ;subtle point: if all args are constants, there won't actually be a child at depth new-depth (probably not worth checking)
              (make-depth-array-aux (+ -1 n)
                                    dag-array-name dag-array depth-array-name
                                    (set-depths-of-nodenums-if-lower depth-array-name new-depth (dargs expr) depth-array (+ 1 n))
                                    dag-len
                                    (max largest-depth new-depth)))))))))

(defthm alen1-of-mv-nth-0-of-make-depth-array-aux
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (integerp n)
                (<= -1 n)
                (< n dag-len)
                (depth-arrayp depth-array-name depth-array (+ 1 n))
                (< n (alen1 depth-array-name depth-array)))
           (equal (alen1 depth-array-name (mv-nth 0 (make-depth-array-aux n
                                                                          dag-array-name
                                                                          dag-array
                                                                          depth-array-name
                                                                          depth-array
                                                                          dag-len
                                                                          largest-depth
                                                                          )))
                  (alen1 depth-array-name depth-array)))
  :hints (("Goal" :in-theory (e/d (make-depth-array-aux NATP-OF-+-OF-1) (natp)))))

(defthm array1p-of-mv-nth-0-of-make-depth-array-aux
  (implies (and (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (integerp n)
                (<= -1 n)
                (< n dag-len)
                (depth-arrayp depth-array-name depth-array (+ 1 n))
                (< n (alen1 depth-array-name depth-array)))
           (array1p depth-array-name (mv-nth 0 (make-depth-array-aux n
                                                                     dag-array-name
                                                                     dag-array
                                                                     depth-array-name
                                                                     depth-array
                                                                     dag-len
                                                                     largest-depth
                                                                     ))))
  :hints (("Goal" :in-theory (e/d (make-depth-array-aux NATP-OF-+-OF-1) (natp)))))

;replace the other
(defthm all-<-of-+-of-1-and-maxelem-gen
  (implies (consp items)
           (all-< items (+ 1 (maxelem items))))
  :hints (("Goal" :in-theory (enable all-<))))

(defthm depth-arrayp-of-aset1-list
  (implies (and (depth-arrayp array-name array array-len)
                (or (natp val) (not val))
                (all-< indices array-len)
                (all-natp indices))
           (depth-arrayp array-name
                         (aset1-list array-name array indices val)
                         array-len))
  :hints (("Goal" :in-theory (enable aset1-list))))

;; Returns (mv depth-array largest-depth)
;fixme should we use depth 0 for the starting-nodes themselves?
;; the depth of a node is the shortest path to it from one of the designated nodes
(defun make-depth-array-for-nodes (starting-nodes dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (all-natp starting-nodes)
                              (true-listp starting-nodes)
                              (consp starting-nodes) ;or else the maxelem below is a problem
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (all-< STARTING-NODES 2147483646)
                              (all-< starting-nodes dag-len))))
  (let* ((max-nodenum (maxelem starting-nodes))
         (depth-array (make-empty-array 'depth-array (+ 1 max-nodenum)))
         (depth-array (aset1-list 'depth-array depth-array starting-nodes 1))
         ;; (depth-array (aset1 'depth-array depth-array smaller-nodenum 1))
         ;; (depth-array (aset1 'depth-array depth-array larger-nodenum 1))
         )
    (make-depth-array-aux max-nodenum dag-array-name dag-array 'depth-array depth-array dag-len 1)))

(defthm alen1-of-mv-nth-0-of-make-depth-array-for-nodes
  (implies (and (all-natp starting-nodes)
                (true-listp starting-nodes)
                (consp starting-nodes) ;or else the maxelem below is a problem
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< starting-nodes 2147483646)
                (all-< starting-nodes dag-len))
           (equal (alen1 'depth-array (mv-nth 0 (make-depth-array-for-nodes starting-nodes dag-array-name dag-array dag-len)))
                  (+ 1 (maxelem starting-nodes)))))

(defthm array1p-of-mv-nth-0-of-make-depth-array-for-nodes
  (implies (and (all-natp starting-nodes)
                (true-listp starting-nodes)
                (consp starting-nodes) ;or else the maxelem below is a problem
                (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                (all-< starting-nodes 2147483646)
                (all-< starting-nodes dag-len))
           (array1p 'depth-array (mv-nth 0 (make-depth-array-for-nodes starting-nodes dag-array-name dag-array dag-len)))))
