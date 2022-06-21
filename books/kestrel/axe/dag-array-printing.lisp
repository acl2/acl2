; Printing DAG arrays
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

;; This book deals with printing dags-arrays, typically only printing the relevant nodes.
;; See alsod dag-array-printing2.lisp.

(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "dag-arrays")
(local (include-book "kestrel/lists-light/cons" :dir :system))

;move
(local
 (defthm acl2-numberp-of-maxelem-2
   (implies (and (all-natp lst) ;yuck
                 (consp lst))
            (acl2-numberp (maxelem lst)))))

;; Extends ACC with the members of ITEMS that are nodenums (also reverses their
;; order).  Each member of ITEMS must be a nodenum or a quoted constant.
;; TODO: This must already exist (keep-atoms?).
(defund filter-nodenums (items acc)
  (declare (xargs :guard (all-dargp items)))
  (if (atom items)
      acc
    (if (consp (car items)) ;tests for quotep
        (filter-nodenums (cdr items) acc)
      (filter-nodenums (cdr items) (cons (car items) acc)))))

(defthm true-listp-of-filter-nodenums
  (equal (true-listp (filter-nodenums items acc))
         (true-listp acc))
  :hints (("Goal" :in-theory (enable filter-nodenums))))

;; TODO: Rename these functions to have "array" in their names.

;; Goes from INDEX down to 0, printing the nodes in NODE-LIST and all of their supporters.
;; TODO: Use a worklist algorithm (this currently goes through the nodes one-by-one).
;; TODO: Instead of using NODE-LIST, perhaps use an array of tags, unless we expect the number of relevant nodes to be small.
(defund print-dag-array-aux (index dag-array-name dag-array node-list first-elementp)
  (declare (xargs :guard (and (integerp index)
                              (<= -1 index)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 index))
                              (true-listp node-list))
                  :measure (+ 1 (nfix (+ 1 index)))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))
                  :split-types t)
	   (type integer index))
  (if (or (< index 0)
          (not (mbt (integerp index))))
      nil
    (if (member index node-list) ; could be slow.
        ;;print this node (and add its supporters to node-list)
        (let ((expr (aref1 dag-array-name dag-array index)))
          (progn$ (if (not first-elementp) (cw "~% ") nil)
                  (cw "~F0" (cons index expr)) ;; TODO: Avoid this cons? (also in the other version)
                  (print-dag-array-aux (+ -1 index)
                                              dag-array-name
                                              dag-array
                                              (if (and (consp expr)
                                                       (not (eq 'quote (ffn-symb expr))))
                                                  (filter-nodenums (dargs expr) node-list)
                                                node-list)
                                              nil)))
      ;;skip this node:
      (print-dag-array-aux (+ -1 index) dag-array-name dag-array node-list nil))))

;; Prints the node whose number is NODENUM, and any supporting nodes.
;; TODO: Improve whitespace and after last node.
;does this do the right thing for very small arrays?
(defund print-dag-array-node-and-supporters (dag-array-name dag-array nodenum)
  (declare (type (integer 0 *) nodenum)
           (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum)))
                  :split-types t))
  (progn$ (cw "(")
          (print-dag-array-aux nodenum dag-array-name dag-array (list nodenum) t)
          (cw ")~%")))

;; Prints the nodes whose numbers are in NODENUMS, and any supporting nodes.
(defund print-dag-array-nodes-and-supporters (dag-array-name dag-array nodenums)
  (declare (xargs :guard (and (all-natp nodenums)
                              (true-listp nodenums)
                              (consp nodenums)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums))))
                  :guard-hints (("Goal" :in-theory (enable maxelem ;todo
                                                           )))))
  (progn$ (cw "(")
          (print-dag-array-aux (maxelem nodenums) dag-array-name dag-array nodenums t)
          (cw ")~%")))

;; Separately prints the part of the DAG supporting each of the NODENUMS.
(defund print-dag-array-node-and-supporters-lst (nodenums dag-array-name dag-array)
  (declare (xargs :guard (and (all-natp nodenums)
                              (true-listp nodenums)
                              (if (consp nodenums)
                                  (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums)))
                                t))))
  (if (endp nodenums)
      nil
    (progn$ (print-dag-array-node-and-supporters dag-array-name dag-array (car nodenums))
            (cw "~%")
            (print-dag-array-node-and-supporters-lst (cdr nodenums) dag-array-name dag-array))))

(defund print-dag-array-all-aux (nodenum dag-array-name dag-array first-elementp)
  (declare (xargs :guard (and (integerp nodenum)
                              (<= -1 nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum)))
                  :measure (+ 1 (nfix (+ 1 nodenum)))
;                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))
                  :split-types t)
	   (type integer nodenum))
  (if (or (< nodenum 0)
          (not (mbt (integerp nodenum))))
      nil
    (let ((expr (aref1 dag-array-name dag-array nodenum)))
      (progn$ (if (not first-elementp) (cw "~% ") nil)
              (cw "~F0" (cons nodenum expr)) ;; TODO: Avoid this cons?
              (print-dag-array-all-aux (+ -1 nodenum)
                                       dag-array-name
                                       dag-array
                                       nil)))))

;; Print the entire dag, from NODENUM down to 0, including nodes not supporting NODENUM.
(defund print-dag-array-all (nodenum dag-array-name dag-array)
  (declare (xargs :guard (and (integerp nodenum)
                              (<= -1 nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum)))))
  (progn$ (cw "(")
          (print-dag-array-all-aux nodenum dag-array-name dag-array t)
          (cw ")~%")))
