; Printing DAG arrays
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

;; This book deals with printing dags-arrays, typcially only printing the relevant nodes.

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
(defun filter-nodenums (items acc)
  (declare (xargs :guard (all-dargp items)))
  (if (atom items)
      acc
    (if (consp (car items)) ;tests for quotep
        (filter-nodenums (cdr items) acc)
      (filter-nodenums (cdr items) (cons (car items) acc)))))

(defthm true-listp-of-filter-nodenums
  (equal (true-listp (filter-nodenums items acc))
         (true-listp acc)))

;; Print the nodes in node-list and all of their supporters.  Doesn't print any nodes below low-index.
;; TODO: Make a specialized version for when low-index is 0.
;; TODO: Use a worklist algorithm (this currently goes through the nodes one-by-one).
(defun print-supporting-dag-nodes (index low-index dag-array-name dag-array node-list first-elementp)
  (declare (type (integer 0 *) low-index)
           (type integer index)
	   (xargs :measure (+ 1 (nfix (- (+ 1 index) low-index)))
                  :guard (and (pseudo-dag-arrayp dag-array-name dag-array (+ 1 index))
                              (true-listp node-list))
                  :guard-hints (("Goal" :in-theory (enable array1p-rewrite)))))
  (if (or (< index low-index)
          (not (mbt (natp low-index)))
          (not (mbt (natp index))))
      nil
    (if (member index node-list) ;fixme this could be slow.  use an array of tags?
        ;;print this node (and add its supporters to node-list)
        (let ((expr (aref1 dag-array-name dag-array index)))
          (progn$ (if (not first-elementp) (cw "~% ") nil)
                  (cw "~F0" (cons index expr)) ;ffixme skip this cons?! (also in the other version)
                  (print-supporting-dag-nodes (+ -1 index)
                                              low-index
                                              dag-array-name
                                              dag-array
                                              (if (and (consp expr)
                                                       (not (eq 'quote (ffn-symb expr))))
                                                  (filter-nodenums (dargs expr) node-list)
                                                node-list)
                                              nil)))
      ;;skip this node:
      (print-supporting-dag-nodes (+ -1 index)
                                  low-index
                                  dag-array-name
                                  dag-array
                                  node-list
                                  nil))))

;fixme whitespace and after last node isn't quite right
;does this do the right thing for very small arrays?
;ffixme allow the key node to be not the top node?
(defun print-dag-only-supporters (dag-array-name dag-array nodenum)
  (declare (type (integer 0 *) nodenum)
           (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 nodenum)))
                  :split-types t))
  (progn$ (cw "(")
          (print-supporting-dag-nodes nodenum 0 dag-array-name dag-array (list nodenum) t)
          (cw ")~%")))

(defun print-dag-only-supporters-of-nodes (dag-array-name dag-array nodenums)
  (declare (xargs :guard (and (all-natp nodenums)
                              (true-listp nodenums)
                              (consp nodenums)
                              (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums))))
                  :guard-hints (("Goal" :in-theory (enable maxelem ;todo
                                                           )))))
  (prog2$
   ;;print the open paren:
   (cw "(")
   (prog2$
    ;;print the elements
    (print-supporting-dag-nodes (maxelem nodenums) 0 dag-array-name dag-array nodenums t)
    ;;print the close paren:
    (cw ")~%"))))

(defun print-dag-only-supporters-lst (nodenums dag-array-name dag-array)
  (declare (xargs :guard (and (all-natp nodenums)
                              (true-listp nodenums)
                              (if (consp nodenums)
                                  (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem nodenums)))
                                t))))
  (if (endp nodenums)
      nil
    (progn$ (print-dag-only-supporters dag-array-name dag-array (car nodenums))
            (cw "~%")
            (print-dag-only-supporters-lst (cdr nodenums) dag-array-name dag-array))))
