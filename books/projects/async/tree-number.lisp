;; Copyright (C) 2017, Regents of the University of Texas
;; Written by Cuong Chau (derived from the FM9001 work of Brock and Hunt)
;; License: A 3-clause BSD license.  See the LICENSE file distributed with
;; ACL2.

;; The ACL2 source code for the FM9001 work is available at
;; https://github.com/acl2/acl2/tree/master/books/projects/fm9001.

;; Cuong Chau <ckcuong@cs.utexas.edu>
;; January 2019

(in-package "ADE")

(include-book "hard-spec")

;; (TREE-NUMBER tree) returns a unique (we think) number for each equivalence
;; class of trees with the same CONS structure.  We use this to give unique,
;; numerical indices to modules created by tree-based module generators.  We
;; never proved that TREE-NUMBER yields a unique encoding, but our netlist
;; predicates would fail if it were ever the case that non-unique encodings
;; were produced.

;; ======================================================================

;; This definition of TREE-NUMBER has the property that a balanced tree with N
;; leaves has (TREE-NUMBER TREE) = N.  In the binary encoding of the tree, each
;; "full" level (whether full of CONS cells or leaves) is encoded as T.
;; Partially empty levels are encoded by NIL, followed by a bit string that
;; encodes with T and NIL those locations that are filled and empty
;; respectively.

(defun fix-breadth-tree-stack (stack n)
  (declare (xargs :guard (natp n)))
  (if (atom stack)
      nil
    (cons
     (append (make-list n) (car stack))
     (fix-breadth-tree-stack (cdr stack) (* 2 n)))))

(defthm true-list-listp-fix-breadth-tree-stack
  (implies (true-list-listp stack)
           (true-list-listp (fix-breadth-tree-stack stack n)))
  :rule-classes :type-prescription)

(defun breadth-tree (tree stack n)
  (declare (xargs :guard (and (true-listp stack)
                              (natp n))))
  (if (atom tree)
      (cons (cons t (if (atom stack)
                        (make-list n)
                      (car stack)))
            (fix-breadth-tree-stack (cdr stack) 2))
    (cons
     (cons t (if (atom stack)
                 (make-list n)
               (car stack)))
     (breadth-tree (cdr tree)
                   (breadth-tree (car tree) (cdr stack) (* 2 n))
                   (1+ (* 2 n))))))

(defthm true-list-listp-breadth-tree
  (implies (true-list-listp stack)
           (true-list-listp (breadth-tree tree stack n)))
  :rule-classes :type-prescription)

(defun collect-breadth-tree (stack n)
  (declare (xargs :guard (and (true-list-listp stack)
                              (natp n))))
  (if (atom stack)
      nil
    (if (equal (car stack) (make-list n :initial-element t))
        (cons t (collect-breadth-tree (cdr stack) (* 2 n)))
      (cons nil (append (car stack)
                        (collect-breadth-tree (cdr stack) (* 2 n)))))))

(defun tree-number (tree)
  (declare (xargs :guard t))
  (floor (1+
          (v-to-nat (collect-breadth-tree (breadth-tree tree nil 0) 1)))
         2))

(defthm natp-tree-number
  (natp (tree-number tree))
  :rule-classes :type-prescription)

(in-theory (disable tree-number))

#|
Problem:  Prove that TREE-NUMBER yields a unique encoding for isomorphic trees.
That is, given

(defun isomorphic (x y)
  (if (or (atom x) (atom y))
      (and (atom x) (atom y))
    (and (isomorphic (car x) (car y))
         (isomorphic (cdr x) (cdr y)))))

then show

(iff (isomorphic t1 t2)
     (equal (tree-number t1)
            (tree-number t2))).

|#
