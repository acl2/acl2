; Copyright (C) 2022, ForrestHunt, Inc.
; Written by J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; A Little Btree Utility

; This file contains a naive, inefficient, :program mode function for
; constructing a balanced binary tree containing a list of ``tip names.''
; E.g.,

; ACL2 !>(test-btree '(a b c d e))
; ((:TREE ((A . B) C D . E))
;  (:COSTS (A . 2)
;          (B . 2)
;          (C . 2)
;          (D . 3)
;          (E . 3)))

; shows the btree constructed and the number of cars and/or cdrs necessary to
; reach each tip.  Notice that the input is just a list of tip names.  The tips
; of the constructed tree are always in the order initially listed.  All
; branches of the tree are either the same depth (when the number of tips is a
; power of two) or just differ by 1, with the all the deeper branches to the
; right.

; This program was used to lay out the defrec rewrite-constant.

(in-package "ACL2")

(program)

(defun car-cdr-depth (name tree)
  (cond
   ((atom tree)
    (if (eq name tree) 0 nil))
   (t
    (let ((card (car-cdr-depth name (car tree))))
      (cond
       (card (+ 1 card))
       (t (let ((cdrd (car-cdr-depth name (cdr tree))))
            (cond
             (cdrd (+ 1 cdrd))
             (t nil)))))))))

(defun car-cdr-depth-lst (names tree)
  (cond ((endp names) nil)
        (t (cons (cons (car names) (car-cdr-depth (car names) tree))
                 (car-cdr-depth-lst (cdr names) tree)))))

(defun flatten (x)
  (if (atom x)
      (list x)
      (append (flatten (car x)) (flatten (cdr x)))))

(defun node-cnt (x)
  (cond ((atom x) 1)
        (t (+ (node-cnt (car x))
              (node-cnt (cdr x))))))

(defun log2 (n)
  (if (zp n) 0 (if (equal n 1) 0 (+ 1 (log2 (floor n 2))))))

(defun full-treep (x)
  (let ((cnt (node-cnt x)))
    (equal cnt (expt 2 (log2 cnt)))))

(mutual-recursion

(defun build-a-btree1 (tree lst)
  (cond ((endp lst) tree)
        (t (build-a-btree1 (add-to-btree tree (car lst))
                           (cdr lst)))))

(defun build-a-btree (lst)
  (build-a-btree1 (car lst) (cdr lst))) 


(defun add-to-btree (x n)
  (cond ((atom x) (cons x n))
        ((< (node-cnt (car x)) (node-cnt (cdr x)))
         (if (full-treep (cdr x))
             (let ((lst (flatten (cdr x))))
               (cons (add-to-btree (car x) (car lst))
                     (build-a-btree (append (cdr lst) (list n)))))
             (cons (car x) (add-to-btree (cdr x) n))))
        (t (cons (car x) (add-to-btree (cdr x) n)))))
)

(defun test-btree (lst)
  (let ((tree (build-a-btree lst)))
    (list (list :tree tree)
          (cons :costs (car-cdr-depth-lst lst tree)))))


