; Tests of defstobj+
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defstobj-plus")

;; TODO: Add more tests

(defstobj+ my-stobj
  (my-array-field :type (array integer (10000)) :initially 0)
  )

;; example (lots of theorems generated, since there are quite a few fields)
(defstobj+ my-stobj2
  (my-array1 :type (array integer (10000)) :initially 0)
  ;; resizable:
  (my-array2 :type (array integer (10000)) :resizable t :initially 0)
  ;; predicate is a conjunction:
  (my-array3 :type (array (satisfies natp) (10000)) :resizable t :initially 0)
  ;; predicate is t:
  (my-array4 :type (array t (10000)) :resizable t :initially 0)
  ;; element predicate is a call to satisfies:
  (my-array5 :type (array (satisfies consp) (10000)) :resizable t :initially (a b))
  ;; an element type which NIL satisfies (nicer theorems):
  (my-array6 :type (array (satisfies atom) (10000)) :resizable t :initially nil)
  ;; element predicate is a call to AND:
  (my-array7 :type (array (and integer (satisfies posp)) (10000)) :resizable t :initially 7)

  (my-scalar1 :type integer :initially 0)
  ;; A "scalar" field that is actually a cons ("scalar field" means not an array field, hash table field, etc.):
  (my-scalar2 :type (satisfies consp) :initially (a b))
  ;; predicate is t:
  (my-scalar3 :type t :initially 0)
  ;; a type-spec that is an AND:
  (my-scalar4 :type (and integer (satisfies posp)) :initially 100)
  my-scalar5
  )

;; A test with a hash-table field (note that defstobj+ doesn't generate theorems about the operations on it yet):
(defstobj+ my-stobj3
  (an-array-field :type (array integer (10000)) :initially 0 :resizable t)
  (a-scalar-field :type integer :initially 0)
  (a-hash-table-field :type (hash-table equal 200))
  )

;; A test where the field name is in the common-lisp package
(defstobj+ foo (print :type atom)
  :renaming ((common-lisp::print get-print)
             (common-lisp::printp printp)
             (common-lisp::update-print update-print)))

;; test of the renaming:
(defstobj+ foo2 (bar :type atom)
  :renaming ((bar get-bar)
             (barp my-barp)
             (update-bar my-update-bar)))

;; In this one, the field is in a different package and we use more exotic names:
;; TODO: Need to fix the generation of names (see TODO in defstobj-plus.lisp):
;; (defstobj+ foo3 (print :type atom)
;;   :renaming ((common-lisp::print my-get-print)
;;              (common-lisp::printp my-printp)
;;              (common-lisp::update-print put-print)))
