; Utilities to quickly form printable sequences of strings
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A string-tree is a cons nest whose leaves are strings or nil.  It represents
;; the concatenation of all the strings at the leaves of the tree, in order,
;; ignoring any nils.  A single string and a true-list of strings are both
;; string-trees.  Creating string-trees may be faster than concatenating many
;; strings together.  Creating string-trees may also be faster than appending
;; lists of strings, since you can use cons instead of append.  The macro list*
;; can be used to create a string-tree from a number of existing string-trees.

;; TODO: Add support for characters (let a string-tree be a single character).
;; TODO: Consider adding support for trees that are numbers and symbols.

(defund string-treep (x)
  (declare (xargs :guard t))
  (if (atom x)
      (or (eq nil x)
          (stringp x))
    (and (string-treep (car x))
         (string-treep (cdr x)))))

(defthm string-treep-of-car
  (implies (and (consp string-tree)
                (string-treep string-tree))
           (string-treep (car string-tree)))
  :hints (("Goal" :in-theory (enable string-treep))))

(defthm string-treep-of-cdr
  (implies (and (consp string-tree)
                (string-treep string-tree))
           (string-treep (cdr string-tree)))
  :hints (("Goal" :in-theory (enable string-treep))))

(defthm string-treep-of-cons
  (equal (string-treep (cons x y))
         (and (string-treep x)
              (string-treep y)))
  :hints (("Goal" :in-theory (enable string-treep))))

(defthmd string-treep-when-string-listp
  (implies (string-listp strings)
           (string-treep strings))
  :hints (("Goal" :in-theory (enable string-treep))))

(defthm string-treep-of-append
  (implies (and (string-treep x)
                (string-treep y))
           (string-treep (append x y)))
  :hints (("Goal" :in-theory (enable string-treep))))

;; This avoids carrying along extra nils
(defund binary-make-string-tree (t1 t2)
  (declare (xargs :guard (and (string-treep t1)
                              (string-treep t2))))
  (if (eq nil t1)
      t2
    (if (eq nil t2)
        t1
      (cons t1 t2))))

(defthm string-treep-of-binary-make-string-tree
  (implies (and (string-treep x)
                (string-treep y))
           (string-treep (binary-make-string-tree x y)))
  :hints (("Goal" :in-theory (enable string-treep binary-make-string-tree))))

(defmacro make-string-tree (&rest rst)
  (cond ((null rst) nil)
        ((null (cdr rst)) (car rst))
        (t (xxxjoin 'binary-make-string-tree rst))))

;; "Flattens" a string-tree into a string.  There may be ways to optimize
;; this. An alternative to flattening a string-tree is to handle the individual
;; strings at the leaves one by one (e.g., by writing them to a file).
(defun flatten-string-tree (string-tree)
  (declare (xargs :guard (string-treep string-tree)
                  :verify-guards nil ;done below
                  ))
  (if (atom string-tree)
      (if (eq nil string-tree)
          ""
        string-tree)
    (concatenate 'string
                 (flatten-string-tree (car string-tree))
                 (flatten-string-tree (cdr string-tree)))))

(defthm stringp-of-flatten-string-tree
  (implies (string-treep string-tree)
           (stringp (flatten-string-tree string-tree)))
  :hints (("Goal" :in-theory (enable string-treep))))

(verify-guards flatten-string-tree)

(defthm string-treep-when-stringp-cheap
  (implies (stringp x)
           (string-treep x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable string-treep))))
