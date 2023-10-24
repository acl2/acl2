; Checking if a bv-list is the negation of another bv-list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/firstn" :dir :system)
(include-book "bvnot-list")

;; Check whether each item of LST1 is the negation of the corresponding item in LST2.
;this stops when the first list runs out
(defun negated-elems-listp (width lst1 lst2)
  (declare (xargs :guard (natp width)))
  (if (atom lst1)
      t
    (and (consp lst2)
         (let ((item1 (first lst1)))
           (and (integerp item1)
                (equal (bvnot width item1) (first lst2))
                (negated-elems-listp width (rest lst1) (rest lst2)))))))

(defthm negated-elems-listp-rewrite
  (implies (true-listp lst1)
           (iff (negated-elems-listp width lst1 lst2)
                (and (all-integerp lst1)
                     (equal (firstn (len lst1) lst2) (bvnot-list width lst1))))))
