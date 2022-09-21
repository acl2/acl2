; A variant of union-equal that differs in which duplicate is dropped
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "filter-non-members")

;; Like union-equal, but for items in both X and Y, this keeps the one in X.
(defund union-equal-alt (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (append x (filter-non-members y x)))

;; (equal (union-equal-alt '(1 2 3) '(2 4)) '(1 2 3 4))
