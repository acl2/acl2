; Utilities for manipulating parsed CSV files
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/all-equal-dollar" :dir :system)

;; Recognzes a blank row, in which every cell is the empty string.
(defund blank-rowp (row)
  (declare (xargs :guard (true-listp row)))
  (all-equal$ "" row))

;; Dicards blank rows at the front of ROWS.
(defund skip-blank-rows (rows)
  (declare (xargs :guard (true-list-listp rows)))
  (if (endp rows)
      rows
    (if (blank-rowp (first rows))
        (skip-blank-rows (rest rows))
      rows)))

(defthm <=-of-len-of-skip-blank-rows-linear
  (<= (len (skip-blank-rows rows))
      (len rows))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable skip-blank-rows))))
