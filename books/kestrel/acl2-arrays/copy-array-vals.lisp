; A library for reasoning about ACL2 arrays (aref1, aset1, etc.)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "alen1")
(local (include-book "acl2-arrays"))

;; Copies the values at locations INDEX down to 0 from FROM-ARRAY to the same
;; locations in TO-ARRAY.  Requires that the arrays be big enough for INDEX to
;; be a valid index.  NOTE: when copying a whole array, consider calling
;; compress1 for speed?
(defund copy-array-vals (index from-array-name from-array to-array-name to-array)
  (declare (xargs :measure (nfix (+ 1 index))
                  :guard (and (rationalp index)
                              (array1p from-array-name from-array)
                              (array1p to-array-name to-array)
                              (< index (alen1 from-array-name from-array))
                              (< index (alen1 to-array-name to-array)))))
  (if (not (natp index))
      to-array
    (let ((to-array (aset1 to-array-name to-array index (aref1 from-array-name from-array index))))
      (copy-array-vals (+ -1 index) from-array-name from-array to-array-name to-array))))
