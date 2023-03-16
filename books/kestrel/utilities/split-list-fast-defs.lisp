; A very fast function to split a list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book introduces the function split-list-fast, which splits a list into
;; two pieces of roughly the same size, where the order doesn't really matter
;; (e.g., for mergesort).

;; Note: "split-list" (without the "-fast") is already the name of a function
;; in the rtl library.

;; Returns (mv first-half second-half).
;; This walks down TAIL twice as fast as it walks down LST.  ACC contains the elems already passed on the slower traversal.
(defun split-list-fast-aux (lst tail acc)
  (declare (xargs :guard (and (true-listp tail)
                              (true-listp lst))))
  (if (or (endp tail)
          (endp (cdr tail)))
      (mv acc lst)
    (split-list-fast-aux (cdr lst) (cddr tail) (cons (car lst) acc))))

;; Splits LST into 2 parts of roughly equal size.
;; This is helpful when all we care about is splitting the list into two pieces
;; of roughly the same size, not the order and not which elements go in which
;; half.  For example this is useful for mergesort. This reuses the tail of the list.
;; Returns (mv first-half-rev second-half) where FIRST-HALF-REV is the first
;; half of the elements in reverse.
;; TODO: Would it be faster to compute the length of the list first and then
;; walk down that many elements (would require arithmetic)?
(defund split-list-fast (lst)
  (declare (xargs :guard (true-listp lst)))
  (split-list-fast-aux lst lst nil))
