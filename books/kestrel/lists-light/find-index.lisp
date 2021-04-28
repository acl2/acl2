; A tool to find the index of an element in a list
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Return the index (0-based) of the first ocurrence of ITEM in LST, or return
;; the length of the list (which is not a valid 0-based index) if ITEM does not
;; occur in LST.  The latter case can be viewed as returning the index of the
;; item "one past" the end of the list.
(defun find-index (item lst)
  (if (endp lst)
      0 ; item not found, so return the length of the list
    (if (equal item (car lst))
        0
      (+ 1 (find-index item (cdr lst))))))

(defthm find-index-of-true-list-fix
  (equal (find-index a (true-list-fix lst))
         (find-index a lst))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm find-index-type
  (natp (find-index item lst))
  :rule-classes :type-prescription)
