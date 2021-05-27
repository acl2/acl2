; A function to search a list for an item not in a second list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Returns the first member of items that is not in items-to-exclude
;; (if any).  Otherwise, returns nil.
(defun first-non-member (items items-to-exclude)
  (declare (xargs :guard (true-listp items-to-exclude)))
  (if (atom items)
      nil
    (if (not (member-equal (car items) items-to-exclude))
        (car items)
      (first-non-member (cdr items) items-to-exclude))))

(defthm first-non-member-of-append
  (equal (first-non-member (append x y) lst)
         (if (acl2::subsetp-equal x lst)
             (first-non-member y lst)
           (first-non-member x lst)))
  :hints (("Goal" :in-theory (enable subsetp-equal))))

(defthmd first-non-member-when-member-equal
  (implies (member-equal (car items) lst)
           (equal (first-non-member items lst)
                  (first-non-member (cdr items) lst))))

(defthm first-non-member-when-not-member-equal
  (implies (not (member-equal (car items) lst))
           (equal (first-non-member items lst)
                  (car items))))
