; A utility to find the shorter of two lists
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")


;this should be faster than comparing the lens (no arithmetic to do, and len would be slow if one list was huge)
;finds the shorter of two lists
;todo: rename
(defund shorter-lst (lst1 lst2 orig-lst1 orig-lst2)
  (declare (xargs :guard (and (true-listp lst1)
                              (true-listp lst2))))
  (if (endp lst1)
      orig-lst1
    (if (endp lst2)
        orig-lst2
      (shorter-lst (rest lst1) (rest lst2) orig-lst1 orig-lst2))))

(defthm shorter-lst-rewrite
  (equal (shorter-lst lst1 lst2 orig-lst1 orig-lst2)
         (if (<= (len lst1) (len lst2))
             orig-lst1
           orig-lst2))
  :hints (("Goal" :in-theory (enable shorter-lst))))

(defthm nat-listp-of-shorter-lst
  (implies (and (nat-listp orig-lst1)
                (nat-listp orig-lst2))
           (nat-listp (shorter-lst lst1 lst2 orig-lst1 orig-lst2))))

(defthm true-listp-of-shorter-lst
  (implies (and (true-listp orig-lst1)
                (true-listp orig-lst2))
           (true-listp (shorter-lst lst1 lst2 orig-lst1 orig-lst2))))
