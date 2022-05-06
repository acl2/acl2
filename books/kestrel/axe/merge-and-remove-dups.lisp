; Merging sorted lists of nodenums and removing pairs of duplicates
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)

;args are sorted in increasing order
;result is sorted in decreasing order
(defund merge-and-remove-dups (lst1 lst2 acc)
  (declare (xargs :measure (+ 1 (len lst1) (len lst2))
                  :guard (and (all-integerp lst1)
                              (true-listp lst1)
                              (all-integerp lst2)
                              (true-listp lst2)
                              (all-integerp acc))))
  (if (endp lst1)
      (revappend lst2 acc)
    (if (endp lst2)
        (revappend lst1 acc)
      (let ((item1 (first lst1))
            (item2 (first lst2)))
        (if (< item1 item2)
            (merge-and-remove-dups (rest lst1) lst2 (cons item1 acc))
          (if (< item2 item1)
              (merge-and-remove-dups lst1 (rest lst2) (cons item2 acc))
            ;;they are equal, so drop them both
            (merge-and-remove-dups (rest lst1) (rest lst2) acc)))))))

(defthm true-listp-of-merge-and-remove-dups
  (implies (true-listp acc)
           (true-listp (merge-and-remove-dups lst1 lst2 acc)))
  :hints (("Goal" :in-theory (enable merge-and-remove-dups))))
