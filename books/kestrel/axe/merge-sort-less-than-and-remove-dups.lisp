; Extracting variable from an R1CS
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/split-list-fast" :dir :system)
(include-book "merge-less-than-and-remove-dups")

;move
(local
 (defthm all-rationalp-when-rational-listp
   (implies (rational-listp x)
            (all-rationalp x))))

(local
  (progn
    (defthm rational-listp-of-mv-nth-0-of-split-list-fast-aux
      (implies (and (rational-listp acc)
                    (rational-listp lst)
                    (rational-listp tail)
                    (<= (len tail) (len lst)) ; needed in general for such proofs?
                    )
               (rational-listp (mv-nth 0 (acl2::split-list-fast-aux lst tail acc))))
      :hints (("Goal" :in-theory (enable acl2::split-list-fast-aux))))

    (defthm rational-listp-of-mv-nth-1-of-split-list-fast-aux
      (implies (and (rational-listp acc)
                    (rational-listp lst)
                    (rational-listp tail)
                    (<= (len tail) (len lst)) ; needed in general for such proofs?
                    )
               (rational-listp (mv-nth 1 (acl2::split-list-fast-aux lst tail acc))))
      :hints (("Goal" :in-theory (enable acl2::split-list-fast-aux))))

    (defthm rational-listp-of-mv-nth-0-of-split-list-fast
      (implies (rational-listp lst)
               (rational-listp (mv-nth 0 (acl2::split-list-fast lst))))
      :rule-classes (:rewrite :type-prescription)
      :hints (("Goal" :in-theory (enable acl2::split-list-fast))))

    (defthm rational-listp-of-mv-nth-1-of-split-list-fast
      (implies (rational-listp lst)
               (rational-listp (mv-nth 1 (acl2::split-list-fast lst))))
      :rule-classes (:rewrite :type-prescription)
      :hints (("Goal" :in-theory (enable acl2::split-list-fast))))))

(defun merge-sort-<-and-remove-dupes (l)
  (declare (xargs :guard (rational-listp l)
                  :measure (len l)
                  :verify-guards nil ; done below
                  ))
  (if (or (endp l)
          (endp (rest l)))
      l ; already sorted and no dups
      (mv-let (l1 l2)
        (split-list-fast l)
        (merge-<-and-remove-dups (merge-sort-<-and-remove-dupes l1)
                                 (merge-sort-<-and-remove-dupes l2)))))

(defthm rational-listp-of-merge-sort-<-and-remove-dupes
  (implies (rational-listp l)
           (rational-listp (merge-sort-<-and-remove-dupes l))))

(verify-guards merge-sort-<-and-remove-dupes
  :hints (("Goal" :in-theory (enable all-rationalp-when-rational-listp))))

(defthm sortedp-<=-of-merge-sort-<-and-remove-dupes
  (sortedp-<= (merge-sort-<-and-remove-dupes l)))

(defthm no-duplicatesp-equal-of-merge-sort-<-and-remove-dupes
  (implies (rational-listp l)
           (no-duplicatesp-equal (merge-sort-<-and-remove-dupes l))))
