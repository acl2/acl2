; Sorting a list and removing extra copies of duplicate items
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider specializing for lists of fixnums

(include-book "kestrel/utilities/split-list-fast-defs" :dir :system)
(include-book "merge-less-than-and-remove-dups")
(local (include-book "kestrel/utilities/split-list-fast" :dir :system))

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
               (rational-listp (mv-nth 0 (split-list-fast-aux lst tail acc))))
      :hints (("Goal" :in-theory (enable split-list-fast-aux))))

    (defthm rational-listp-of-mv-nth-1-of-split-list-fast-aux
      (implies (and (rational-listp acc)
                    (rational-listp lst)
                    (rational-listp tail)
                    (<= (len tail) (len lst)) ; needed in general for such proofs?
                    )
               (rational-listp (mv-nth 1 (split-list-fast-aux lst tail acc))))
      :hints (("Goal" :in-theory (enable split-list-fast-aux))))

    (defthm rational-listp-of-mv-nth-0-of-split-list-fast
      (implies (rational-listp lst)
               (rational-listp (mv-nth 0 (split-list-fast lst))))
      :rule-classes (:rewrite :type-prescription)
      :hints (("Goal" :in-theory (enable split-list-fast))))

    (defthm rational-listp-of-mv-nth-1-of-split-list-fast
      (implies (rational-listp lst)
               (rational-listp (mv-nth 1 (split-list-fast lst))))
      :rule-classes (:rewrite :type-prescription)
      :hints (("Goal" :in-theory (enable split-list-fast))))))

(local
  (progn
    (defthm nat-listp-of-mv-nth-0-of-split-list-fast-aux
      (implies (and (nat-listp acc)
                    (nat-listp lst)
                    (nat-listp tail)
                    (<= (len tail) (len lst)) ; needed in general for such proofs?
                    )
               (nat-listp (mv-nth 0 (split-list-fast-aux lst tail acc))))
      :hints (("Goal" :in-theory (enable split-list-fast-aux))))

    (defthm nat-listp-of-mv-nth-1-of-split-list-fast-aux
      (implies (and (nat-listp acc)
                    (nat-listp lst)
                    (nat-listp tail)
                    (<= (len tail) (len lst)) ; needed in general for such proofs?
                    )
               (nat-listp (mv-nth 1 (split-list-fast-aux lst tail acc))))
      :hints (("Goal" :in-theory (enable split-list-fast-aux))))

    (defthm nat-listp-of-mv-nth-0-of-split-list-fast
      (implies (nat-listp lst)
               (nat-listp (mv-nth 0 (split-list-fast lst))))
      :rule-classes (:rewrite :type-prescription)
      :hints (("Goal" :in-theory (enable split-list-fast))))

    (defthm nat-listp-of-mv-nth-1-of-split-list-fast
      (implies (nat-listp lst)
               (nat-listp (mv-nth 1 (split-list-fast lst))))
      :rule-classes (:rewrite :type-prescription)
      :hints (("Goal" :in-theory (enable split-list-fast))))))

(local
  (progn
    (defthm all-<-of-mv-nth-0-of-split-list-fast-aux
      (implies (and (all-< acc bound)
                    (all-< lst bound)
                    (all-< tail bound)
                    (<= (len tail) (len lst)) ; needed in general for such proofs?
                    )
               (all-< (mv-nth 0 (split-list-fast-aux lst tail acc)) bound))
      :hints (("Goal" :in-theory (enable split-list-fast-aux))))

    (defthm all-<-of-mv-nth-1-of-split-list-fast-aux
      (implies (and (all-< acc bound)
                    (all-< lst bound)
                    (all-< tail bound)
                    (<= (len tail) (len lst)) ; needed in general for such proofs?
                    )
               (all-< (mv-nth 1 (split-list-fast-aux lst tail acc)) bound))
      :hints (("Goal" :in-theory (enable split-list-fast-aux))))

    (defthm all-<-of-mv-nth-0-of-split-list-fast
      (implies (all-< lst bound)
               (all-< (mv-nth 0 (split-list-fast lst)) bound))
      :rule-classes (:rewrite :type-prescription)
      :hints (("Goal" :in-theory (enable split-list-fast))))

    (defthm all-<-of-mv-nth-1-of-split-list-fast
      (implies (all-< lst bound)
               (all-< (mv-nth 1 (split-list-fast lst)) bound))
      :rule-classes (:rewrite :type-prescription)
      :hints (("Goal" :in-theory (enable split-list-fast))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund merge-sort-<-and-remove-dups (l)
  (declare (xargs :guard (rational-listp l)
                  :measure (len l)
                  :verify-guards nil ; done below
                  ))
  (if (or (endp l)
          (endp (rest l)))
      l ; already sorted and no dups
      (mv-let (l1 l2)
        (split-list-fast l)
        (merge-<-and-remove-dups (merge-sort-<-and-remove-dups l1)
                                 (merge-sort-<-and-remove-dups l2)))))

(defthm rational-listp-of-merge-sort-<-and-remove-dups
  (implies (rational-listp l)
           (rational-listp (merge-sort-<-and-remove-dups l)))
  :hints (("Goal" :in-theory (enable merge-sort-<-and-remove-dups))))

(defthm true-listp-of-merge-sort-<-and-remove-dups
  (implies (true-listp l)
           (true-listp (merge-sort-<-and-remove-dups l)))
  :hints (("Goal" :in-theory (enable merge-sort-<-and-remove-dups))))

(verify-guards merge-sort-<-and-remove-dups
  :hints (("Goal" :in-theory (enable all-rationalp-when-rational-listp))))

;; special case
(defthm nat-listp-of-merge-sort-<-and-remove-dups
  (implies (nat-listp l)
           (nat-listp (merge-sort-<-and-remove-dups l)))
  :hints (("Goal" :in-theory (enable merge-sort-<-and-remove-dups))))

;; could do sortedp-<, which should imply no dupes
(defthm sortedp-<=-of-merge-sort-<-and-remove-dups
  (sortedp-<= (merge-sort-<-and-remove-dups l))
  :hints (("Goal" :in-theory (enable merge-sort-<-and-remove-dups))))

(defthm no-duplicatesp-equal-of-merge-sort-<-and-remove-dups
  (implies (rational-listp l)
           (no-duplicatesp-equal (merge-sort-<-and-remove-dups l)))
  :hints (("Goal" :in-theory (enable merge-sort-<-and-remove-dups))))

(defthm all-<-of-merge-sort-<-and-remove-dups
  (implies (all-< l bound)
           (all-< (merge-sort-<-and-remove-dups l) bound))
  :hints (("Goal" :in-theory (enable merge-sort-<-and-remove-dups))))

;; (= (merge-sort-<-and-remove-dups '(4 4 1 2 3 1 0 2 3 2)) (0 1 2 3 4))
