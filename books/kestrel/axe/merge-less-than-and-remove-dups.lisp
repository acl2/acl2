; Merging sorted lists and removing extra copies of duplicate items
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider specializing for lists of fixnums

;; Note that this keeps one copy of each set of dupes (when each arg has no dupes).
;; See also merge-and-remove-pairs-of-dups.lisp.

(include-book "kestrel/typed-lists-light/sortedp-less-than-or-equal" :dir :system)
(include-book "kestrel/typed-lists-light/all-rationalp" :dir :system)
(include-book "kestrel/typed-lists-light/all-less-than-or-equal-all" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(local (include-book "merge-sort-less-than-rules")) ; todo: move some of these
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-lists" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))

(local (in-theory (enable <=-of-car-and-cadr-when-sortedp-<=)))

;move
(defthmd not-intersection-equal-when-all-<-of-car-and-sortedp-<=
  (implies (and (all-< y (car x))
                (sortedp-<= x))
           (not (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable all-< sortedp-<= intersection-equal))))

;move
(defthmd <-of-car-and-cadr-when-sortedp-<=-and-no-duplicatesp-equal
  (implies (and (sortedp-<= x)
                (no-duplicatesp-equal x)
                (consp (cdr x))
                (all-rationalp x))
           (< (car x) (cadr x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable sortedp-<= no-duplicatesp-equal))))

;; Merges sorted lists (according to <) and removes duplicates that appear in both lists.
;; L1 and L2 should be sorted in ascending order (and be duplicate free).
;; ACC should contain the smallest items (smaller than anything in L1 or L2), sorted in decreasing order.
(defund merge-<-and-remove-dups-aux (l1 l2 acc)
  (declare (xargs :guard (and (all-rationalp l1)
                              (all-rationalp l2)
                              (true-listp acc))
                  :measure (+ (len l1) (len l2))))
  (cond ((atom l1) (revappend acc l2))
        ((atom l2) (revappend acc l1))
        ((equal (car l1) (car l2)) ;drop one copy:
         (merge-<-and-remove-dups-aux (cdr l1) l2 acc))
        ((< (car l1) (car l2))
         (merge-<-and-remove-dups-aux (cdr l1)
                                      l2 (cons (car l1) acc)))
        (t (merge-<-and-remove-dups-aux l1 (cdr l2)
                                        (cons (car l2) acc)))))

(local
  (defthm nat-listp-of-merge-<-and-remove-dups-aux
    (implies (and (nat-listp l1)
                  (nat-listp l2)
                  (nat-listp acc))
             (nat-listp (merge-<-and-remove-dups-aux l1 l2 acc)))
    :hints (("Goal" :in-theory (enable merge-<-and-remove-dups-aux)))))

(local
  (defthm true-listp-of-merge-<-and-remove-dups-aux
    (implies (and (true-listp l1)
                  (true-listp l2))
             (true-listp (merge-<-and-remove-dups-aux l1 l2 acc)))
    :hints (("Goal" :in-theory (enable merge-<-and-remove-dups-aux)))))

(local
  (defthm rational-listp-of-merge-<-and-remove-dups-aux
    (implies (and (rational-listp l1)
                  (rational-listp l2)
                  (rational-listp acc))
             (rational-listp (merge-<-and-remove-dups-aux l1 l2 acc)))
    :hints (("Goal" :in-theory (enable merge-<-and-remove-dups-aux)))))

(local
  (defthm sortedp-<=-of-merge-<-and-remove-dups-aux
    (implies (and (sortedp-<= l1)
                  (sortedp-<= l2)
                  (sortedp-<= (reverse-list acc))
                  (all-<=-all acc l1)
                  (all-<=-all acc l2))
             (sortedp-<= (merge-<-and-remove-dups-aux l1 l2 acc)))
    :hints (("Goal" :expand ((merge-<-and-remove-dups-aux l1 l2 acc))
             :induct (merge-<-and-remove-dups-aux l1 l2 acc)
             :in-theory (enable merge-<-and-remove-dups-aux
                                revappend-becomes-append-of-reverse-list
                                all-<=-all)))))

(local
  (defthm no-duplicatesp-equal-of-merge-<-and-remove-dups-aux
    (implies (and (sortedp-<= l1)
                  (sortedp-<= l2)
                  (sortedp-<= (reverse-list acc))
                  (implies (consp l1) (all-< acc (first l1)))
                  (implies (consp l2) (all-< acc (first l2)))
                  (no-duplicatesp-equal l1)
                  (no-duplicatesp-equal l2)
                  (no-duplicatesp-equal acc)
                  (all-rationalp l1)
                  (all-rationalp l2))
             (no-duplicatesp-equal (merge-<-and-remove-dups-aux l1 l2 acc)))
    :hints (("Goal" :in-theory (enable merge-<-and-remove-dups-aux
                                       revappend-becomes-append-of-reverse-list
                                       not-intersection-equal-when-all-<-of-car-and-sortedp-<=
                                       <-of-car-and-cadr-when-sortedp-<=-and-no-duplicatesp-equal)))))

(local
 (defthm all-<-of-merge-<-and-remove-dups-aux
   (equal (all-< (merge-<-and-remove-dups-aux l1 l2 acc) bound)
          (and (all-< l1 bound)
               (all-< l2 bound)
               (all-< acc bound)))
   :hints (("Goal" :in-theory (enable merge-<-and-remove-dups-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Merge L1 and L2 into a sorted list representing their union, except avoid
;; duplication that arises when an item is in both L1 and L2.  L1 and L2 should
;; each be sorted and duplicate-free.  If either L1 or L2 is empty, this should
;; be very fast.
(defund merge-<-and-remove-dups (l1 l2)
  (declare (xargs :guard (and (all-rationalp l1)
                              (all-rationalp l2))))
  (merge-<-and-remove-dups-aux l1 l2 nil))

;; not a good test, as each list has dups?
;(merge-<-and-remove-dups '(1 2 2 3 5 5 5 6 6 8) '(1 2 3 4 5 6 7 7))

(defthm true-listp-of-merge-<-and-remove-dups
  (implies (and (true-listp l1)
                (true-listp l2))
           (true-listp (merge-<-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups))))

(defthm rational-listp-of-merge-<-and-remove-dups
  (implies (and (rational-listp l1)
                (rational-listp l2))
           (rational-listp (merge-<-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups))))

;; special case
(defthm nat-listp-of-merge-<-and-remove-dups
  (implies (and (nat-listp l1)
                (nat-listp l2))
           (nat-listp (merge-<-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups))))

; strengthen to sortedp-< ?
(defthm sortedp-<=-of-merge-<-and-remove-dups
  (implies (and (sortedp-<= l1)
                (sortedp-<= l2))
           (sortedp-<= (merge-<-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups))))

(defthm no-duplicatesp-equal-of-merge-<-and-remove-dups
  (implies (and (sortedp-<= l1)
                (sortedp-<= l2)
                (no-duplicatesp-equal l1)
                (no-duplicatesp-equal l2)
                (all-rationalp l1)
                (all-rationalp l2))
           (no-duplicatesp-equal (merge-<-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups))))

(defthm all-<-of-merge-<-and-remove-dups
  (equal (all-< (merge-<-and-remove-dups l1 l2) bound)
         (and (all-< l1 bound)
              (all-< l2 bound)))
  :hints (("Goal" :in-theory (enable merge-<-and-remove-dups))))

;(equal (merge-<-and-remove-dups '(1 2 2 3 4 4 5) '(0 1 2 3 3 4 6)) '(0 1 2 3 3 4 5 6)) ; note the two 3s in the result
