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
;; See also merge-less-than-and-remove-dups.lisp.

;; TODO: Avoid nested inductions

(include-book "sortedp-greater-than-or-equal")
(include-book "kestrel/typed-lists-light/all-rationalp" :dir :system)
(include-book "kestrel/typed-lists-light/all-greater-than-or-equal-all" :dir :system)
(local (include-book "kestrel/typed-lists-light/all-less-than-or-equal-all" :dir :system))
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "kestrel/typed-lists-light/all-greater" :dir :system)
(local (include-book "merge-sort-less-than-rules")) ; todo: move some of these
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/rational-lists" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))

;; (local (in-theory (enable >=-of-car-and-cadr-when-sortedp->=)))

;move
(local
  (defthmd all->=-all-becomes-all-<=-all
    (equal (all->=-all x y)
           (all-<=-all y x))
    :hints (("Goal" :induct (all-<=-all y x) ; found by advice tool
             :in-theory (enable all->=-all
                                all-<=-all
                                all->=)))))

;move
(local
  (defthmd not-intersection-equal-when-all->-of-car-and-sortedp->=
    (implies (and (all-> y (car x))
                  (sortedp->= x))
             (not (intersection-equal x y)))
    :hints (("Goal" :in-theory (enable all-> sortedp->= intersection-equal)))))

;move
(local
  (defthmd >-of-car-and-cadr-when-sortedp->=-and-no-duplicatesp-equal
    (implies (and (sortedp->= x)
                  (no-duplicatesp-equal x)
                  (consp (cdr x))
                  (all-rationalp x))
             (> (car x) (cadr x)))
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable sortedp->= no-duplicatesp-equal)))))

;; Merges sorted (decreasing) lists and removes duplicates that appear in both lists.
;; L1 and L2 should be sorted in decreasing order (and be duplicate free).
;; ACC should contain the largest items (larger than anything in L1 or L2), sorted in increasing order.
(defund merge->-and-remove-dups-aux (l1 l2 acc)
  (declare (xargs :guard (and (all-rationalp l1)
                              (all-rationalp l2)
                              (true-listp acc))
                  :measure (+ (len l1) (len l2))))
  (cond ((atom l1) (revappend acc l2))
        ((atom l2) (revappend acc l1))
        ((equal (car l1) (car l2)) ;drop one copy:
         (merge->-and-remove-dups-aux (cdr l1) l2 acc))
        ((> (car l1) (car l2))
         (merge->-and-remove-dups-aux (cdr l1)
                                      l2 (cons (car l1) acc)))
        (t (merge->-and-remove-dups-aux l1 (cdr l2)
                                        (cons (car l2) acc)))))

(local
  (defthm nat-listp-of-merge->-and-remove-dups-aux
    (implies (and (nat-listp l1)
                  (nat-listp l2)
                  (nat-listp acc))
             (nat-listp (merge->-and-remove-dups-aux l1 l2 acc)))
    :hints (("Goal" :in-theory (enable merge->-and-remove-dups-aux)))))

(local
  (defthm true-listp-of-merge->-and-remove-dups-aux
    (implies (and (true-listp l1)
                  (true-listp l2))
             (true-listp (merge->-and-remove-dups-aux l1 l2 acc)))
    :hints (("Goal" :in-theory (enable merge->-and-remove-dups-aux)))))

(local
  (defthm rational-listp-of-merge->-and-remove-dups-aux
    (implies (and (rational-listp l1)
                  (rational-listp l2)
                  (rational-listp acc))
             (rational-listp (merge->-and-remove-dups-aux l1 l2 acc)))
    :hints (("Goal" :in-theory (enable merge->-and-remove-dups-aux)))))

;move and rename
(local
  (defthm helper
    (implies (and (<= (CAR L1) x)
                  (SORTEDP->= L1)
                  (consp l1))
             (ALL-<= L1 x))
    :hints (("Goal" :induct (ALL-<= l1 X)
             :in-theory (enable ALL-<=-ALL
                                ALL-<=
                                <=-OF-CAR-AND-CAR-WHEN-ALL-<=-ALL
                                >=-of-car-and-cadr-when-sortedp->=-linear)))))

(local
  (defthm sortedp->=-of-merge->-and-remove-dups-aux
    (implies (and (sortedp->= l1)
                  (sortedp->= l2)
                  (sortedp->= (reverse-list acc))
                  (all->=-all acc l1)
                  (all->=-all acc l2))
             (sortedp->= (merge->-and-remove-dups-aux l1 l2 acc)))
    :hints (("Goal" :expand ((merge->-and-remove-dups-aux l1 l2 acc))
             :induct (merge->-and-remove-dups-aux l1 l2 acc)
             :in-theory (enable merge->-and-remove-dups-aux
                                revappend-becomes-append-of-reverse-list
                                ;all->=-all
                                all->=-all-becomes-all-<=-all
                                <=-of-car-and-car-when-all-<=-all)))))

(local ;move and rename
  (defthm helper2
    (implies (and (all-> x free)
                  (<= a free))
             (all-> x a))
    :hints (("Goal" :in-theory (enable all->)))))

(local ;move
  (defthm not-member-equal-when-all->
    (implies (all-> x a)
             (not (member-equal a x)))
    :hints (("Goal" :in-theory (enable all-> member-equal)))))

(local
  (defthm no-duplicatesp-equal-of-merge->-and-remove-dups-aux
    (implies (and (sortedp->= l1)
                  (sortedp->= l2)
                  (sortedp->= (reverse-list acc))
                  (implies (consp l1) (all-> acc (first l1)))
                  (implies (consp l2) (all-> acc (first l2)))
                  (no-duplicatesp-equal l1)
                  (no-duplicatesp-equal l2)
                  (no-duplicatesp-equal acc)
                  (all-rationalp l1)
                  (all-rationalp l2))
             (no-duplicatesp-equal (merge->-and-remove-dups-aux l1 l2 acc)))
    :hints (("Goal" :in-theory (enable merge->-and-remove-dups-aux
                                       revappend-becomes-append-of-reverse-list
                                       not-intersection-equal-when-all->-of-car-and-sortedp->=
                                       >-of-car-and-cadr-when-sortedp->=-and-no-duplicatesp-equal
                                       >=-of-car-and-cadr-when-sortedp->=-linear)))))

(local
 (defthm all-<-of-merge->-and-remove-dups-aux
   (implies (and (all-< l1 bound)
                 (all-< l2 bound)
                 (all-< acc bound))
            (all-< (merge->-and-remove-dups-aux l1 l2 acc) bound))
   :hints (("Goal" :in-theory (enable merge->-and-remove-dups-aux)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Merge L1 and L2 into a sorted (decreasing) list representing their union, except avoid
;; duplication that arises when an item is in both L1 and L2.  L1 and L2 should
;; each be sorted (decreasing) and duplicate-free.  If either L1 or L2 is empty, this should
;; be very fast.
(defund merge->-and-remove-dups (l1 l2)
  (declare (xargs :guard (and (all-rationalp l1)
                              (all-rationalp l2))))
  (merge->-and-remove-dups-aux l1 l2 nil))

(defthm true-listp-of-merge->-and-remove-dups
  (implies (and (true-listp l1)
                (true-listp l2))
           (true-listp (merge->-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge->-and-remove-dups))))

(defthm rational-listp-of-merge->-and-remove-dups
  (implies (and (rational-listp l1)
                (rational-listp l2))
           (rational-listp (merge->-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge->-and-remove-dups))))

;; special case
(defthm nat-listp-of-merge->-and-remove-dups
  (implies (and (nat-listp l1)
                (nat-listp l2))
           (nat-listp (merge->-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge->-and-remove-dups))))

; strengthen to sortedp-> ?
(defthm sortedp->=-of-merge->-and-remove-dups
  (implies (and (sortedp->= l1)
                (sortedp->= l2))
           (sortedp->= (merge->-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge->-and-remove-dups))))

(defthm no-duplicatesp-equal-of-merge->-and-remove-dups
  (implies (and (sortedp->= l1)
                (sortedp->= l2)
                (no-duplicatesp-equal l1)
                (no-duplicatesp-equal l2)
                (all-rationalp l1)
                (all-rationalp l2))
           (no-duplicatesp-equal (merge->-and-remove-dups l1 l2)))
  :hints (("Goal" :in-theory (enable merge->-and-remove-dups))))

(defthm all-<-of-merge->-and-remove-dups
  (implies (and (all-< l1 bound)
                (all-< l2 bound))
           (all-< (merge->-and-remove-dups l1 l2) bound))
  :hints (("Goal" :in-theory (enable merge->-and-remove-dups))))

;(equal (merge->-and-remove-dups '(5 4 4 3 2 2 1) '(6 4 3 3 2 1 0)) '(6 5 4 3 3 2 1 0)) ; note the two 3s in the result
