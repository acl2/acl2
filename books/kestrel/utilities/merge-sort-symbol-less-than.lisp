; A lightweight book about the built-in function merge-sort-symbol<
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/no-duplicatesp-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/evens-and-odds" :dir :system))
(local (include-book "kestrel/typed-lists-light/strict-symbol-less-than-sortedp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;; TODO: Make sure this includes all of the rules we'd get if
;; merge-sort-symbol< were defined using defmergesort.

;; todo: disable merge-sort-symbol<

;; TODO: Make this an equality
(defthm symbol-listp-of-merge-symbol<
  (implies (and (symbol-listp acc)
                (symbol-listp l1)
                (symbol-listp l2))
           (symbol-listp (merge-symbol< l1 l2 acc))))

(defthm consp-of-merge-symbol<
  (equal (consp (merge-symbol< l1 l2 acc))
         (or (consp l1)
             (consp l2)
             (consp acc)))
  :hints (("Goal" :in-theory (enable merge-symbol<))))

(defthm strict-symbol<-sortedp-of-merge-symbol<
  (implies (and (strict-symbol<-sortedp lst1)
                (strict-symbol<-sortedp lst2)
                (strict-symbol<-sortedp (reverse acc))
                (symbol-listp lst1)
                (symbol-listp lst2)
                (symbol-listp acc)
                (not (intersection-equal lst1 lst2))
                ;; acc has the smallest items:
                (implies (and (consp lst1) (consp acc))
                         (symbol< (car acc) (car lst1)))
                (implies (and (consp lst2) (consp acc))
                         (symbol< (car acc) (car lst2))))
           (strict-symbol<-sortedp (merge-symbol< lst1 lst2 acc)))
  :hints (("Goal" :induct (merge-symbol< lst1 lst2 acc)
           :in-theory (enable strict-symbol<-sortedp merge-symbol<))))

;; Special case for acc=nil
(defthm strict-symbol<-sortedp-of-merge-symbol<-of-nil
  (implies (and (strict-symbol<-sortedp lst1)
                (strict-symbol<-sortedp lst2)
                (symbol-listp lst1)
                (symbol-listp lst2)
                (not (intersection-equal lst1 lst2)))
           (strict-symbol<-sortedp (merge-symbol< lst1 lst2 nil))))

(defthm intersection-equal-of-merge-symbol<-arg2-iff
  (iff (intersection-equal x (merge-symbol< lst1 lst2 acc))
       (or (intersection-equal x lst1)
           (intersection-equal x lst2)
           (intersection-equal x acc)))
  :hints (("Goal" :in-theory (enable merge-symbol<))))

(defthm intersection-equal-of-merge-symbol<-arg1-iff
  (iff (intersection-equal (merge-symbol< lst1 lst2 acc) x)
       (or (intersection-equal lst1 x)
           (intersection-equal lst2 x)
           (intersection-equal acc x)))
  :hints (("Goal" :in-theory (enable merge-symbol<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Make this an equality
(defthm symbol-listp-of-merge-sort-symbol<
  (implies (symbol-listp l)
           (symbol-listp (merge-sort-symbol< l))))

(defthm consp-of-merge-sort-symbol<
  (equal (consp (merge-sort-symbol< l))
         (consp l))
  :hints (("Goal" :in-theory (enable merge-sort-symbol<))))

;; need perm to do this right
;; ;; Sorting doesn't effect whether there is an intersection
(defthm intersection-equal-of-merge-sort-symbol<-arg1-iff
  (iff (intersection-equal (merge-sort-symbol< l1) l2)
       (intersection-equal l1 l2))
  :hints (("Goal" :in-theory (e/d (merge-sort-symbol<
                                   intersection-equal-when-intersection-equal-of-evens
                                   intersection-equal-when-intersection-equal-of-odds)
                                  (intersection-equal-symmetric-iff)))))

(defthm intersection-equal-of-merge-sort-symbol<-arg2-iff
  (iff (intersection-equal l2 (merge-sort-symbol< l1))
       (intersection-equal l1 l2))
  :hints (("Goal" :use intersection-equal-of-merge-sort-symbol<-arg1-iff
           :in-theory (disable intersection-equal-of-merge-sort-symbol<-arg1-iff))))

(defthm strict-symbol<-sortedp-of-merge-sort-symbol<
  (implies (and (symbol-listp l)
                ;; If there are duplicates, the sorting can't be strict:
                (no-duplicatesp-equal l))
           (strict-symbol<-sortedp (merge-sort-symbol< l))))
