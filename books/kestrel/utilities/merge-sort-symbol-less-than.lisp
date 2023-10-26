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
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/strict-symbol-less-than-sortedp" :dir :system))

;; TODO: Make sure this includes all of the rules we'd get if
;; merge-sort-symbol< were defined using defmergesort.

;; todo: disable merge-sort-symbol<

;move
(defthm symbol-listp-of-evens
  (implies (symbol-listp l)
           (symbol-listp (evens l)))
  :hints (("Goal" :induct (evens l)
           :in-theory (enable evens))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(local
  (defthm strict-symbol<-sortedp-of-merge-symbol<
    (implies (and (acl2::strict-symbol<-sortedp lst1)
                  (acl2::strict-symbol<-sortedp lst2)
                  (acl2::strict-symbol<-sortedp (reverse acc))
                  (symbol-listp lst1)
                  (symbol-listp lst2)
                  (symbol-listp acc)
                  (not (intersection-equal lst1 lst2))
                  ;; acc has the smallest items:
                  (implies (and (consp lst1) (consp acc))
                           (symbol< (car acc) (car lst1)))
                  (implies (and (consp lst2) (consp acc))
                           (symbol< (car acc) (car lst2))))
             (acl2::strict-symbol<-sortedp (acl2::merge-symbol< lst1 lst2 acc)))
    :hints (("Goal" :induct (acl2::merge-symbol< lst1 lst2 acc)
             :in-theory (enable acl2::strict-symbol<-sortedp acl2::merge-symbol<)))))

;; Special case for acc=nil
(defthmd strict-symbol<-sortedp-of-merge-symbol<-of-nil
  (implies (and (acl2::strict-symbol<-sortedp lst1)
                (acl2::strict-symbol<-sortedp lst2)
                (symbol-listp lst1)
                (symbol-listp lst2)
                (not (intersection-equal lst1 lst2)))
           (acl2::strict-symbol<-sortedp (acl2::merge-symbol< lst1 lst2 nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Make this an equality
(defthm symbol-listp-of-merge-sort-symbol<
  (implies (symbol-listp l)
           (symbol-listp (merge-sort-symbol< l))))

(defthm consp-of-merge-sort-symbol<
  (equal (consp (merge-sort-symbol< l))
         (consp l))
  :hints (("Goal" :in-theory (enable merge-sort-symbol<))))
