; A function to remove duplicates from a sorted list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "kestrel/typed-lists-light/all-less-than-or-equal-all" :dir :system)
(include-book "merge-sort-less-than-rules") ;reduce
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(defthm all-<=-of-car-when-all-<=-of-all
  (implies (and (all-<=-all acc list)
                (consp list))
           (all-<= acc (car list))))

(defthmd not-<-of-car-when-<=-all
  (implies (and (<=-all x y)
                (consp y))
           (not (< (car y) x)))
  :hints (("Goal" :in-theory (enable <=-all))))

;; todo: this must exist somewhere?
;; Leaves one member of each run of consecutive duplicates
(defund remove-duplicates-from-sorted-list (list acc)
  (declare (xargs :guard (and (all-natp list)
                              (true-listp list)
                              (all-natp acc)
                              (true-listp acc))))
  (if (endp list)
      (reverse-list acc)
    (let ((first (first list)))
      (if (endp (rest list))
          (reverse-list (cons first acc))
        (if (equal first (second list))
            ;; Drop the first element:
            (remove-duplicates-from-sorted-list (rest list) acc)
          (remove-duplicates-from-sorted-list (rest list) (cons first acc)))))))

(defthm car-of-remove-duplicates-from-sorted-list
  (equal (car (remove-duplicates-from-sorted-list list acc))
         (if (consp acc)
             (nth (+ -1 (len acc)) acc)
           (car list)))
  :hints (("Goal" :in-theory (enable remove-duplicates-from-sorted-list))))

(defthm consp-of-remove-duplicates-from-sorted-list
  (equal (consp (remove-duplicates-from-sorted-list list acc))
         (or (consp list)
             (consp acc)))
  :hints (("Goal" :in-theory (enable remove-duplicates-from-sorted-list))))

(defthm all-<-of-remove-duplicates-from-sorted-list
  (equal (all-< (remove-duplicates-from-sorted-list list acc) bound)
         (and (all-< list bound)
              (all-< acc bound)))
  :hints (("Goal" :in-theory (enable remove-duplicates-from-sorted-list))))

(defthm sortedp-<=-of-remove-duplicates-from-sorted-list
  (equal (sortedp-<= (remove-duplicates-from-sorted-list list acc))
         (and (sortedp-<= list)
              (sortedp-<= (reverse-list acc))
              (all-<=-all acc list)))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :in-theory (enable sortedp-<=
                              remove-duplicates-from-sorted-list
                              not-<-of-car-when-<=-all
                              <=-of-first-and-second-when-sortedp))))
