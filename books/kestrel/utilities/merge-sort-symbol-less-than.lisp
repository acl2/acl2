; A lightweight book about the built-in function merge-sort-symbol<
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Make sure this includes all of the rules we'd get if
;; merge-sort-symbol< were defined using defmergesort.

;; TODO: Make this an equality
(defthm symbol-listp-of-merge-symbol<
  (implies (and (symbol-listp acc)
                (symbol-listp l1)
                (symbol-listp l2))
           (symbol-listp (merge-symbol< l1 l2 acc))))

(defthm symbol-listp-of-evens
  (implies (symbol-listp l)
           (symbol-listp (evens l)))
  :hints (("Goal" :induct (evens l)
           :in-theory (enable evens))))

(defthm symbol-listp-of-merge-sort-symbol<
  (implies (symbol-listp l)
           (symbol-listp (merge-sort-symbol< l))))

(defthm consp-of-merge-symbol<
  (equal (consp (merge-symbol< l1 l2 acc))
         (or (consp l1)
             (consp l2)
             (consp acc)))
  :hints (("Goal" :in-theory (enable merge-symbol<))))

(defthm consp-of-merge-sort-symbol<
  (equal (consp (merge-sort-symbol< l))
         (consp l))
  :hints (("Goal" :in-theory (enable merge-sort-symbol<))))
