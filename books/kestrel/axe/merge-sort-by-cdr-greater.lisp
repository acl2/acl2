; Merge sort by > applied to cdrs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-consp")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

(defforall all-cdrs-rationalp (x) (rationalp (cdr x)) :guard (all-consp x))

;; ;fixme redo this (and other!) merge sorts to follow the fast pattern in merge-sort.lisp

(defun merge-by-cdr-> (l1 l2 acc)
  (declare (xargs :measure (+ (len l1) (len l2))
                  :guard (and (all-consp l1)
                              (all-cdrs-rationalp l1)
                              (all-consp l2)
                              (all-cdrs-rationalp l2)
                              (true-listp acc))))
  (cond ((atom l1) (revappend acc l2))
        ((atom l2) (revappend acc l1))
        ((> (cdr (car l1)) (cdr (car l2)))
         (merge-by-cdr-> (cdr l1)
                         l2
                         (cons (car l1) acc)))
        (t (merge-by-cdr-> l1 (cdr l2)
                           (cons (car l2) acc)))))

(defthm acl2-count-of-evens-bound
  (implies (< 1 (len l))
           (< (acl2-count (evens l))
              (acl2-count l))))

(defthm <-of-acl2-count-of-evens
  (implies (consp (cdr l))
           (< (acl2-count (evens l))
              (acl2-count l)))
  :hints (("Goal" :in-theory (enable evens acl2-count))))

(defthm alistp-of-merge-by-cdr->
  (implies (and (alistp l1)
                (alistp l2)
                (alistp acc))
           (alistp (merge-by-cdr-> l1 l2 acc)))
  :hints (("Goal" :in-theory (enable merge-by-cdr->))))

;fixme use defmergesort
(defun merge-sort-by-cdr-> (l)
  (declare (xargs :guard (and (true-listp l) ;why?
                              (all-consp l)
                              (all-cdrs-rationalp l))
                  :hints (("Goal" :in-theory (enable )))
                  :verify-guards nil ;done below
                  ))
  (cond ((atom (cdr l)) l)
        (t (merge-by-cdr-> (merge-sort-by-cdr-> (evens l))
                           (merge-sort-by-cdr-> (odds l))
                           nil))))

(defthm all-conps-of-evens
  (implies (all-consp x)
           (all-consp (evens x))))

(defthm all-consp-of-merge-by-cdr->
  (implies (and (all-consp x)
                (all-consp y)
                (all-consp acc))
           (all-consp (merge-by-cdr-> x y acc))))

(defthm all-consp-of-merge-sort-by-cdr->
  (implies (all-consp x)
           (all-consp (merge-sort-by-cdr-> x))))

(defthm all-cdrs-rationalp-of-evens
  (implies (all-cdrs-rationalp x)
           (all-cdrs-rationalp (evens x))))

(defthm all-cdrs-rationalp-of-merge-by-cdr->
  (implies (and (all-cdrs-rationalp x)
                (all-cdrs-rationalp y)
                (all-cdrs-rationalp acc))
           (all-cdrs-rationalp (merge-by-cdr-> x y acc))))

(defthm all-cdrs-rationalp-of-merge-sort-by-cdr->
  (implies (all-cdrs-rationalp x)
           (all-cdrs-rationalp (merge-sort-by-cdr-> x))))

(verify-guards merge-sort-by-cdr->)

(defthm alistp-of-evens
  (implies (alistp x)
           (alistp (evens x)))
  :hints (("Goal" :induct (EVENS X)
           :in-theory (enable evens alistp))))

(defthm alistp-of-odds
  (implies (alistp x)
           (alistp (odds x))))

(defthm alistp-of-merge-sort-by-cdr->
  (implies (alistp x)
           (alistp (merge-sort-by-cdr-> x)))
  :hints (("Goal" :in-theory (enable merge-sort-by-cdr->))))
