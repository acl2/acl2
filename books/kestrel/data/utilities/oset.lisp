; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(include-book "std/osets/top" :dir :system)

(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))

(include-book "total-order/total-order")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled osetp-of-append
  (implies (and (setp x)
                (setp y))
           (equal (setp (append x y))
                  (or (not x)
                      (not y)
                      (<< (car (last x)) (car y)))))
  :induct t
  :enable (append
           setp))

(defruled osetp-of-cons
  (implies (setp y)
           (equal (setp (cons x y))
                  (or (not y)
                      (<< x (car y)))))
  :enable setp)

(defruled cardinality-becomes-len-when-osetp
  (implies (setp oset)
           (equal (cardinality oset)
                  (len oset)))
  :induct t
  :enable (cardinality
           emptyp
           tail
           setp))

(defruled setp-of-cdr-when-osetp
  (implies (setp l)
           (setp (cdr l)))
  :enable setp)

;; Splitting an oset: both halves of an append are osets themselves.

(defruled setp-of-prefix-when-osetp-of-append
  (implies (and (true-listp x)
                (setp (append x y)))
           (setp x))
  :induct t
  :enable (setp
           append))

(defruled setp-of-suffix-when-osetp-of-append
  (implies (setp (append x y))
           (setp y))
  :induct (append x y)
  :enable (setp
           append
           setp-of-cdr-when-osetp))

;; An oset is strictly increasing, so its head is below every later element,
;; and every element of a prefix is below the head of what follows.

(defruled <<-of-car-when-member-equal-of-cdr
  (implies (and (setp l)
                (member-equal x (cdr l)))
           (<< (car l) x))
  :induct (member-equal x l)
  :enable (setp
           member-equal
           set::not-member-when-smaller
           setp-of-cdr-when-osetp
           <<-rules))

(defruled <<-of-cars-when-osetp-of-append
  (implies (and (setp (append a b))
                (consp a)
                (consp b))
           (<< (car a) (car b)))
  :induct (append a b)
  :enable (setp
           append
           setp-of-cdr-when-osetp
           <<-rules))

(defruled <<-across-append-when-osetp
  (implies (and (setp (append a b))
                (member-equal x a)
                (consp b))
           (<< x (car b)))
  :induct (append a b)
  :enable (setp
           append
           member-equal
           setp-of-cdr-when-osetp
           <<-of-cars-when-osetp-of-append
           <<-rules))

;; An oset has no duplicates, so membership in the tail is membership anywhere
;; but at the head.

(defruled member-equal-of-cdr-when-osetp
  (implies (setp l)
           (iff (member-equal x (cdr l))
                (and (not (equal x (car l)))
                     (member-equal x l))))
  :induct t
  :enable (setp
           set::not-member-when-smaller
           <<-rules))
