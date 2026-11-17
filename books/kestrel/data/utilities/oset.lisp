; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/defrule" :dir :system)

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(include-book "std/osets/top" :dir :system)

(local (include-book "kestrel/lists-light/butlast" :dir :system))
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
           append))

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
           <<-rules))

(defruled <<-of-cars-when-osetp-of-append
  (implies (and (setp (append a b))
                (consp a)
                (consp b))
           (<< (car a) (car b)))
  :induct (append a b)
  :enable (setp
           append
           <<-rules))

(defruled <<-across-append-when-osetp
  (implies (and (setp (append a b))
                (member-equal x a)
                (consp b))
           (<< x (car b)))
  :induct (append a b)
  :enable (setp
           append
           <<-of-cars-when-osetp-of-append))

;; So every element of a prefix is below every element of what follows.

(defruled <<-across-append-of-members-when-osetp
  (implies (and (setp (append a b))
                (member-equal x a)
                (member-equal y b))
           (<< x y))
  :cases ((equal y (car b)))
  :use (<<-across-append-when-osetp
        (:instance setp-of-suffix-when-osetp-of-append (x a) (y b))
        (:instance <<-of-car-when-member-equal-of-cdr (l b) (x y)))
  :enable <<-rules)

;; An oset has no duplicates, so no element is on both sides of an append.

(defruled not-member-equal-of-prefix-when-osetp-of-append
  (implies (and (setp (append a b))
                (member-equal x b))
           (not (member-equal x a)))
  :use (:instance <<-across-append-of-members-when-osetp (y x))
  :enable <<-rules)

(defruled not-member-equal-of-suffix-when-osetp-of-append
  (implies (and (setp (append a b))
                (member-equal x a))
           (not (member-equal x b)))
  :enable not-member-equal-of-prefix-when-osetp-of-append)

;; Likewise, membership in the tail is membership anywhere but at the head.

(defruled member-equal-of-cdr-when-osetp
  (implies (setp l)
           (iff (member-equal x (cdr l))
                (and (not (equal x (car l)))
                     (member-equal x l))))
  :enable (setp
           set::not-member-when-smaller
           <<-rules))

;; Likewise, membership in all but the last element is membership anywhere but
;; at the last.

(defrulel member-equal-of-car-of-last
  (implies (consp l)
           (member-equal (car (last l)) l))
  :induct (last l)
  :enable last)

(defrulel not-equal-of-car-of-last-when-osetp-of-cons
  (implies (and (setp (cons a b))
                (consp b))
           (not (equal a (car (last b)))))
  :use (:instance <<-of-car-when-member-equal-of-cdr
                  (l (cons a b))
                  (x (car (last b))))
  :enable <<-rules)

(defruled member-equal-of-butlast-when-osetp
  (implies (setp l)
           (iff (member-equal x (butlast l 1))
                (and (not (equal x (car (last l))))
                     (member-equal x l))))
  :induct (last l)
  :enable (last
           setp-of-cdr-when-osetp))

;; An element of an oset is below whatever its last element is below, and above
;; whatever its first element is above.

(defrulel <<-of-car-when-<<-of-car-of-last
  (implies (and (setp l)
                (<< (car (last l)) y))
           (<< (car l) y))
  :induct (last l)
  :enable (last
           setp
           <<-rules))

(defruled <<-when-member-equal-and-<<-of-car-of-last
  (implies (and (member-equal x l)
                (setp l)
                (<< (car (last l)) y))
           (<< x y))
  :induct (last l)
  :enable (last
           setp-of-cdr-when-osetp))

(defruled <<-when-member-equal-and-<<-of-arg1-and-car
  (implies (and (member-equal y l)
                (setp l)
                (<< x (car l)))
           (<< x y))
  :induct (member-equal y l)
  :enable (member-equal
           setp
           <<-rules))
