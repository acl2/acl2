; Oset Utilities
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

(include-book "std/osets/top" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc oset-utilities
  :parents (acl2::kestrel-utilities)
  :short "Utilities for
          <see topic='@(url std/osets)'>finite sets</see>.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist list-in (x set)
  :guard (and (true-listp x)
              (setp set))
  :parents (oset-utilities)
  :short "Lift @(tsee in) to lists."
  (in x set)
  :true-listp nil
  :elementp-of-nil :unknown
  ///

  (std::defrule list-in-of-sfix-2
    (equal (list-in list (sfix set))
           (list-in list set))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc typed-osets
  :parents (oset-utilities)
  :short "Typed <see topic='@(url std/osets)'>finite sets</see>,
          i.e. finite sets whose elements all belong to certain types.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc osets-of-natural-numbers
  :parents (typed-osets)
  :short "<see topic='@(url std/osets)'>Finite sets</see>
          of <see topic='@(url acl2::natp)'>natural numbers</see>.")

(std::define set-all-natp ((set setp))
  :returns (yes/no booleanp)
  :parents (osets-of-natural-numbers)
  :short "Check if all the elements of a set are natural numbers."
  (or (empty set)
      (and (natp (head set))
           (set-all-natp (tail set))))
  ///

  (std::defrule set-all-natp-of-insert
    (equal (set-all-natp (insert nat nats))
           (and (natp nat)
                (set-all-natp (sfix nats)))))

  (std::defrule set-all-natp-of-union
    (equal (set-all-natp (union nats1 nats2))
           (and (set-all-natp (sfix nats1))
                (set-all-natp (sfix nats2))))
    :induct (union nats1 nats2)
    :enable union))

(std::define nat-setp (x)
  :returns (yes/no booleanp)
  :parents (osets-of-natural-numbers)
  :short "Recognize finite sets of natural numbers."
  (and (setp x)
       (set-all-natp x))
  ///

  (std::defrule setp-when-nat-setp
    (implies (nat-setp nats)
             (setp nats)))

  (std::defrule nat-setp-of-insert
    (equal (nat-setp (insert nat nats))
           (and (natp nat)
                (nat-setp (sfix nats)))))

  (std::defrule nat-setp-of-union
    (equal (nat-setp (union nats1 nats2))
           (and (nat-setp (sfix nats1))
                (nat-setp (sfix nats2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc osets-of-integer-numbers
  :parents (typed-osets)
  :short "<see topic='@(url std/osets)'>Finite sets</see>
          of <see topic='@(url acl2::integerp)'>integer numbers</see>.")

(std::define set-all-integerp ((set setp))
  :returns (yes/no booleanp)
  :parents (osets-of-integer-numbers)
  :short "Check if all the elements of a set are integer numbers."
  (or (empty set)
      (and (integerp (head set))
           (set-all-integerp (tail set))))
  ///

  (std::defrule set-all-integerp-of-insert
    (equal (set-all-integerp (insert int ints))
           (and (integerp int)
                (set-all-integerp (sfix ints)))))

  (std::defrule set-all-integerp-of-union
    (equal (set-all-integerp (union ints1 ints2))
           (and (set-all-integerp (sfix ints1))
                (set-all-integerp (sfix ints2))))
    :induct (union ints1 ints2)
    :enable union))

(std::define integer-setp (x)
  :returns (yes/no booleanp)
  :parents (osets-of-integer-numbers)
  :short "Recognize finite sets of integer numbers."
  (and (setp x)
       (set-all-integerp x))
  ///

  (std::defrule setp-when-integer-setp
    (implies (integer-setp ints)
             (setp ints)))

  (std::defrule integer-setp-of-insert
    (equal (integer-setp (insert int ints))
           (and (integerp int)
                (integer-setp (sfix ints)))))

  (std::defrule integer-setp-of-union
    (equal (integer-setp (union ints1 ints2))
           (and (integer-setp (sfix ints1))
                (integer-setp (sfix ints2))))))
