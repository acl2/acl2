; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "std/osets/top" :dir :system)

(include-book "../insert")
(include-book "../set")
(include-book "mk-random")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mk-random-set
  ((size natp)
   (set setp)
   (elements true-listp)
   state)
  :returns (mv (set setp)
               (elements nat-listp)
               state)
  (if (zp size)
      (mv set elements state)
    (b* (((mv obj state)
          (mk-random-obj state)))
      (mk-random-set (- size 1)
                     (insert obj set)
                     (cons obj elements)
                     state))))

(define mk-random-oset
  ((size natp)
   (set set::setp)
   (elements true-listp)
   state)
  :returns (mv (set set::setp)
               (elements nat-listp)
               state)
  (if (zp size)
      (mv set elements state)
    (b* (((mv obj state)
          (mk-random-obj state)))
      (mk-random-oset (- size 1)
                      (set::insert obj set)
                      (cons obj elements)
                      state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mk-consecutive-nat-set
  ((size natp)
   (set setp)
   (elements true-listp))
  :returns (mv (set setp)
               (elements nat-listp))
  (if (zp size)
      (mv set elements)
    (mk-consecutive-nat-set (- size 1)
                            (insert size set)
                            (cons size set))))

(define mk-consecutive-nat-oset
  ((size natp)
   (set set::setp)
   (elements))
  :returns (mv (set set::setp)
               (elements nat-listp))
  (if (zp size)
      (mv set elements)
    (mk-consecutive-nat-oset (- size 1)
                             (set::insert size set)
                             (cons size elements))))
