; BV Library: The definition of getbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See getbit.lisp for theorems about getbit.

(include-book "slice-def")
(local (include-book "../arithmetic-light/floor")) ; for FLOOR-DIVIDE-BY-SAME
(local (include-book "../arithmetic-light/expt"))
(local (include-book "../arithmetic-light/mod"))

;; local copy, to support the :type-prescription of getbit
(local
  (defthm bitp-of-bvchop-of-1-type
    (bitp (bvchop 1 x))
    :hints (("Goal" :in-theory (enable bvchop)))
    :rule-classes :type-prescription))

;; local copy, to support the :type-prescription of getbit
(local
  (defthm bitp-of-slice-same-type
    (bitp (slice n n x))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable slice)))))

;; Extract bit N from the bit vector X, where the numbering starts at 0 for the
;; least significant bit.
;; Similar to bitn in books/rtl.
(defund getbit (n x)
  (declare (xargs :guard (and (natp n)
                              (integerp x))
                  :type-prescription (bitp (getbit n x))
                  :split-types t
                  :guard-hints (("Goal"
                                 :use (:instance floor-divide-by-same
                                                 (i x)
                                                 (j (expt 2 n))
                                                 (k (expt 2 n)))
                                 :in-theory (e/d (ash slice logtail bvchop)
                                                 (floor-unique-equal-version)))))
           (type (integer 0 *) n)
           (type integer x))
  (mbe :logic (slice n n x)
       ;;i think this is faster than calling slice:
       :exec (mod (ash x (- n)) 2)))
