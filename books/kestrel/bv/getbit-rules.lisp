; Mixed theorems about getbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "getbit")
(include-book "bitnot")
(local (include-book "slice-rules"))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(defthm getbit-of-minus
  (implies (and (integerp x)
                (natp n)
                )
           (equal (getbit n (- x))
                  (if (EQUAL (BVCHOP N X) 0)
                      (getbit n x)
                    (bitnot (getbit n x)))))
  :hints (("Goal" :in-theory (e/d (getbit bitnot)
                                  (BVCHOP-1-BECOMES-GETBIT
                                   SLICE-BECOMES-GETBIT
                                   ;BITNOT-OF-SLICE ;bozo
                                   ;BITXOR-OF-SLICE-ARG2 ;loops with defn getbit
                                   )))))

(defthmd floor-when-equal-of-floor-and-0-and->=
  (implies (and (equal (floor x y) 0)
                (<= xsmall x)
                (posp y)
                (natp n)
                (natp x)
                (natp xsmall))
           (equal (floor xsmall y)
                  0)))

(defthmd logtail-when-equal-of-logtail-and-0-and->=
  (implies (and (equal (logtail$inline n x) 0)
                (<= xsmall x)
                (natp n)
                (integerp x)
                (natp xsmall)
                )
           (equal (logtail$inline n xsmall)
                  0))
  :hints (("Goal" :in-theory (enable logtail
                                     floor-when-equal-of-floor-and-0-and->=))))

(defthm getbit-of-floor-when-top-bit-0
  (implies (and (equal (getbit n x) 0)
                (unsigned-byte-p (+ 1 n) x)
                (posp y)
                (integerp x)
                (natp n))
           (equal (getbit n (floor x y))
                  0))
  :hints (("Goal" :in-theory (e/d (getbit slice logtail-when-equal-of-logtail-and-0-and->=)
                                  (BVCHOP-1-BECOMES-GETBIT
                                   SLICE-BECOMES-GETBIT)))))
