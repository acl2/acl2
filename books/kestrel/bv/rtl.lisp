; Connections between this BV library and the RTL library
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rtl/rel11/lib/defs" :dir :system)
(include-book "getbit")
(local (include-book "kestrel/arithmetic-light/floor-mod-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

(local
  (defthm floor-of-*-of-/-and-1-alt
    (equal (FLOOR (* (/ i) i2) 1)
           (floor i2 i))
    :hints (("Goal" :in-theory (enable floor)))))

(defthm bits-becomes-slice
  (implies (and (integerp x)
                (<= j i)
                (integerp i)
                (natp j))
           (equal (rtl::bits x i j)
                  (slice i j x)))
  :hints (("Goal" :in-theory (enable rtl::bits RTL::FL slice LOGTAIL$INLINE bvchop
                                     ;mod-cancel
                                     ))))

(defthm bitn-becomes-getbit
  (implies (and (integerp x)
                (natp n))
           (equal (rtl::bitn x n)
                  (getbit n x)))
  :hints (("Goal" :in-theory (enable rtl::bitn))))

(defthm bvcep-becomes-unsigned-byte-p
  (implies (natp n)
           (equal (rtl::bvecp x n)
                  (unsigned-byte-p n x)))
  :hints (("Goal" :in-theory (enable rtl::bvecp unsigned-byte-p))))
