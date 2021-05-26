; Prime fields library: minus1
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "fep")

;; this is equal to p-1, but it can help to think of it as "negative 1"
(defund minus1 (p)
  (declare (xargs :guard (integerp p)))
  (+ -1 p))

(defthm integerp-of-minus1
  (implies (integerp p)
           (integerp (minus1 p)))
  :hints (("Goal" :in-theory (enable fep minus1))))

;; -1 is in the field
(defthm fep-of-minus1
  (implies (posp p)
           (fep (minus1 p) p))
  :hints (("Goal" :in-theory (enable fep minus1))))

(defthm not-equal-of-0-and-minus1
  (implies (< 1 p)
           (not (equal 0 (minus1 p))))
  :hints (("Goal" :in-theory (enable fep minus1))))

(defthm natp-of-one-less-than-minus1
  (implies (and (integerp p)
                (< 1 p))
           (natp (+ -1 (minus1 p))) ;the addition here is not the field addition
           )
  :hints (("Goal" :in-theory (enable minus1))))
