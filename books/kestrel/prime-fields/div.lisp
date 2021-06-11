; Prime fields library: Division
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "inv")

;; Divide x by y modulo the prime.
(defund div (x y p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (fep y p)
                              (not (equal 0 y)))))
  (mul x (inv y p) p))

(defthm natp-of-div
  (natp (div x y p))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable div))))

(defthm fep-of-div
  (implies (and (< 1 p)
                (integerp p))
           (fep (div x y p) p))
  :hints (("Goal" :in-theory (enable div))))

(defthm div-of-1-arg2
  (implies (and (< 1 p)
                (integerp p)
                (integerp x))
           (equal (div x 1 p)
                  (mod x p)))
  :hints (("Goal" :in-theory (enable div inv))))

(defthm <-of-div
  (implies (and (< 1 p) ; gen?
                (integerp p))
           (< (div x y p) p))
  :hints (("Goal" :in-theory (enable div))))
