; Prime fields library: Multiplicative inverse
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "pow")
(include-book "minus1")

;; Compute the multiplicative inverse of x modulo the prime.
;; See theorem inv-correct below.
(defund inv (x p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (not (equal x 0)))
                  :guard-hints (("Goal" :in-theory (enable minus1)))))
  (pow x (+ -1 (minus1 p)) p))

(defthm natp-of-inv
  (natp (inv x p))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable inv))))

(defthm fep-of-inv
  (implies (and (< 1 p)
                (integerp p))
           (fep (inv x p) p))
  :hints (("Goal" :in-theory (enable inv minus1))))

(defthm <-of-inv
  (implies (and (< 1 p) ;so that 1 is a fep
                (integerp p))
           (< (inv x p) p))
  :hints (("Goal" :use (:instance fep-of-inv)
           :in-theory (disable fep-of-inv))))
