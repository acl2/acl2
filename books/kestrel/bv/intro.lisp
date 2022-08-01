; Rules to introduce BV ops
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvand")
(include-book "bvor")
(include-book "bvxor")
(include-book "bvplus")
(include-book "bvminus")

;; We'll keep these disabled as they may conflict with opening up the BV
;; functions.

(defthmd bvchop-of-logand-becomes-band
  (equal (bvchop size (logand x y))
         (bvand size x y))
  :hints (("Goal" :in-theory (enable bvand))))

(defthmd bvchop-of-logior-becomes-bvor
  (equal (bvchop size (logior x y))
         (bvor size x y))
  :hints (("Goal" :in-theory (enable bvor))))

(defthmd bvchop-of-logxor-becomes-bvxor
  (equal (bvchop size (logxor x y))
         (bvxor size x y))
  :hints (("Goal" :in-theory (enable bvxor))))

(defthmd bvchop-of-+-becomes-bvplus
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop size (+ x y))
                  (bvplus size x y)))
  :hints (("Goal" :in-theory (enable bvplus))))

(defthmd bvchop-of---becomes-bvminus
  (implies (and (integerp x)
                (integerp y))
           (equal (bvchop size (- x y))
                  (bvminus size x y)))
  :hints (("Goal" :in-theory (enable bvminus))))
