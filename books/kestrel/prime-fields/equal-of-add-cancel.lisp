; Prime fields library: Non-bind-free rules to cancel common addends
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; NOTE: The rules in this file may be subsumed by the bind-free rules and in
;; fact may interfere with them.

(include-book "prime-fields")
(local (include-book "prime-fields-rules"))
(local (include-book "../arithmetic-light/mod"))

(defthm equal-of-add-and-add-cancel-1-gen
  (implies (posp p)
           (equal (equal (add x y p) (add x z p))
                  (equal (mod (ifix y) p) (mod (ifix z) p))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add sub))))

(defthm equal-of-add-and-add-cancel-2
  (implies (and (integerp y) ;(fep y p)
                (integerp z) ;(fep z p)
                (posp p))
           (equal (equal (add x y p) (add z x p))
                  (equal (mod y p) (mod z p))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add sub))))

(defthm equal-of-add-and-add-cancel-3
  (implies (and ;(integerp x) ;(fep x p)
                (integerp y) ;(fep y p)
                (integerp z) ;(fep z p)
                (posp p))
           (equal (equal (add y x p) (add x z p))
                  (equal (mod y p) (mod z p))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add sub))))

(defthm equal-of-add-and-add-cancel-4
  (implies (and ;(integerp x) ;(fep x p)
                (integerp y) ;(fep y p)
                (integerp z) ;(fep z p)
                (posp p))
           (equal (equal (add y x p) (add z x p))
                  (equal (mod y p) (mod z p))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add sub))))

(defthm equal-of-add-and-add-cancel-2+-2+
  (implies (and (integerp x)
                (integerp y1)
                (integerp z1)
                (integerp y2)
                (integerp z2)
                (posp p))
           (equal (equal (add y1 (add x z1 p) p) (add y2 (add x z2 p) p))
                  (equal (add y1 z1 p) (add y2 z2 p))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (enable add sub))))

(defthm equal-of-add-and-add-cancel-3+-1+
  (implies (and (integerp x)
                (integerp y1)
                (integerp z1)
                (integerp w1)
                (integerp y2)
                (posp p))
           (equal (equal (add y1 (add w1 (add x z1 p) p) p)
                         (add x y2 p))
                  (equal (add y1 (add w1 z1 p) p)
                         (mod y2 p))))
  :hints (("Goal" :use (:instance equal-of-add-and-add-cancel-1-gen
                                  (x (neg x p))
                                  (y (add y1 (add w1 (add x z1 p) p) p))
                                  (z (add x y2 p)))
           :in-theory (disable equal-of-add-and-add-cancel-1-gen
                               equal-of-add-cancel-1))))
