; A lightweight book about the built-in function ceiling.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable ceiling))

(local (include-book "../../arithmetic-3/top")) ;todo: reduce
(local (include-book "integerp"))
;(local (include-book "nonnegative-integer-quotient"))
;(local (include-book "numerator"))
;(local (in-theory (disable floor)))

(defthmd ceiling-of-0
  (equal (ceiling 0 j)
         0)
  :hints (("Goal" :in-theory (enable ceiling floor))))

(defthmd ceiling-in-terms-of-floor
  (equal (ceiling i j)
         (- (floor (- i) j)))
  :hints (("Goal" :in-theory (enable ceiling floor))))

(defthm ceiling-when-<=
  (implies (and (<= i j)
                (natp i)
                (posp j))
           (equal (ceiling i j)
                  (if (equal 0 i)
                      0
                    1)))
  :hints (("Goal"
           :cases ((equal i 0)
                   (equal i j))
           :use (:instance integerp-squeeze (x (/ i j)))
           :in-theory (enable ceiling-in-terms-of-floor))))

;;gen - replace the with below
(defthm ceiling-of-+-of-minus-8
 (implies (rationalp x)
          (equal (ceiling (+ -8 x) 8)
                 (+ -1 (ceiling x 8))))
 :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor))))

;todo: put back
;; (include-book "../bv/floor")
;; (defthm ceiling-of-+-of-when-multiple-arg1
;;   (implies (and (integerp (/ i1 j))
;;                 (rationalp i2)
;;                 (rationalp j)
;;                 (not (equal 0 j)))
;;           (equal (ceiling (+ i1 i2) j)
;;                  (+ (/ i1 j) (ceiling i2 j))))
;;  :hints (("Goal" :in-theory (enable ceiling-in-terms-of-floor))))

(defthmd ceiling-in-terms-of-floor-cases
  (implies (and (rationalp i)
                (rationalp j))
           (equal (ceiling i j)
                  (if (integerp (/ i j))
                      (/ i j)
                    (+ 1 (floor i j)))))
  :hints (("Goal" :in-theory (enable ceiling floor))))

;; (thm
;;  (implies (and (rationalp x)
;;                (posp n) ;gen?
;;                )
;;           (equal (CEILING (+ (- N) x) N)
;;                  (+ -1 (CEILING x N))))
;;  :hints (("Goal" :in-theory (enable ceiling))))
