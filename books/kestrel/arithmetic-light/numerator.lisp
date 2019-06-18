; A lightweight book about the built-in function numerator.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "denominator"))

(defthm numerator-when-integerp
  (implies (integerp x)
           (equal (numerator x)
                  x))
  :hints (("Goal" :use (:instance rational-implies2)
           :in-theory (disable rational-implies2))))

(defthm equal-of-numerator-same
  (equal (equal x (numerator x))
         (integerp x)))

(defthm <-of-numerator-and-0
  (implies (rationalp x)
           (equal (< (numerator x) 0)
                  (< x 0)))
  :hints (("Goal" :cases ((< x 0)))))
