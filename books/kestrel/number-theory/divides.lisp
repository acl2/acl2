; Rules about the function DIVIDES
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "../../projects/numbers/euclid") ;brings in divides
(local (include-book "../arithmetic-light/times"))

;; when x > y, x usually doesn't divide y.
(defthm divides-when-<
  (implies (and (< y x) ; unusual
                (natp y)
                (natp x))
           (equal (divides x y)
                  (or (equal x 0)
                      (equal y 0))))
  :hints (("Goal"
           :cases ((equal 0 y)
                   (and (< 0 y) (equal 0 x)))
           :in-theory (enable divides))))
