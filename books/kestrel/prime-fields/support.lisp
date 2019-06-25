; Prime fields library: supporting material.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../../projects/quadratic-reciprocity/euclid") ;brings in rtl::primep
(local (include-book "../arithmetic-light/times"))

(encapsulate ()
  (local (include-book "../../arithmetic-3/top"))
  ;;gen?
  (defthm not-divides-when-<
    (implies (and (< a b)
                  (posp a)
                  (posp b))
             (not (rtl::divides b a)))
    :hints (("Goal"
             :cases ((equal 0 a))
             :in-theory (enable rtl::divides)))))

;why needed?
(defthm distributivity-alt
  (equal (* (+ y z) x)
         (+ (* y x) (* z x))))
