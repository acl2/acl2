#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "LIST")

;theorems mixing repeat and memberp (and perhaps other list functions).

(include-book "repeat")
(include-book "memberp")

(defthm memberp-of-repeat-same
  (equal (memberp v (repeat n v))
         (not (zp n)))
  :hints (("Goal" :in-theory (enable repeat))))

(defthm memberp-of-repeat
  (equal (memberp x (repeat n v))
         (and (equal x v)
              (integerp n)
              (< 0 n)))
  :hints (("Goal" :in-theory (enable repeat))))
