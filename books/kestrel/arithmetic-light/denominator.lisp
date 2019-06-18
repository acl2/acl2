; A lightweight book about the built-in function denominator.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm denominator-when-integerp
  (implies (integerp x)
           (equal (denominator x)
                  1))
  :hints (("Goal" :in-theory (enable numerator))))

(defthm equal-of-1-and-denominator
  (equal (equal 1 (denominator x))
         (integerp (rfix x))))
