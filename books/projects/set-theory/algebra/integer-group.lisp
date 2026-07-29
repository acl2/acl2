; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book verifies an example of an Abelian group, the integers with the
; usual operations.

(in-package "ZF")

(include-book "groups")

(zsub integers ()
      x
      (v-omega)
      (integerp x)
      )

(defthmz integers$comprehension-better
  (implies (force (integers$prop))
           (equal (in x (integers))
                  (integerp x)))
  :props (zfc v$prop integers$prop prod2$prop domain$prop inverse$prop))

(in-theory (disable integers$comprehension))

(defun add2 (x)
  (+ (car x) (cdr x)))

(zify z+ add2 :dom (prod2 (integers) (integers)) :ran (integers)
      :props (v$prop integers$prop))

(zify z- unary-- :dom (integers) :ran (integers)
      :props (v$prop integers$prop))

(defthmz abelian-group-p-integers
  (abelian-group-p (integers) (z+) 0 (z-))
  :hints (("Goal" :in-theory (e/d (subset in-image-rewrite) (equal-apply))))
  :props (zfc v$prop integers$prop prod2$prop domain$prop inverse$prop
              z-$prop z+$prop))
