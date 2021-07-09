; A lightweight book about the built-in function ifix
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "plus"))

;; (in-theory (disable ifix)) ; todo: consider this

(defthm ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x)
                  x))
  :hints (("Goal" :in-theory (enable ifix))))

(defthm ifix-when-not-integerp
  (implies (not (integerp x))
           (equal (ifix x)
                  0))
  :hints (("Goal" :in-theory (enable ifix))))

(defthm ifix-of--
  (equal (ifix (- x))
         (- (ifix x)))
  :hints (("Goal" :in-theory (enable ifix))))

(defthm ifix-of-ifix
  (equal (ifix (ifix x))
         (ifix x))
  :hints (("Goal" :in-theory (enable ifix))))

(defthm fix-of-+-when-integerp-arg1
  (implies (integerp x1)
           (equal (ifix (+ x1 x2))
                  (if (and (acl2-numberp x2)
                           (not (integerp x2)))
                      0 ; unusual case
                    (+ x1 (fix x2)))))
  :hints (("Goal" :in-theory (enable ifix))))
