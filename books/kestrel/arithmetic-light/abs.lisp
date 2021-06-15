; A lightweight book about the built-in function abs
;
; Copyright (C) 2016-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider disabling abs

(defthm abs-when-non-neg
  (implies (and (<= 0 x)
                (rationalp x))
           (equal (abs x)
                  x)))

(defthm natp-of-abs
  (equal (natp (abs x))
         (integerp x))
  :hints (("Goal" :cases ((integerp x)))))

(defthm integerp-of-abs
  (equal (integerp (abs x))
         (integerp x))
  :hints (("Goal" :cases ((integerp x)))))

;; Since abs returns non-numbers unchanged
(defthm rationalp-of-abs
  (equal (rationalp (abs x))
         (rationalp x))
  :hints (("Goal" :cases ((rationalp x)))))

;; Since abs returns non-numbers unchanged
(defthm acl2-numberp-of-abs
  (equal (acl2-numberp (abs x))
         (acl2-numberp x))
  :hints (("Goal" :cases ((acl2-numberp x)))))
