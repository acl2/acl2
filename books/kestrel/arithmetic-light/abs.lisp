; A lightweight book about the built-in function abs
;
; Copyright (C) 2016-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable abs))

(defthm abs-when-non-neg
  (implies (<= 0 x)
           (equal (abs x)
                  x))
  :hints (("Goal" :in-theory (enable abs))))

(defthm natp-of-abs
  (equal (natp (abs x))
         (integerp x))
  :hints (("Goal" :in-theory (enable abs)
           :cases ((integerp x)))))

(defthm integerp-of-abs
  (equal (integerp (abs x))
         (integerp x))
  :hints (("Goal" :in-theory (enable abs)
           :cases ((integerp x)))))

;; Since abs returns non-numbers unchanged
(defthm rationalp-of-abs
  (equal (rationalp (abs x))
         (rationalp x))
  :hints (("Goal" :in-theory (enable abs)
           :cases ((rationalp x)))))

;; Since abs returns non-numbers unchanged
(defthm acl2-numberp-of-abs
  (equal (acl2-numberp (abs x))
         (acl2-numberp x))
  :hints (("Goal" :in-theory (enable abs)
           :cases ((acl2-numberp x)))))

(defthm equal-of-0-and-abs
  (implies (acl2-numberp x) ; for example, (abs t) = t
           (equal (equal 0 (abs x))
                  (equal 0 x)))
  :hints (("Goal" :in-theory (enable abs))))
