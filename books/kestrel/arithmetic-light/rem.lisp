; A lightweight book about the built-in function rem
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "truncate"))
(local (include-book "mod"))
(local (include-book "floor"))
(local (include-book "times"))
(local (include-book "times-and-divides"))
(local (include-book "plus-and-minus"))
(local (include-book "plus"))
(local (include-book "minus"))
(local (include-book "floor"))
(local (include-book "divides"))

(in-theory (disable rem))

(defthm rem-of-0-arg2
  (equal (rem x 0)
         (fix x))
  :hints (("Goal" :in-theory (enable rem))))

(defthm rem-of-0-arg1
  (equal (rem 0 y)
         0)
  :hints (("Goal" :in-theory (enable rem))))

(defthmd rem-becomes-mod
  (implies (and (rationalp x)
                (rationalp y))
           (equal (rem x y)
                  (if (or (and (<= 0 x) (<= 0 y))
                          (and (< x 0) (< y 0)))
                      (mod x y)
                    (if (equal 0 (mod x y))
                        0
                      (+ (- y) (mod x y))))))
  :hints (("Goal" :in-theory (e/d (rem mod truncate-becomes-floor-gen)
                                  ())
           :cases ((equal 0 y)))))

(defthm rem-x-y-=-x-better
  (implies (and (rationalp x)
                (rationalp y))
           (equal (equal (rem x y) x)
                  (if (equal 0 y)
                      (acl2-numberp x)
                    (< (abs x) (abs y)))))
  :hints (("Goal" :cases ((< 0 x))
           :in-theory (enable rem
                              truncate-becomes-floor-gen
                              equal-of-floor))))
