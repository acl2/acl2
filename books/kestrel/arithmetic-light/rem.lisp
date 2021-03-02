; A lightweight book about the built-in function rem
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/arithmetic-light/truncate" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divides" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(defthm rem-of-0
  (equal (rem x 0)
         (fix x))
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
