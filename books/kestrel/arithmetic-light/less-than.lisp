; A lightweight book about the built-in function <.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthmd <-when-rationalp-and-complex-rationalp
  (implies (and (complex-rationalp y)
                (rationalp x))
           (equal (< x y)
                  (if (< x (realpart y))
                      t
                    (and (equal x (realpart y))
                         (< 0 (imagpart y))))))
  :hints (("Goal" :use (:instance completion-of-<) )))

(defthmd <-when-complex-rationalp-and-rationalp
  (implies (and (complex-rationalp x)
                (rationalp y))
           (equal (< x y)
                  (if (< (realpart x) y)
                      t
                    (and (equal y (realpart x))
                         (< (imagpart x) 0)))))
  :hints (("Goal" :use (:instance completion-of-<))))

(defthmd <-when-complex-rationalp-and-complex-rationalp
  (implies (and (complex-rationalp y)
                (complex-rationalp x))
           (equal (< x y)
                  (if (< (realpart x) (realpart y))
                      t
                    (and (equal (realpart x) (realpart y))
                         (< (imagpart x) (imagpart y))))))
  :hints (("Goal" :use (:instance completion-of-<) )))

(defthm not-<-same
  (not (< x x)))
