; A lightweight book +, *, and / together
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "plus"))
(local (include-book "times"))
(local (include-book "divide"))

(defthm <-*-/-left-with-addend
  (implies (and (< 0 y)
                (real/rationalp x)
                (rationalp k)
                (real/rationalp y)
                (real/rationalp a))
           (equal (< (+ k (* x (/ y))) a)
                  (< (+ (* k y) x) (* a y))))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel
                                  (y y)
                                  (x1 (+ k (* x (/ y))))
                                  (x2 a))
           :in-theory (disable <-of-*-and-*-cancel))))

(defthm <-*-/-left-with-addend-alt
  (implies (and (< 0 y)
                (real/rationalp x)
                (rationalp k)
                (real/rationalp y)
                (real/rationalp a))
           (equal (< a (+ k (* x (/ y))))
                  (< (* a y) (+ (* k y) x))))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel
                                  (y y)
                                  (x1 a)
                                  (x2 (+ k (* x (/ y)))))
           :in-theory (disable <-of-*-and-*-cancel))))
