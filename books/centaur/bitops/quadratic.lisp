; Copyright (C) 2024 Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "BITOPS")
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/misc/multiply-out" :dir :system))

(defmacro quad (x a b c)
  `(let ((x ,x))
     (+ ,c (* ,b x) (* ,a x x))))


(defthmd quad-increasing-past-midpoint
  (implies (and (rationalp x)
                (rationalp a)
                (rationalp b)
                (rationalp c)
                (< 0 a)
                (<= (/ (- b) (* 2 a)) x)
                (rationalp y)
                (< x y))
           (< (quad x a b c)
              (quad y a b c)))
  :hints ((and stable-under-simplificationp
               '(:nonlinearp t))))

(defthmd quad-decreasing-before-midpoint
  (implies (and (rationalp x)
                (rationalp a)
                (rationalp b)
                (rationalp c)
                (< 0 a)
                (<= x (/ (- b) (* 2 a)))
                (rationalp y)
                (< y x))
           (< (quad x a b c)
              (quad y a b c)))
  :hints ((and stable-under-simplificationp
               '(:nonlinearp t))))

(defthmd quad-decreasing-past-midpoint
  (implies (and (rationalp x)
                (rationalp a)
                (rationalp b)
                (rationalp c)
                (< a 0)
                (<= (/ (- b) (* 2 a)) x)
                (rationalp y)
                (< x y))
           (< (quad y a b c)
              (quad x a b c)))
  :hints ((and stable-under-simplificationp
               '(:nonlinearp t))))

(defthmd quad-increasing-before-midpoint
  (implies (and (rationalp x)
                (rationalp a)
                (rationalp b)
                (rationalp c)
                (< a 0)
                (<= x (/ (- b) (* 2 a)))
                (rationalp y)
                (< y x))
           (< (quad y a b c)
              (quad x a b c)))
  :hints ((and stable-under-simplificationp
               '(:nonlinearp t))))

(local (Defthm a/a*x
         (implies (and (acl2-numberp a)
                       (not (equal a 0)))
                  (equal (* a (/ a) x) (fix x)))
         :hints ((and stable-under-simplificationp
                      '(:nonlinearp t)))))

(defthmd quad-always-positive
  (implies (and (rationalp x)
                (rationalp a)
                (rationalp b)
                (rationalp c)
                (< 0 a)
                (< 0 (quad (/ (- b) (* 2 a)) a b c)))
           (< 0 (quad x a b c)))
  :hints (("goal" :use ((:instance quad-increasing-past-midpoint
                         (y x) (x (/ (- b) (* 2 a))))
                        (:instance quad-decreasing-before-midpoint
                         (y x) (x (/ (- b) (* 2 a)))))
           :in-theory (disable acl2::multiply-out-<
                               acl2::multiply-out-equal))))

(defthmd quad-always-negative
  (implies (and (rationalp x)
                (rationalp a)
                (rationalp b)
                (rationalp c)
                (< a 0)
                (< (quad (/ (- b) (* 2 a)) a b c) 0))
           (< (quad x a b c) 0))
  :hints (("goal" :use ((:instance quad-decreasing-past-midpoint
                         (y x) (x (/ (- b) (* 2 a))))
                        (:instance quad-increasing-before-midpoint
                         (y x) (x (/ (- b) (* 2 a)))))
           :in-theory (disable acl2::multiply-out-<
                               acl2::multiply-out-equal))))


;; roots:
;; x <> (-b +- sqrt(b^2 - 4ac) / 2 a)
;; 2ax + b <> +- sqrt(b^2 - 4ac)

(defthmd quad-zero
    (implies (and (rationalp x)
                  (rationalp a)
                  (rationalp b)
                  (rationalp c)
                  (not (equal a 0))
                  ;; Note: this means x is one of the roots of the quadratic
                  (equal (* (+ (* 2 a x) b) (+ (* 2 a x) b))
                         (- (* b b) (* 4 a c))))
             (equal (quad x a b c) 0))
    :hints (("goal" :in-theory (enable acl2::divide-out-common-factors-equal))
            (and stable-under-simplificationp
                 '(:nonlinearp t))))

(defthmd quad-positive-outside
    (implies (and (rationalp x)
                  (rationalp a)
                  (rationalp b)
                  (rationalp c)
                  (< 0 a)
                  ;; we don't need to assume that the zeros are real for this theorem

                  ;; x is outside the roots of the quadratic
                  (> (* (+ (* 2 a x) b) (+ (* 2 a x) b))
                     (- (* b b) (* 4 a c))))
             (< 0 (quad x a b c)))
    :hints ((and stable-under-simplificationp
                 '(:nonlinearp t))))

(defthmd quad-negative-inside
    (implies (and (rationalp x)
                  (rationalp a)
                  (rationalp b)
                  (rationalp c)
                  (< 0 a)
                  (< (quad (/ (- b) (* 2 a)) a b c) 0)
                  ;; x is between the roots of the quadratic
                  (< (* (+ (* 2 a x) b) (+ (* 2 a x) b))
                     (- (* b b) (* 4 a c))))
             (< (quad x a b c) 0))
    :hints ((and stable-under-simplificationp
                 '(:nonlinearp t))))




(defthmd quad-negative-outside
    (implies (and (rationalp x)
                  (rationalp a)
                  (rationalp b)
                  (rationalp c)
                  (< a 0)
                  ;; we don't need to assume that the zeros are real for this theorem
                  
                  ;;  x is outside the roots of the quadratic
                  (> (* (+ (* 2 a x) b) (+ (* 2 a x) b))
                     (- (* b b) (* 4 a c))))
             (< (quad x a b c) 0))
    :hints ((and stable-under-simplificationp
                 '(:nonlinearp t))))

(defthmd quad-positive-inside
    (implies (and (rationalp x)
                  (rationalp a)
                  (rationalp b)
                  (rationalp c)
                  (< a 0)
                  (< 0 (quad (/ (- b) (* 2 a)) a b c))
                  ;; x is between the roots of the quadratic
                  (< (* (+ (* 2 a x) b) (+ (* 2 a x) b))
                     (- (* b b) (* 4 a c))))
             (< 0 (quad x a b c)))
    :hints ((and stable-under-simplificationp
                 '(:nonlinearp t))))

