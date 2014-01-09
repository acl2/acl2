; Arithmetic-3 Extensions
; Copyright (C) 2006 Alex Spiridonov
;
; This program is free software; you can redistribute it and/ormodify it under
; the terms of the GNU General Public Licenseas published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version. This program is distributed in the hope that it will be useful, but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.You should have received a copy of the GNU General Public License along
; with this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA."

; ext-compat.lisp
;
; The events in this file were originally part of arithmetic-3/extra/ext.lisp,
; contributed by Alex Spiridonov, with helpful consulting from Robert Krug.
;
; In 2014, Jared Davis moved these events out of ext.lisp into this new file,
; because ext.lisp also includes other events that do not work in ACL2(r), and
; this caused compatibility issues for the build system.
;
; In other words, this "-compat" book is the portion of ext.lisp that is
; compatible across both ACL2 and ACL2(r).  The top-level "ext" book now simply
; includes this book, and then adds the events that don't work with ACL2(r).

(in-package "ACL2")

; Theorems from arithmetic/top-with-meta
(encapsulate
  ()

  (local (include-book "arithmetic/top-with-meta" :dir :system))

  ; Theorems about inequalities
  (defthm /-inverts-order-1
    (implies (and (< 0 x)
                  (< x y)
                  (real/rationalp x)
                  (real/rationalp y))
             (< (/ y) (/ x))))

  (defthm /-inverts-order-2
    (implies (and (< y 0)
                  (< x y)
                  (real/rationalp x)
                  (real/rationalp y))
             (< (/ y) (/ x))))

  (defthm /-inverts-weak-order
    (implies (and (< 0 x)
                  (<= x y)
                  (real/rationalp x)
                  (real/rationalp y))
             (not (< (/ x) (/ y)))))

  ; Theorems about equalities
  (defthm equal-*-x-y-x
    (equal (equal (* x y) x)
           (or (equal x 0)
               (and (equal y 1)
                    (acl2-numberp x)))))

  (defthm equal-*-x-y-y
    (equal (equal (* x y) y)
           (or (equal y 0)
               (and (equal x 1)
                    (acl2-numberp y)))))

  (defthm equal-/
   (implies (and (acl2-numberp x)
                 (not (equal 0 x)))
            (equal (equal (/ x) y)
                   (equal 1 (* x y)))))

; From rtl/rel5/arithmetic
; Originally written as (mod (binary-* k x) (binary-* y k)), but we write is
; this way because arithmetic-3 will rewrite (binary-* y k) to (binary-* k y).
  (defthm mod-cancel-special-1-ext
    (implies (if (acl2-numberp x)
                 (if (rationalp k)
                     (if (acl2-numberp y)
                         (if (not (equal y '0))
                             (not (equal k '0))
                             'nil)
                         'nil)
                     'nil)
                 'nil)
             (equal (mod (binary-* k x) (binary-* k y))
                    (binary-* k (mod x y)))))

)

; Theorems from ihs
(encapsulate
  ()

  (local (include-book "ihs/ihs-definitions" :dir :system))
  (local (include-book "ihs/ihs-lemmas" :dir :system))
  (local (minimal-ihs-theory))

  (defthm integerp-i/j-integerp-forward
    (implies
     (and (integerp (/ i j))
	  (real/rationalp i)
	  (integerp j)
	  (not (zerop j)))
     (integerp i))
    :rule-classes
    ((:forward-chaining
      :corollary
      (implies
       (and (integerp (/ i j))
	    (force (real/rationalp i))
	    (integerp j)
	    (force (not (equal 0 j))))
       (integerp i)))
     (:forward-chaining
      :corollary
      (implies
       (and (integerp (* (/ j) i))
	    (force (real/rationalp i))
	    (integerp j)
	    (force (not (equal 0 j))))
       (integerp i)))))

  (defthm justify-floor-recursion-ext
    (implies
     (and (force (real/rationalp x))
          (force (real/rationalp y))
          (force (not (equal 0 y))))
     (and
      (implies
       (and (< 0 x)
            (< 1 y))
       (< (floor x y) x))
      (implies
       (and (< x -1)
            (<= 2 y))
       (< x (floor x y))))))

; From arithmetic-2
; Alternative: mod-x-y-=-x+y from IHS
  (defthm mod-x-y-=-x-+-y-ext
    (implies (and (rationalp x)
                  (rationalp y)
                (not (equal y 0))
		(if (< 0 y)
		    (and (< x 0)
			 (<= (- x) y))
		  (and (< 0 x)
		       (<= y (- x)))))
             (equal (mod x y) (+ x y)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)
                   (:rewrite
                    :corollary
                    (implies (and (rationalp x)
                                  (rationalp y)
                                  (not (equal y 0)))
                             (equal (equal (mod x y) (+ x y))
                                    (if (< 0 y)
                                        (and (< x 0)
                                             (<= (- x) y))
                                      (and (< 0 x)
                                           (<= y (- x)))))))))

  (defthm mod-x-i*j
    (implies
     (and (> i 0)
	  (> j 0)
	  (force (integerp i))
	  (force (integerp j))
	  (force (real/rationalp x)))
     (equal (mod x (* i j))
	    (+ (mod x i) (* i (mod (floor x i) j))))))

  (defthm floor-x+i*k-i*j
    (implies
     (and (force (real/rationalp x))
          (force (integerp i))
          (force (integerp j))
          (force (integerp k))
          (< 0 i)
          (< 0 j)
          (<= 0 x)
          (< x i))
     (equal (floor (+ x (* i k)) (* i j))
            (floor k j))))

  (defthm mod-x+i*k-i*j
    (implies
     (and (force (real/rationalp x))
          (force (integerp i))
          (force (integerp j))
          (force (integerp k))
          (< 0 i)
          (< 0 j)
          (<= 0 x)
          (< x i))
     (equal (mod (+ x (* i k)) (* i j))
            (+ x (* i (mod k j))))))

)

(encapsulate
  ()

  (local (include-book "arithmetic-2/meta/expt" :dir :system))
  (local (include-book "arithmetic-2/meta/integerp" :dir :system))

  (defthm expt-1-linear-b
    (implies (and (<= 0 x)
                  (< x 1)
                  (< 0 i)
                  (real/rationalp x)
                  (integerp i))
             (< (expt x i) 1))
    :rule-classes :linear)

  (defthm expt-1-linear-d
    (implies (and (<= 0 x)
                  (<= x 1)
                  (<= 0 i)
                  (real/rationalp x)
                  (integerp i))
             (<= (expt x i) 1))
    :rule-classes :linear)

  (defthm expt-1-linear-h
    (implies (and (< 0 x)
                  (<= x 1)
                  (< i 0)
                  (real/rationalp x)
                  (integerp i))
             (<= 1 (expt x i)))
    :rule-classes :linear)

  (defthm nintegerp-expt
    (implies (and (real/rationalp x)
                  (< 1 x)
                  (integerp n)
                  (< n 0))
             (not (integerp (expt x n))))
    :hints (("Goal" :use nintegerp-expt-helper))
    :rule-classes :type-prescription)

)


#|
(encapsulate
  ()

  ; Expensive: adds ~9 seconds to test suite. Gain: 1.
  (local (include-book "arithmetic-3/bind-free/top" :dir :system))
  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

  (defthm mod-x-y-=-x---y
    (implies (and (and (rationalp x)
                       (rationalp y)
                       (not (equal y 0)))
                  (if (< 0 y)
                      (and (<= y x)
                           (< x (* 2 y)))
                    (and (<= x y)
                         (< (* 2 y) x))))
             (equal (mod x y) (- x y)))
    :hints ((nonlinearp-default-hint stable-under-simplificationp hist pspv))
    :rule-classes ((:rewrite :backchain-limit-lst 0)
                   (:rewrite
                    :corollary
                    (implies (and (rationalp x)
                                  (rationalp y)
                                  (not (equal y 0)))
                             (equal (equal (mod x y) (- x y))
                                    (if (< 0 y)
                                        (and (<= y x)
                                             (< x (* 2 y)))
                                      (and (<= x y)
                                           (< (* 2 y) x))))))))
)
|#
