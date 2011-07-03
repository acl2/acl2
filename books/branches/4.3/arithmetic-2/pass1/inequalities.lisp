; Arithmetic-2 Library
; Copyright (C) 1999 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;
;; inequalities.lisp
;;

(in-package "ACL2")

(local (include-book "basic-arithmetic"))

; ??? I'm not convinced we should be apply FC to REAL/RATIONALP hypotheses,
; but for now I'll go ahead and do so at times.

(defmacro fc (x)
  x)

;; I need iff-equal for the next batch of theorems up till
;; <-*-right-cancel (which is in fact proved in
;; inequalities-helper.lisp).

(local
 (defthm iff-equal
   (equal (equal (< w x) (< y z))
	  (iff (< w x) (< y z)))))

(defthm /-preserves-positive
  (implies (real/rationalp x)
	   (equal (< 0 (/ x))
		  (< 0 x))))

(defthm /-preserves-negative
  (implies (real/rationalp x)
	   (equal (< (/ x) 0)
		  (< x 0))))

(defthm <-0-minus
  (equal (< 0 (- x))
         (< x 0)))

(defthm <-minus-zero
  (equal (< (- x) 0)
         (< 0 x)))

(defthm <-minus-minus
  (equal (< (- x) (- y))
	 (< y x)))

(defthm <-0-+-negative-1
  (equal (< 0 (+ (- y) x))
         (< y x)))

(defthm <-0-+-negative-2
  (equal (< 0 (+ x (- y)))
         (< y x)))

(defthm <-+-negative-0-1
  (equal (< (+ (- y) x) 0)
         (< x y)))

(defthm <-+-negative-0-2
  (equal (< (+ x (- y)) 0)
         (< x y)))

(defthm <-*-0
  (implies (and (real/rationalp x)
                (real/rationalp y))
           (equal (< (* x y) 0)
                (and (not (equal x 0))
                     (not (equal y 0))
                     (iff (< x 0)
                          (< 0 y))))))

(defthm 0-<-*
  (implies (and (real/rationalp x)
                (real/rationalp y))
           (equal (< 0 (* x y))
                (and (not (equal x 0))
                     (not (equal y 0))
                     (iff (< 0 x)
                          (< 0 y))))))

; The following two lemmas could be extended by adding two more such
; lemmas, i.e. for (< (* x z) (* z y)) and (< (* z x) (* y z)), but
; rather than incur that overhead here and in any other such cases
; (and besides, how about for example (< (* x z a) (* z a y))?), I'll
; wait for metalemmas to handle such things.

(defthm <-*-right-cancel
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y))
                (fc (real/rationalp z)))
           (equal (< (* x z) (* y z))
		  (cond ((< 0 z) (< x y))
			((< z 0) (< y x))
			((equal z 0) nil)
			(t nil))))
  :hints (("Goal" :use ((:instance 
                         (:theorem
                          (implies (and (real/rationalp a)
                                        (< 0 a)
                                        (real/rationalp b)
                                        (< 0 b))
                                   (< 0 (* a b))))
                         (a (abs (- y x)))
                         (b (abs z))))
                  :in-theory (disable |0-<-*|))))

(defthm <-*-left-cancel
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y))
                (fc (real/rationalp z)))
           (equal (< (* z x) (* z y))
		  (cond ((< 0 z) (< x y))
			((< z 0) (< y x))
			((equal z 0) nil)
			(t nil)))))

(defthm <-*-x-y-y
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (equal (< (* x y) y)
		  (cond
                   ((< 0 y) (< x 1))
                   ((< y 0) (< 1 x))
                   ((equal y 0) nil)
		   (t nil))))
  :hints (("Goal" :use ((:instance <-*-right-cancel
                                   (x x)
                                   (y 1)
                                   (z y))))))

(defthm <-*-y-x-y
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (equal (< (* y x) y)
		  (cond
                   ((< 0 y) (< x 1))
                   ((< y 0) (< 1 x))
                   ((equal y 0) nil)
                   (t nil)))))

(defthm <-y-*-x-y
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (equal (< y (* x y))
		  (cond
                   ((< 0 y) (< 1 x))
                   ((< y 0) (< x 1))
                   ((equal y 0) nil)
                   (t nil))))
  :hints (("Goal" :use ((:instance <-*-right-cancel
                                   (x 1)
                                   (y x)
                                   (z y))))))

(defthm <-y-*-y-x
  (implies (and (fc (real/rationalp x))
		(fc (real/rationalp y)))
	   (equal (< y (* y x))
		  (cond
                   ((< 0 y) (< 1 x))
                   ((< y 0) (< x 1))
                   ((equal y 0) nil)
                   (t nil)))))
