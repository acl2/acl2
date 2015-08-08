;  Copyright (C) 2000 Panagiotis Manolios

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

(in-package "ACL2")

(defun b--and (p q) (if p (if q t nil) nil))
(defun b--or (p q) (if p t (if q t nil)))
(defun b--xor (p q) (if p (if q nil t) (if q t nil)))

(defun b--maj (p q c)
  (b--or (b--and p q)
	(b--or (b--and p c)
	      (b--and q c))))

(defun full-adder (p q c)
  (mv (b--xor p (b--xor q c))
      (b--maj p q c)))

(defun serial-adder (x y c)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (and (endp x) (endp y))
      (list c)
    (mv-let (sum cout)
	    (full-adder (car x) (car y) c)
	    (cons sum (serial-adder (cdr x) (cdr y) cout)))))

#|
     11  (3)
   1100 (12)
 +    1  (1)
 ------
  10000 (16)

(serial-adder '(t t nil) '(nil nil t t) t)
|#

(defun n (v)
  (cond ((endp v) 0)
        ((car v) (+ 1 (* 2 (n (cdr v)))))
        (t (* 2 (n (cdr v))))))

#|
(n (serial-adder '(t t nil) '(nil nil t t) t))

(+ (n '(t t nil)) (n '(nil nil t t)) 1)
|#

(local
 (progn
   (defthm serial-adder-correct-nil-nil
     (equal (n (serial-adder x nil nil))
	    (n x)))

   (defthm serial-adder-correct-nil-t
     (equal (n (serial-adder x nil t))
	    (+ 1 (n x))))
   ))

(defthm serial-adder-correct
  (equal (n (serial-adder x y c))
         (+ (n x) (n y) (if c 1 0))))

(defun multiplier (x y p)
  (if (endp x)
      p
    (multiplier (cdr x)
		(cons nil y)
		(if (car x)
		    (serial-adder y p nil)
		  p))))
#|
For example,

      1001      (9)
    x 1010   x (10)
    ------   ------
     10010     (90)
   1001000
 ---------
   1011010

(multiplier '(t nil nil t) '(nil t nil t) nil)
(n (multiplier '(t nil nil t) '(nil t nil t) nil))
|#

(local
 (defthm complete-*
   (equal (* y (* x z))
	  (* x (* y z)))
   :hints (("Goal"
	    :use ((:instance associativity-of-* (y x) (x y))
		  (:instance associativity-of-*))
	    :in-theory (disable associativity-of-*)))))

(defthm multiplier-correct
  (equal (n (multiplier x y p))
	 (+ (* (n x) (n y)) (n p))))

(defun mmod (n m)
  (cond ((zp n) 0)
	((zp m) 0)
	((< n m) n)
	(t (mmod (- n M) m))))

(defun add-fix (i l)
  (if (zp i)
      nil
    (cons (if (car l) t nil)
	  (add-fix (1- i) (cdr l)))))

(defun 128fix (l)
  (add-fix 128 l))

(defun serial-alu (op v1 v2)
  (cond ((equal op 0)
	 (128fix (serial-adder (128fix v1) (128fix v2) nil)))
	(t (128fix (multiplier v1 v2 nil)))))

(local
 (progn
   (include-book "../../../top/ihs")

   (defthm mod-mmod
     (implies (and (natp n) (posp m))
	      (equal (mod n m) (mmod n m))))

   (defun induct-for-thm (l b)
     (if (zp b)
	 (cons l b)
       (induct-for-thm (cdr l) (1- b))))

   (defthm mmod-1
     (equal (mmod n 1) 0))

   (defthm expt-<
     (implies (natp b)
	      (and (integerp (expt 2 b))
		   (< 0 (expt 2 b)))))

   (defthm mmod-*-2
     (implies (and (integerp b)
		   (integerp n)
		   (<= 0 b))
	      (equal (mmod (* 2 n) (* 2 b))
		     (* 2 (mmod n b)))))

   (defthm int-expt
     (implies (and (integerp b)
		   (< 0 b))
	      (integerp (* 1/2 (expt 2 b)))))

   (in-theory (disable EXPT))

   ;; Added in Version_2.6.
   (local (in-theory (enable exponents-add-unrestricted)))

   (defthm mmod-*-2-
     (implies (and (integerp b)
		   (integerp n)
		   (< 0 b))
	      (equal (mmod (* 2 n) (expt 2 b))
		     (* 2 (mmod n (expt 2 (1- b))))))
     :hints (("goal" :use (:instance mmod-*-2 (b (expt 2 (1- b)))))))

   (defthm mmod-a-b
     (implies (and (natp a)
		   (integerp b)
		   (< a b))
	      (equal (mmod a b) a)))

   (defthm mod-over-expt
     (implies (and (posp b)
		   (natp n))
	      (equal (mod (+ 1 (* 2 n)) (expt 2 b))
		     (+ 1 (* 2 (mod n (* 1/2 (expt 2 b)))))))
     :hints (("goal" :use (:instance mod-x+i*k-i*j (x 1) (I 2) (k n) (j (* 1/2 (expt 2 b)))))))

   (defthm mmod-over-expt
     (implies (and (posp b)
		   (natp n))
	      (equal (mmod (+ 1 (* 2 n)) (expt 2 b))
		     (+ 1 (* 2 (mmod n (* 1/2 (expt 2 b)))))))
     :hints (("goal" :use ((:instance mod-over-expt)
			   (:instance mod-mmod (n (+ 1 (* 2 n))) (m (expt 2 b)))
			   (:instance mod-mmod (m (* 1/2 (expt 2 b))))))))

   (defthm add-fix-mod
     (implies (and (integerp b)
		   (<= 0 b))
	      (equal (n (add-fix b l))
		     (mmod (n l) (expt 2 b))))
     :hints (("goal" :induct (induct-for-thm l b))
	     ("subgoal *1/2.4'"
	      :in-theory '(natp posp)
	      :use (:instance mmod-over-expt (n (n (cdr l)))))))

   (defthm full-car1
     (implies (and (car v))
	      (equal (full-adder (car v) x y)
		     (full-adder t x y))))

   (defthm full-car2
     (implies (and (car v))
	      (equal (full-adder x (car v) y)
		     (full-adder x t y))))

   (defthm add-fix-cons
     (implies (and (integerp n)
		   (<= 0 n))
	      (equal (add-fix n (cons nil (add-fix n nil)))
		     (add-fix n nil))))

   (defthm serial-add-add-fix
     (implies (and (integerp n) (<= 0 n))
	      (equal (serial-adder (add-fix n nil)
				   (add-fix n nil)
				   nil)
		     (add-fix (1+ n) nil))))

   ))

(defthm add-fix-add
  (implies (and (integerp n)
		(<= 0 n))
	   (equal (add-fix n (serial-adder (add-fix n v1) (add-fix n v2) c))
		  (add-fix n (serial-adder v1 v2 c)))))

(defthm add-serial
  (implies (and (integerp n)
		(<= 0 n))
	   (equal (n (add-fix n (serial-adder v1 v2 c)))
		  (mod (+ (n v1) (n v2) (if c 1 0)) (expt 2 n)))))

(defun serial-excp (op v1 v2)
  (cond ((equal op 0)
	 (not (equal (n (128fix (serial-adder (128fix v1) (128fix v2) nil)))
		     (n (serial-adder v1 v2 nil)))))
	(t (not (equal (n (128fix (multiplier v1 v2 nil)))
		       (n (multiplier v1 v2 nil)))))))

; from isa128.lisp
(defun ALU-output (op val1 val2)
  (cond ((equal op 0)
	 (mod (+ (nfix val1) (nfix val2)) (expt 2 128)))
	(t (mod (* (nfix val1) (nfix val2)) (expt 2 128)))))

; from isa128.lisp
(defun excp (op val1 val2)
  (cond ((equal op 0)
	 (not (equal (mod (+ (nfix val1) (nfix val2)) (expt 2 128))
		     (+ (nfix val1) (nfix val2)))))
	(t (not (equal (mod (* (nfix val1) (nfix val2)) (expt 2 128))
		       (* (nfix val1) (nfix val2)))))))

(defthm serial-ALU-ALU-output
  (equal (n (serial-ALU op v1 v2))
	 (ALU-output op (n v1) (n v2))))

(defthm serial-excp-excp
  (equal (serial-excp op v1 v2)
	 (excp op (n v1) (n v2))))
