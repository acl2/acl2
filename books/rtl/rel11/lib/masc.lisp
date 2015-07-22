; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/top"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))


;;;**********************************************************************
;;;                      Bit Manipulation
;;;**********************************************************************

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund chop (x k)
  (/ (fl (* (expt 2 k) x)) (expt 2 k)))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defund si (r n)
  (if (= (bitn r (1- n)) 1)
      (- r (expt 2 n))
    r))

(defund binary-cat (x m y n)
  (declare (xargs :guard (and (integerp x)
                              (integerp y)
                              (natp m)
                              (natp n))))
  (if (and (natp m) (natp n))
      (+ (* (expt 2 n) (bits x (1- m) 0))
         (bits y (1- n) 0))
    0))

(defun formal-+ (x y)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard t))
  (if (and (acl2-numberp x) (acl2-numberp y))
      (+ x y)
    (list '+ x y)))

;;X is a list of alternating data values and sizes.  CAT-SIZE returns the
;;formal sum of the sizes.  X must contain at least 1 data/size pair, but we do
;;not need to specify this in the guard, and leaving it out of that guard
;;simplifies the guard proof.

(defun cat-size (x)
  ;;an auxiliary function that does not appear in translate-rtl output.
  (declare (xargs :guard (and (true-listp x) (evenp (length x)))))
  (if (endp (cddr x))
      (cadr x)
    (formal-+ (cadr x)
	      (cat-size (cddr x)))))

(defmacro cat (&rest x)
  (declare (xargs :guard (and x (true-listp x) (evenp (length x)))))
  (cond ((endp (cddr x))
         `(bits ,(car x) ,(formal-+ -1 (cadr x)) 0))
        ((endp (cddddr x))
         `(binary-cat ,@x))
        (t
         `(binary-cat ,(car x) 
                      ,(cadr x) 
                      (cat ,@(cddr x)) 
                      ,(cat-size (cddr x))))))

;Allows things like (in-theory (disable cat)) to refer to binary-cat.
(add-macro-alias cat binary-cat)

(defsection-rtl |Language Overview| |MASC: The Formal Language|

(defun setbits (x w i j y)
  (declare (xargs :guard (and (natp x)
                              (integerp y)
                              (integerp i)
                              (integerp j)
                              (<= 0 j)
                              (<= j i)
                              (integerp w)
                              (< i w))))
  (mbe :logic (cat (bits x (1- w) (1+ i))
                   (+ -1 w (- i))
                   (cat (bits y (+ i (- j)) 0)
                        (+ 1 i (- j))
                        (bits x (1- j) 0)
                        j)
                   (1+ i))
       :exec  (cond ((int= j 0)
                     (cond ((int= (1+ i) w)
                            (bits y (+ i (- j)) 0))
                           (t
                            (cat (bits x (1- w) (1+ i))
                                 (+ -1 w (- i))
                                 (bits y (+ i (- j)) 0)
                                 (1+ i)))))
                    ((int= (1+ i) w)
                     (cat (bits y (+ i (- j)) 0)
                          (+ 1 i (- j))
                          (bits x (1- j) 0)
                          j))
                    (t
                     (cat (bits x (1- w) (1+ i))
                          (+ -1 w (- i))
                          (cat (bits y (+ i (- j)) 0)
                               (+ 1 i (- j))
                               (bits x (1- j) 0)
                               j)
                          (1+ i))))))

(defun setbitn (x w n y)
  (declare (xargs :guard (and (natp x)
                              (integerp y)
                              (integerp n)
                              (<= 0 n)
                              (integerp w)
                              (< n w))))
  (setbits x w n n y))


;;;**********************************************************************
;;;                      Boolean Functions
;;;**********************************************************************

(defun log= (x y)
  (declare (xargs :guard t))
  (if (equal x y) 1 0))

(defun log<> (x y)
  (declare (xargs :guard t))
  (if (equal x y) 0 1))

(defun log< (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (< x y) 1 0))

(defun log<= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (<= x y) 1 0))

(defun log> (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (> x y) 1 0))

(defun log>= (x y)
  (declare (xargs :guard (and (rationalp x) (rationalp y))))
  (if (>= x y) 1 0))

(defun logior1 (x y)
  (if (and (equal x 0) (equal y 0)) 0 1))

(defun logand1 (x y)
  (if (or (equal x 0) (equal y 0)) 0 1))

(defun lognot1 (x)
  (if (equal x 0) 1 0))

(defun true$ () 1)

(defun false$ () 0)

(defmacro if1 (x y z) `(if (eql ,x 0) ,z ,y))    

(defmacro in-function (fn term)
  `(if1 ,term () (er hard ',fn "Assertion ~x0 failed" ',term)))
)


;;;**********************************************************************
;;;                           Arrays
;;;**********************************************************************

(include-book "misc/records" :dir :system)


;;;**********************************************************************
;;;                      Fixed-Point Registers
;;;**********************************************************************

(defsection-rtl |Arithmetic| |MASC: The Formal Language|

(defund ui (r) r)

(defund si (r n)
  (if (= (bitn r (1- n)) 1)
      (- r (expt 2 n))
    r))

(defund uf (r n m)
  (* (expt 2 (- m n)) (ui r)))

(defund sf (r n m)
  (* (expt 2 (- m n)) (si r n)))

(defthmd bits-uf
  (let ((x (uf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp i)
                  (natp j)
                  (<= j i))
             (equal (bits r i j)
                    (* (expt 2 (- f j))
                       (- (chop x (- f j))
                          (chop x (- f (1+ i)))))))))

(defthmd bits-sf
  (let ((x (sf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp i)
                  (natp j)
                  (<= j i)
                  (< i n))
             (equal (bits r i j)
                    (* (expt 2 (- f j))
                       (- (chop x (- f j))
                          (chop x (- f (1+ i)))))))))

(defthm chop-uf
  (let ((x (uf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp k)
                  (<= (- f n) k)
                  (< k f))
             (iff (= (chop x k) x)
                  (= (bits r (1- (- f k)) 0) 0))))
  :rule-classes ())

(defthm chop-sf
  (let ((x (sf r n m))
        (f (- n m)))
    (implies (and (natp n)
                  (natp m)
                  (<= m n)
                  (bvecp r n)
                  (natp k)
                  (<= (- f n) k)
                  (< k f))
             (iff (= (chop x k) x)
                  (= (bits r (1- (- f k)) 0) 0))))
  :rule-classes ())

(defthmd sf-val
  (implies (and (natp n)
                (natp m)
                (<= m n)
                (bvecp r n)
                (integerp y)
                (= (mod y (expt 2 n)) r)
                (<= (- (expt 2 (1- n))) y)
                (< y (expt 2 (1- n))))
            (equal (sf r n m) 
                   (* (expt 2 (- m n)) y))))
)
