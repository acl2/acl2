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

;Necessary definitions:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(local (include-book "fl")) ; yuck?

(defun or-dist-induct (y n)
  (if (and (integerp n) (>= n 0))
      (if (= n 0)
	  y
	(or-dist-induct (fl (/ y 2)) (1- n)))
    ()))

(defun log-induct (i j)
  (if (and (integerp i) (>= i 0)
	   (integerp j) (>= j 0))
      (if (or (= i 0) (= j 0))
	  ()
	(log-induct (fl (/ i 2)) (fl (/ j 2))))
    ()))

(DEFUN logand-three-args-induct (I J K)
  (declare (xargs :measure (ACL2-COUNT (abs i))
                  :hints (("Goal" :in-theory (enable abs)))))
  (IF (AND (INTEGERP I)
           (INTEGERP J)
           (INTEGERP K)
           )
      (IF (OR (= I 0) (= J 0) (= K 0)
              (= I -1) (= J -1) (= K -1))
          NIL
          (logand-three-args-induct
           (FL (/ I 2))
           (FL (/ J 2))
           (FL (/ K 2))))
      NIL))


(DEFUN LOG-INDUCT-allows-negatives (i j)
  (IF (AND (INTEGERP i)
           (INTEGERP j)
           )
      (IF (OR (= i 0) (= j 0) (= i -1) (= j -1))
          NIL
          (LOG-INDUCT-allows-negatives (FL (/ i 2)) (FL (/ j 2))))
      NIL))

(defun op-dist-induct (i j n)
  (if (and (integerp n) (>= n 0))
      (if  (= n 0)
	  (list i j)
	(op-dist-induct (fl (/ i 2)) (fl (/ j 2)) (1- n)))
    ()))

#|
(defun op-dist-induct-negative (i j n)
  (if (and (integerp n) (<= n 0))
      (if (= n 0)
	  (list i j)
	(op-dist-induct-negative (fl (/ i 2)) (fl (/ j 2)) (1+ n)))
    ()))
|#


;move?
(defun natp-induct (k)
  (if (zp k)
      t
    (natp-induct (1- k))))
