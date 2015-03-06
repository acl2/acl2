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

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))
(local (in-theory (enable bvecp)))

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defun check-array (name a dim1 dim2)
  (if (zp dim1)
      t
    (and (bvecp (aref1 name a (1- dim1)) dim2)
	 (check-array name a (1- dim1) dim2))))

(defthm check-array-lemma-1
    (implies (and (not (zp dim1))
		  (check-array name a dim1 dim2)
		  (natp i)
		  (< i dim1))
	     (bvecp (aref1 name a i) dim2))
  :rule-classes ())

(defthm check-array-lemma
    (implies (and (bvecp i n)
		  (not (zp (expt 2 n)))
		  (check-array name a (expt 2 n) dim2))		  
	     (bvecp (aref1 name a i) dim2))
  :rule-classes ()
  :hints (("Goal" :use ((:instance check-array-lemma-1 (dim1 (expt 2 n)))))))


