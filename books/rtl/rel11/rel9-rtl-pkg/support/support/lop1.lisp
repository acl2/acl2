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

(local (include-book "lop1-proofs"))
(include-book "merge") ;BOZO drop

(defund lop (a b d k)
  (let ((c (- (bitn a (1- k)) (bitn b (1- k)))))
    (if (and (integerp k) (>= k 0))
	(if (= k 0)
	    0
	  (if (= d 0)
	      (lop a b c (1- k))
	    (if (= d (- c))
		(lop a b (- c) (1- k))
	      k)))
      0)))

(defthm LOP-MOD
  (implies (and (integerp a)
                (>= a 0)
                (integerp b)
                (>= b 0)
                (integerp d)
                (integerp j)
                (>= j 0)
                (integerp k)
                (>= k j))
           (= (lop a b d j)
              (lop (mod a (expt 2 k)) (mod b (expt 2 k)) d j)))
  :rule-classes ())

(defthm LOP-BNDS
  (implies (and (integerp a)
                (integerp b)
                (integerp n)
                (>= a 0)
                (>= b 0)
                (>= n 0)
                (not (= a b))
                (< a (expt 2 n))
                (< b (expt 2 n)))
           (or (= (lop a b 0 n) (expo (- a b)))
               (= (lop a b 0 n) (1+ (expo (- a b))))))
  :rule-classes ())

