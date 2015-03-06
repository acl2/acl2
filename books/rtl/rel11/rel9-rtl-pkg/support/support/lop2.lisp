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

(include-book "lop1") ;BOZO
(include-book "lior0");BOZO
(local (include-book "lop2-proofs"))

(defthm lop-thm-1-original
  (implies (and (integerp a)
                (> a 0)
                (integerp b)
                (> b 0)
                (= e (expo a))
                (< (expo b) e)
                (= lambda
                   (lior0 (* 2 (mod a (expt 2 e)))
                         (lnot (* 2 b) (1+ e))
                         (1+ e))))
           (or (= (expo (- a b)) (expo lambda))
               (= (expo (- a b)) (1- (expo lambda)))))
  :rule-classes ())
