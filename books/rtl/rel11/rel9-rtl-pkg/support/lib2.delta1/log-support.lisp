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

(include-book "../lib2/top")

(local (include-book "log-support-proofs"))


(defthmd lnot-lognot
  (implies (and (natp n)
                (> n 0)
                (integerp x))
           (equal (lnot x n)
                  (bits (lognot x) (+ -1 n) 0))))



(defthmd land-logand
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (land x y n)
                  (bits (logand x y) (+ -1 n) 0))))

(defthmd lxor-logxor
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (lxor x y n)
                  (bits (logxor x y) (+ -1 n) 0))))


(defthmd lior-logior
  (implies (and (natp n)
                (> n 0)
                (integerp x)
                (integerp y))
           (equal (lior x y n)
                  (bits (logior x y) (+ -1 n) 0))))




(defthmd logand-bits-reduce
  (implies (and (syntaxp (or (and (consp y)
                                  (not (equal (car y) 'bits)))
                             (symbolp y)))
                (bvecp y (+ 1 n))
                (natp n)
                (integerp x))
           (equal (logand (bits x n 0)
                          y)
                  (logand x y))))


(defthmd logand-bitn-reduce
  (implies (and (syntaxp (or (and (consp y)
                                  (not (equal (car y) 'bitn)))
                             (symbolp y)))
                (bvecp y 1)
                (integerp x))
           (equal (logand (bitn x 0)
                          y)
                  (logand x y))))


;;;;
;;;;
