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

(include-book "log")
(include-book "logn")

(local (include-book "../support/top/top"))

(set-inhibit-warnings "theory")
(local (in-theory nil))

(defthm land-logand
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (land x y n)
                  (logand x y))))

(defthm lior-logior
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (lior x y n)
                  (logior x y))))

(defthm lxor-logxor
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (equal (lxor x y n)
                  (logxor x y))))

(defthm logior-bvecp
  (implies (and (bvecp x n) (bvecp y n))
           (bvecp (logior x y) n)))
           
(defthm logand-bvecp
  (implies (and (natp n) (bvecp x n) (integerp y))
           (bvecp (logand x y) n)))

(defthm logxor-bvecp
  (implies (and (bvecp x n)
                (bvecp y n)
                (natp n))
           (bvecp (logxor x y) n)))

(defthm lnot-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (lnot x n) k)))

;; (defthm lnot-lognot
;;   (implies (and (integerp x)
;;                 (natp n))
;;            (equal (lnot x n)
;;                   (bits (lognot x) (1- n) 0)))
;;   :hints (("Goal" :use (lnot-lognot-1))))
