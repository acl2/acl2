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

(include-book "land0")
(include-book "lior0")
(include-book "lxor0")
(local (include-book "lextra-proofs"))

;theorems mixing two or more of the new logical operators.

;BOZO really the -1 and -2 names below should be switched?

(deflabel lextra0-start)

(defthm lior0-land0-1
  (equal (lior0 x (land0 y z n) n)
         (land0 (lior0 x y n) (lior0 x z n) n)))

(defthm lior0-land0-2
  (equal (lior0 (land0 y z n) x n)
         (land0 (lior0 x y n) (lior0 x z n) n)))

(defthm land0-lior0-1
  (equal (land0 x (lior0 y z n) n)
         (lior0 (land0 x y n) (land0 x z n) n)))

(defthm land0-lior0-2
  (equal (land0 (lior0 y z n) x n)
         (lior0 (land0 x y n) (land0 x z n) n)))

(defthm lior0-land0-lxor0
  (equal (lior0 (land0 x y n) (lior0 (land0 x z n) (land0 y z n) n) n)
         (lior0 (land0 x y n) (land0 (lxor0 x y n) z n) n)))

(defthm lxor0-rewrite
  (equal (lxor0 x y n)
         (lior0 (land0 x (lnot y n) n)
               (land0 y (lnot x n) n)
               n)))

(defthm lnot-lxor0
  (equal (lnot (lxor0 x y n) n)
         (lxor0 (lnot x n) y n)))

(defthm lnot-lior0
  (equal (lnot (lior0 x y n) n)
         (land0 (lnot x n) (lnot y n) n)))

(defthm lnot-land0
  (equal (lnot (land0 x y n) n)
         (lior0 (lnot x n) (lnot y n) n)))

(deflabel lextra0-end)

(in-theory (current-theory 'lextra0-start))
