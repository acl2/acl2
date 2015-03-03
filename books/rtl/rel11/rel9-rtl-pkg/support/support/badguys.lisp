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

; This file introduces definable Skolem functions that can be used in order to
; reduce theorems about all elements of a list to theorems about an arbitrary
; elements of a list.  Matt Kaufmann first learned of this trick from Ken
; Kunen.

(in-package "RTL")

;;;**********************************************************************
;;;                       SUMBITS
;;;**********************************************************************

(include-book "merge") ; for badguy and lemmas about it

(defun sumbits-badguy (x y k)
  (if (zp k)
      0 ; arbitrary
    (if (not (equal (bitn x (1- k)) (bitn y (1- k))))
        (1- k)
      (sumbits-badguy x y (1- k)))))

(local
 (defthm sumbits-badguy-is-correct-lemma
   (implies (equal (bitn x (sumbits-badguy x y k))
                   (bitn y (sumbits-badguy x y k)))
            (equal (sumbits x k)
                   (sumbits y k)))
   :rule-classes nil))

(defthmd sumbits-badguy-is-correct
  (implies (and (bvecp x k)
                (bvecp y k)
                (equal (bitn x (sumbits-badguy x y k))
                       (bitn y (sumbits-badguy x y k)))
                (integerp k)
                (< 0 k))
           (equal (equal x y) t))
  :hints (("Goal"
           :use sumbits-badguy-is-correct-lemma
           :in-theory (enable sumbits-thm))))

(defthmd sumbits-badguy-bounds
  (implies (and (integerp k)
                (< 0 k))
           (let ((badguy (sumbits-badguy x y k)))
             (and (integerp badguy)
                  (<= 0 badguy)
                  (< badguy k)))))
