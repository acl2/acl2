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

(include-book "bitn")
(include-book "bits")

(defun sumbits (x n)
  (if (zp n)
      0
    (+ (* (expt 2 (1- n)) (bitn x (1- n)))
       (sumbits x (1- n)))))

(defthmd sumbits-bits
  (implies (and (natp x)
                (natp n)
                (> n 0))
           (equal (sumbits x n)
                  (bits x (1- n) 0)))
  :hints (("Goal" :in-theory (enable bits-n-n-rewrite) ;yuck?
           :induct (sumbits x n))
          ("Subgoal *1/2" :use ((:instance bitn-plus-bits (n (1- n)) (m 0))))))

(defthmd sumbits-thm
     (implies (and (bvecp x n)
                   (natp n)
                   (> n 0))
              (equal (sumbits x n)
                     x))
   :hints (("Goal" :in-theory (enable sumbits-bits bvecp))))

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
