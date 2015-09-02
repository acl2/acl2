; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

; This file introduces definable Skolem functions that can be used in order to
; reduce theorems about all elements of a list to theorems about an arbitrary
; elements of a list.  Matt Kaufmann first learned of this trick from Ken
; Kunen.

(in-package "ACL2")

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
