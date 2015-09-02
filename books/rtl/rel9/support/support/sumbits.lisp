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

(in-package "ACL2")

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
