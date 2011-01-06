; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

(defund duplicity (a x)
  (declare (xargs :guard t))
  (cond ((atom x)
         0)
        ((equal (car x) a)
         (+ 1 (duplicity a (cdr x))))
        (t
         (duplicity a (cdr x)))))

(defthm duplicity-when-not-consp
  (implies (not (consp x))
           (equal (duplicity a x)
                  0))
  :hints(("Goal" :in-theory (enable duplicity))))

(defthm duplicity-of-cons
  (equal (duplicity a (cons b x))
         (if (equal a b)
             (+ 1 (duplicity a x))
           (duplicity a x)))
  :hints(("Goal" :in-theory (enable duplicity))))

(defthm duplicity-of-append
  (equal (duplicity a (append x y))
         (+ (duplicity a x)
            (duplicity a y)))
  :hints(("Goal" :induct (len x))))

(defthm duplicity-of-revappend
  (equal (duplicity a (revappend x y))
         (+ (duplicity a x)
            (duplicity a y)))
  :hints(("Goal" :induct (revappend x y))))

(defthm duplicity-of-reverse
  (equal (duplicity a (reverse x))
         (duplicity a x)))





(defthm duplicity-when-non-member-equal
  (implies (not (member-equal a x))
           (equal (duplicity a x)
                  0)))

(defthm no-duplicatesp-equal-when-high-duplicity
  (implies (> (duplicity a x) 1)
           (not (no-duplicatesp-equal x))))




(defund duplicity-badguy1 (dom x)
  (declare (xargs :guard t))
  (if (consp dom)
      (if (> (duplicity (car dom) x) 1)
          (list (car dom))
        (duplicity-badguy1 (cdr dom) x))
    nil))

(defthm duplicity-badguy1-exists-in-list
  (implies (duplicity-badguy1 dom x)
           (member-equal (car (duplicity-badguy1 dom x)) x))
  :hints(("Goal" :in-theory (enable duplicity-badguy1))))

(defthm duplicity-badguy1-exists-in-dom
  (implies (duplicity-badguy1 dom x)
           (member-equal (car (duplicity-badguy1 dom x)) dom))
  :hints(("Goal" :in-theory (enable duplicity-badguy1))))

(defthm duplicity-badguy1-has-high-duplicity
  (implies (duplicity-badguy1 dom x)
           (< 1 (duplicity (car (duplicity-badguy1 dom x)) x)))
  :hints(("Goal" :in-theory (enable duplicity-badguy1))))

(defthm duplicity-badguy1-is-complete-for-domain
  (implies (and (member-equal a dom)
                (< 1 (duplicity a x)))
           (duplicity-badguy1 dom x))
  :hints(("Goal" :in-theory (enable duplicity-badguy1))))

(defthm duplicity-badguy1-need-only-consider-the-list
  (implies (duplicity-badguy1 dom x)
           (duplicity-badguy1 x x))
  :hints(("Goal"
          :in-theory (disable duplicity-badguy1-exists-in-dom
                              duplicity-badguy1-exists-in-list)
          :use ((:instance duplicity-badguy1-exists-in-dom)
                (:instance duplicity-badguy1-exists-in-list)))))

(encapsulate
 ()
 (local (defthm lemma1
          (implies (duplicity-badguy1 dom x)
                   (duplicity-badguy1 dom (cons a x)))
          :hints(("Goal" :in-theory (enable duplicity-badguy1)))))

 (local (defthm lemma2
          (implies (and (member-equal a x)
                        (member-equal a dom))
                   (duplicity-badguy1 dom (cons a x)))
          :hints(("Goal" :in-theory (enable duplicity-badguy1)))))

 (defthm no-duplicatesp-equal-when-duplicity-badguy1
   (implies (and (not (duplicity-badguy1 dom x))
                 (subsetp-equal x dom))
            (no-duplicatesp-equal x))
   :hints(("Goal" :in-theory (enable duplicity-badguy1)))))




(defund duplicity-badguy (x)
  (declare (xargs :guard t))
  (duplicity-badguy1 x x))

(defthm duplicity-badguy-exists
  (implies (duplicity-badguy x)
           (member-equal (car (duplicity-badguy x)) x))
  :hints(("Goal" :in-theory (enable duplicity-badguy))))

(defthm duplicity-badguy-has-high-duplicity
  (implies (duplicity-badguy x)
           (< 1 (duplicity (car (duplicity-badguy x)) x)))
  :hints(("Goal" :in-theory (enable duplicity-badguy))))

(defthm duplicity-badguy-is-complete
  (implies (< 1 (duplicity a x))
           (duplicity-badguy x))
  :hints(("Goal"
          :in-theory (enable duplicity-badguy)
          :use ((:instance duplicity-badguy1-is-complete-for-domain
                           (dom x))))))




(encapsulate
 ()
 (local (defthm lemma
          (implies (subsetp-equal a (cdr x))
                   (subsetp-equal a x))))

 (local (defthm lemma2
          (subsetp-equal x x)
          :hints(("Goal" :induct (len x)))))

 (local (defthm lemma3
          (implies (not (duplicity-badguy x))
                   (no-duplicatesp-equal x))
          :hints(("Goal" :in-theory (enable duplicity-badguy)))))

 (local (defthm lemma5
          (implies (duplicity-badguy x)
                   (not (no-duplicatesp-equal x)))
          :hints(("Goal"
                  :in-theory (disable no-duplicatesp-equal)
                  :use ((:instance no-duplicatesp-equal-when-high-duplicity
                                   (a (car (duplicity-badguy x)))))))))

 (defthm duplicity-badguy-under-iff
   (iff (duplicity-badguy x)
        (not (no-duplicatesp-equal x)))))



(encapsulate
 (((duplicity-hyp) => *)
  ((duplicity-lhs) => *)
  ((duplicity-rhs) => *))

 (local (defun duplicity-hyp () nil))
 (local (defun duplicity-lhs () nil))
 (local (defun duplicity-rhs () nil))

 (defthm duplicity-constraint
   (implies (duplicity-hyp)
            (equal (duplicity a (duplicity-lhs))
                   (duplicity a (duplicity-rhs))))))

(encapsulate
 ()
 (local (defthm lemma1
          (implies (and (duplicity-hyp)
                        (no-duplicatesp-equal (duplicity-lhs)))
                   (no-duplicatesp-equal (duplicity-rhs)))
          :hints(("goal"
                  :in-theory (disable duplicity-constraint
                                      duplicity-badguy-has-high-duplicity)
                  :use ((:instance duplicity-badguy-has-high-duplicity
                                   (x (duplicity-rhs)))
                        (:instance duplicity-constraint
                                   (a (car (duplicity-badguy (duplicity-rhs))))))))))

 (local (defthm lemma2
          (implies (and (duplicity-hyp)
                        (no-duplicatesp-equal (duplicity-rhs)))
                   (no-duplicatesp-equal (duplicity-lhs)))
          :hints(("goal"
                  :in-theory (disable duplicity-constraint
                                      duplicity-badguy-has-high-duplicity)
                  :use ((:instance duplicity-badguy-has-high-duplicity
                                   (x (duplicity-lhs)))
                        (:instance duplicity-constraint
                                   (a (car (duplicity-badguy (duplicity-lhs))))))))))

 (defthm no-duplicatesp-equal-same-by-duplicity
   (implies (duplicity-hyp)
            (equal (no-duplicatesp-equal (duplicity-lhs))
                   (no-duplicatesp-equal (duplicity-rhs))))
   :hints(("goal"
           :use ((:instance lemma1)
                 (:instance lemma2))))))

