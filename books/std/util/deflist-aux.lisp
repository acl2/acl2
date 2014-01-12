; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "STD")
(include-book "std/osets/top" :dir :system)

; This should not be included directly.  It is just a helper book for deflist,
; and I reserve the right to eliminate and/or change it.

(encapsulate
 (((predicate *) => *))
  (local (defun predicate (x) x)))

(defund all (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (predicate (car x))
           (all (cdr x)))
    t))

(encapsulate
 (((all-hyps) => *)
  ((all-list) => *))

 (local (defun all-hyps () nil))
 (local (defun all-list () nil))

 (defthmd all-by-membership-constraint
   (implies (all-hyps)
	    (implies (member-equal arbitrary-element (all-list))
		     (predicate arbitrary-element)))))

(encapsulate
 ()
 (local (defun all-badguy (x)
          (if (consp x)
              (if (predicate (car x))
                  (all-badguy (cdr x))
                (list (car x)))
            nil)))

 (local (defthmd all-badguy-membership-property
          (implies (all-badguy x)
                   (and (member-equal (car (all-badguy x)) x)
                        (not (predicate (car (all-badguy x))))))
          :hints(("Goal" :induct (all-badguy x)))))

 (local (defthm all-badguy-under-iff
          (iff (all-badguy x)
               (not (all x)))
          :hints(("Goal" :in-theory (enable all)))))

 (defthmd all-by-membership
   (implies (all-hyps)
            (all (all-list)))
   :hints(("Goal"
           :in-theory (enable all-by-membership-constraint)
           :use ((:instance all-badguy-membership-property
                            (x (all-list))))))))

(defund subsetp-equal-trigger (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (subsetp-equal x y))

(defthm pick-a-point-subsetp-equal-strategy
  (implies (and (syntaxp (sets::rewriting-goal-lit mfc state))
		(syntaxp (sets::rewriting-conc-lit `(subsetp-equal ,x ,y) mfc state)))
	   (equal (subsetp-equal x y)
		  (subsetp-equal-trigger x y)))
  :hints(("Goal" :in-theory (enable subsetp-equal-trigger))))

(COMPUTED-HINTS::automate-instantiation
 :new-hint-name pick-a-point-subsetp-equal-hint
 :generic-theorem all-by-membership
 :generic-predicate predicate
 :generic-hyps all-hyps
 :generic-collection all-list
 :generic-collection-predicate all
 :actual-collection-predicate subsetp-equal
 :actual-trigger subsetp-equal-trigger
 :predicate-rewrite (((predicate ?x ?y) (member-equal ?x ?y)))
 :tagging-theorem pick-a-point-subsetp-equal-strategy)
