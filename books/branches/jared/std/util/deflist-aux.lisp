; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
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
  (implies (and (syntaxp (set::rewriting-goal-lit mfc state))
		(syntaxp (set::rewriting-conc-lit `(subsetp-equal ,x ,y) mfc state)))
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
