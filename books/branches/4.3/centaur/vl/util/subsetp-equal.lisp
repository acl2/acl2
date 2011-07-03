; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "VL")

; This book should be only locally included!  Define functions in util-defs
; redundantly if you need to.  Eventually this stuff should be put into a
; library.

(include-book "finite-set-theory/osets/sets" :dir :system)
(include-book "unicode/list-fix" :dir :system)
(include-book "unicode/take" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))

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



(defthm member-equal-when-not-consp
  (implies (not (consp x))
           (equal (member-equal a x)
                  nil)))

(defthm member-equal-of-cons
  (equal (member-equal a (cons b x))
         (if (equal a b)
             (cons b x)
           (member-equal a x))))

(in-theory (disable member member-eq member-equal))

(defthm member-equal-of-car-under-iff
  (iff (member-equal (car x) x)
       (consp x))
  :hints(("Goal" :in-theory (enable member-equal))))

(defthm member-equal-when-member-equal-of-cdr-under-iff
  (implies (member-equal a (cdr x))
           (member-equal a x))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable member-equal))))



; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm subsetp-is-subsetp-equal
;   (equal (subsetp x y)
;          (subsetp-equal x y))
;   :hints(("Goal" :in-theory (enable subsetp))))
; 
; (in-theory (disable subsetp))

(defthm subsetp-equal-when-not-consp
  (implies (not (consp x))
           (equal (subsetp-equal x y)
                  t)))

(defthm subsetp-equal-of-cons
  (equal (subsetp-equal (cons a x) y)
         (and (member-equal a y)
              (subsetp-equal x y))))

(in-theory (disable subsetp-equal))


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

(defthm member-equal-when-subsetp-equal
  (implies (and (member-equal a x)
                (subsetp-equal x y))
           (member-equal a y))
  :rule-classes ((:rewrite)
                 (:rewrite :corollary (implies (and (subsetp-equal x y)
                                                    (member-equal a x))
                                               (member-equal a y)))
                 (:rewrite :corollary (implies (and (not (member-equal a y))
                                                    (subsetp-equal x y))
                                               (not (member-equal a x))))
                 (:rewrite :corollary (implies (and (subsetp-equal x y)
                                                    (not (member-equal a y)))
                                               (not (member-equal a x)))))
  :hints(("Goal" :induct (len x))))

(defund subsetp-equiv (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (and (subsetp-equal x y)
       (subsetp-equal y x)))

(defthm subsetp-equal-reflexive
  (subsetp-equal x x))

(defthm subsetp-equal-transitive
  (and (implies (and (subsetp-equal x y)
                     (subsetp-equal y z))
                (subsetp-equal x z))
       (implies (and (subsetp-equal y z)
                     (subsetp-equal x y))
                (subsetp-equal x z))))

(defequiv subsetp-equiv
  :hints(("Goal" :in-theory (enable subsetp-equiv))))

(defcong subsetp-equiv iff (member-equal a x) 2
  :hints(("Goal" :in-theory (enable subsetp-equiv))))

(defcong subsetp-equiv equal (subsetp-equal x y) 1
  :hints(("Goal"
          :in-theory (enable subsetp-equiv)
          :cases ((subsetp-equal x y)))))

(defcong subsetp-equiv equal (subsetp-equal x y) 2
  :hints(("Goal"
          :in-theory (enable subsetp-equiv)
          :cases ((subsetp-equal x y)))))

(defcong subsetp-equiv subsetp-equiv (append x y) 1
  :hints(("Goal"
          :in-theory (enable subsetp-equiv))))

(defcong subsetp-equiv subsetp-equiv (append x y) 2
  :hints(("Goal"
          :in-theory (enable subsetp-equiv))))

(defcong subsetp-equiv subsetp-equiv (revappend x y) 1
  :hints(("Goal"
          :in-theory (enable subsetp-equiv))))

(defcong subsetp-equiv subsetp-equiv (revappend x y) 2
  :hints(("Goal"
          :in-theory (enable subsetp-equiv))))

(defthm reverse-under-subsetp-equiv
  (implies (true-listp x)
           (subsetp-equiv (reverse x)
                          x))
  :hints(("Goal" :in-theory (enable subsetp-equiv))))

(defthm remove-duplicates-equal-under-subsetp-equiv
  (subsetp-equiv (remove-duplicates-equal x)
                 x)
  :hints(("Goal" :in-theory (enable subsetp-equiv))))

(defthm revappend-under-subsetp-equiv
  (subsetp-equiv (revappend x y)
                 (append x y))
  :hints(("Goal" :in-theory (enable subsetp-equiv))))

(defcong subsetp-equiv subsetp-equiv (remove-duplicates-equal x) 1
  :hints(("Goal"
          :in-theory (enable subsetp-equiv))))


(defthm member-equal-of-list-fix
  (equal (member-equal a (list-fix x))
         (list-fix (member-equal a x)))
  :hints(("Goal" :induct (len x))))

(defthm subsetp-equal-of-list-fix-one
  (equal (subsetp-equal (list-fix a) x)
         (subsetp-equal a x))
  :hints(("Goal" :induct (len a))))

(defthm subsetp-equal-of-list-fix-two
  (equal (subsetp-equal a (list-fix x))
         (subsetp-equal a x))
  :hints(("Goal" :induct (len a))))

(defthm list-fix-under-subsetp-equiv
  (subsetp-equiv (list-fix x)
                 x)
  :hints(("Goal" :in-theory (enable subsetp-equiv))))


(defthm subsetp-equal-of-cdr
  (subsetp-equal (cdr x) x))



(encapsulate
 ()
 (local (defthm lemma
          (subsetp-equal x (cons a x))))

 (defthm subsetp-equiv-of-cons-self
   (equal (subsetp-equiv x (cons a x))
          (if (member-equal a x)
              t
            nil))
   :hints(("Goal" :in-theory (enable subsetp-equiv)))))

(defcong subsetp-equiv subsetp-equiv (cons a x) 2
  :hints(("Goal" :in-theory (enable subsetp-equiv))))


(encapsulate
  ()
  (local (defthmd l0
           (iff (member-equal a x)
                (< 0 (acl2::duplicity a x)))
           :hints(("Goal" :in-theory (enable acl2::duplicity)))))

  (local (defthm member-equal-same-by-duplicity
           (implies (acl2::duplicity-hyp)
                    (iff (member-equal a (acl2::duplicity-lhs))
                         (member-equal a (acl2::duplicity-rhs))))
           :hints(("Goal"
                   :in-theory (enable l0)
                   :use ((:instance acl2::duplicity-constraint
                                    (acl2::a a)))))))

  (local (defthm subsetp-equal-by-duplicity-1
           (implies (acl2::duplicity-hyp)
                    (subsetp-equal (acl2::duplicity-lhs)
                                   (acl2::duplicity-rhs)))))

  (local (defthm subsetp-equal-by-duplicity-2
           (implies (acl2::duplicity-hyp)
                    (subsetp-equal (acl2::duplicity-rhs)
                                   (acl2::duplicity-lhs)))))

  (defthmd subsetp-equiv-by-duplicity
    (implies (acl2::duplicity-hyp)
             (subsetp-equiv (acl2::duplicity-lhs)
                            (acl2::duplicity-rhs)))
    :hints(("Goal" :in-theory (enable subsetp-equiv)))))

(defcong subsetp-equiv subsetp-equiv (acl2::<<-sort x) 1
  :hints(("Goal"
          :use ((:functional-instance
                 subsetp-equiv-by-duplicity
                 (acl2::duplicity-hyp (lambda () t))
                 (acl2::duplicity-rhs (lambda () (acl2::<<-sort x)))
                 (acl2::duplicity-lhs (lambda () x)))
                (:functional-instance
                 subsetp-equiv-by-duplicity
                 (acl2::duplicity-hyp (lambda () t))
                 (acl2::duplicity-rhs (lambda () (acl2::<<-sort x-equiv)))
                 (acl2::duplicity-lhs (lambda () x-equiv)))))))

(defthm <<-sort-under-subsetp-equiv
  (subsetp-equiv (acl2::<<-sort x) x)
  :hints(("Goal"
          :use ((:functional-instance
                 subsetp-equiv-by-duplicity
                 (acl2::duplicity-hyp (lambda () t))
                 (acl2::duplicity-rhs (lambda () (acl2::<<-sort x)))
                 (acl2::duplicity-lhs (lambda () x)))))))



(encapsulate
  ()
  (local (defthm l0
           (implies (and (string-listp y)
                         (member-equal a y))
                    (stringp a))))

  (defthm string-listp-when-subsetp-equal-of-string-listp
    (implies (and (string-listp y)
                  (subsetp-equal x y))
             (equal (string-listp x)
                    (true-listp x)))
    :hints(("Goal" :induct (len x)))
    :rule-classes ((:rewrite)
                   (:rewrite :corollary
                             (implies (and (subsetp-equal x y)
                                           (string-listp y))
                                      (equal (string-listp x)
                                             (true-listp x)))))))


(encapsulate
  ()
  (local (defthm l0
           (implies (and (symbol-listp y)
                         (member-equal a y))
                    (symbolp a))))

  (defthm symbol-listp-when-subsetp-equal-of-symbol-listp
    (implies (and (symbol-listp y)
                  (subsetp-equal x y))
             (equal (symbol-listp x)
                    (true-listp x)))
    :hints(("Goal" :induct (len x)))
    :rule-classes ((:rewrite)
                   (:rewrite :corollary
                             (implies (and (subsetp-equal x y)
                                           (symbol-listp y))
                                      (equal (symbol-listp x)
                                             (true-listp x)))))))


(defthm subsetp-equal-of-duplicated-members
  (subsetp-equal (duplicated-members x) x))

(defthm subsetp-equal-of-hons-duplicated-members
  (subsetp-equal (hons-duplicated-members x) x))

(defthm string-listp-of-duplicated-members
  (implies (string-listp x)
           (string-listp (duplicated-members x))))

(defthm symbol-listp-of-duplicated-members
  (implies (symbol-listp x)
           (symbol-listp (duplicated-members x))))

(defthm string-listp-of-hons-duplicated-members
  (implies (string-listp x)
           (string-listp (hons-duplicated-members x))))

(defthm symbol-listp-of-hons-duplicated-members
  (implies (symbol-listp x)
           (symbol-listp (hons-duplicated-members x))))



(defthm simpler-take-of-len
  (equal (simpler-take (len x) x)
         (list-fix x))
  :hints(("Goal" :in-theory (enable simpler-take))))

(defthm no-duplicatesp-equal-of-list-fix
  (equal (no-duplicatesp-equal (list-fix x))
         (no-duplicatesp-equal x)))




(defthm acl2-count-when-member-equal
  (implies (member-equal a x)
           (< (acl2-count a) (acl2-count x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable member-equal acl2-count))))

(defthm member-equal-self
  (not (member-equal x x))
  :hints(("Goal"
          :in-theory (disable acl2-count-when-member-equal)
          :use ((:instance acl2-count-when-member-equal
                           (a x) (x x))))))
