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

(include-book "centaur/misc/equal-sets" :dir :system)
(include-book "finite-set-theory/osets/sets" :dir :system)
(include-book "unicode/list-fix" :dir :system)
(include-book "unicode/take" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))

(in-theory (disable member member-eq member-equal
                    subsetp subsetp-eq subsetp-equal))

;; These are disabled in equal-sets.lisp because they can sometimes be
;; expensive.  But I prefer to leave them enabled by default, and just disable
;; them when they become expensive.
(in-theory (enable acl2::subsetp-equal-member
                   acl2::subsetp-equal-trans2))


(defthm member-equal-when-member-equal-of-cdr-under-iff
  (implies (member-equal a (cdr x))
           (member-equal a x))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))


;; BOZO some of this, especially the congruences, should be moved to equal-sets

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

(defthm list-fix-under-set-equivp
  (set-equivp (list-fix x) x)
  :hints((set-reasoning)))




(defsection set-equivp-by-duplicity

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

  (defthmd set-equivp-by-duplicity
    (implies (acl2::duplicity-hyp)
             (set-equivp (acl2::duplicity-lhs)
                         (acl2::duplicity-rhs)))
    :hints((set-reasoning))))

(defcong set-equivp set-equivp (acl2::<<-sort x) 1
  :hints(("Goal"
          :use ((:functional-instance
                 set-equivp-by-duplicity
                 (acl2::duplicity-hyp (lambda () t))
                 (acl2::duplicity-rhs (lambda () (acl2::<<-sort x)))
                 (acl2::duplicity-lhs (lambda () x)))
                (:functional-instance
                 set-equivp-by-duplicity
                 (acl2::duplicity-hyp (lambda () t))
                 (acl2::duplicity-rhs (lambda () (acl2::<<-sort acl2::x-equiv)))
                 (acl2::duplicity-lhs (lambda () acl2::x-equiv)))))))

(defthm <<-sort-under-set-equivp
  (set-equivp (acl2::<<-sort x) x)
  :hints(("Goal"
          :use ((:functional-instance set-equivp-by-duplicity
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
  (subsetp-equal (duplicated-members x) x)
  :hints((set-reasoning)))

(defthm subsetp-equal-of-hons-duplicated-members
  (subsetp-equal (hons-duplicated-members x) x)
  :hints((set-reasoning)))

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



;; BOZO why are these here?

(defthm simpler-take-of-len
  (equal (simpler-take (len x) x)
         (list-fix x))
  :hints(("Goal" :in-theory (enable simpler-take))))

(defthm no-duplicatesp-equal-of-list-fix
  (equal (no-duplicatesp-equal (list-fix x))
         (no-duplicatesp-equal x)))




