; Duplicity -- Count how many times an element occurs in a list
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
(include-book "xdoc/top" :dir :system)
(include-book "equiv")

(defsection duplicity
  :parents (defsort count no-duplicatesp)
  :short "@(call duplicity) counts how many times the element @('a') occurs
within the list @('x')."

  :long "<p>This function is similar to ACL2's built-in @(see count) function
but is more limited:</p>

<ul>

<li>@('count') can either scan for occurrences of a character in a string or
an element in a list, and can only search within some particular sub-range,
whereas</li>

<li>@('duplicity') only works on lists and always searches the entire list.</li>

</ul>

<p>In practice, these limitations make @9'duplicity') a much nicer function to
work with and reason about.</p>

<p>Reasoning about duplicity is very useful when trying to show that two lists
are permutations of one another (sometimes called multiset- or
bag-equivalence).  A classic exercise for new ACL2 users is to prove that a
permutation function is symmetric.  Hint: a duplicity-based argument may
compare quite favorably to induction on the definition of permutation.</p>"

  (defund duplicity-exec (a x n)
    (declare (xargs :guard (natp n)))
    (if (atom x)
        n
      (duplicity-exec a (cdr x)
                      (if (equal (car x) a)
                          (+ 1 n)
                        n))))

  (defund duplicity (a x)
    (declare (xargs :guard t
                    :verify-guards nil))
    (mbe :logic (cond ((atom x)
                       0)
                      ((equal (car x) a)
                       (+ 1 (duplicity a (cdr x))))
                      (t
                       (duplicity a (cdr x))))
         :exec (duplicity-exec a x 0)))

  (defthm duplicity-exec-removal
    (implies (natp n)
             (equal (duplicity-exec a x n)
                    (+ (duplicity a x) n)))
    :hints(("Goal" :in-theory (enable duplicity duplicity-exec))))

  (verify-guards duplicity
    :hints(("Goal" :in-theory (enable duplicity))))

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

  (defthm duplicity-of-list-fix
    (equal (duplicity a (list-fix x))
           (duplicity a x))
    :hints(("Goal" :induct (len x))))

  (defcong list-equiv equal (duplicity a x) 2
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (duplicity-of-list-fix))
            :use ((:instance duplicity-of-list-fix)
                  (:instance duplicity-of-list-fix (x x-equiv))))))

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
             (not (no-duplicatesp-equal x)))))


(defsection duplicity-badguy1
  :parents (duplicity-badguy)
  :short "@(call duplicity-badguy1) finds the first element of @('dom') whose
duplicity in @('x') exceeds 1, if such a member exists."

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
      :hints(("Goal" :in-theory (enable duplicity-badguy1))))))



(defsection duplicity-badguy
  :parents (duplicity no-duplicatesp-equal-same-by-duplicity)
  :short "@(call duplicity-badguy) finds an element that occurs multiple times
in the list @('x'), if one exists."

  :long "<p>This function is central to our proof of @(see
no-duplicatesp-equal-same-by-duplicity), a pick-a-point style strategy for
proving that @(see no-duplicatesp) holds of a list by reasoning about duplicity
of an arbitrary element.</p>"

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



(defsection no-duplicatesp-equal-same-by-duplicity
  :parents (no-duplicatesp-equal duplicity)
  :short "Proof strategy: show that a list satisfies @(see no-duplicatesp-equal)
because it has no element whose @(see duplicity) is over 1."

  :long "<p>This is often a good way to prove @(see no-duplicatesp).  This is a
basic pick-a-point style theorem that you can (manually) functionally
instantiate.</p>

@(def duplicity-constraint)"

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

