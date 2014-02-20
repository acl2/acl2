; Basic Lists-as-Sets Reasoning
; Copyright (C) 2008-2013 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "equiv")
(include-book "mfc-utils")
(include-book "rev")
(include-book "rcons")
(include-book "flatten")

(local (defthm equal-of-booleans-to-iff
         (implies (and (booleanp a) (booleanp b))
                  (equal (equal a b) (iff a b)))))

(defxdoc std/lists/member
  :parents (std/lists member)
  :short "Lemmas about @(see member) available in the @(see std/lists)
library.")

(defxdoc std/lists/subsetp
  :parents (std/lists subsetp)
  :short "Lemmas about @(see subsetp) available in the @(see std/lists)
library.")


(defsection basic-member-lemmas
  :parents (std/lists/member)
  :short "Very basic lemmas about @(see member)."

  (defthm member-when-atom
    (implies (atom x)
             (not (member a x))))

  (defthm member-of-cons
    (equal (member a (cons b x))
           (if (equal a b)
               (cons b x)
             (member a x))))

  (defthm member-of-car
    (equal (member (car x) x)
           (if (consp x)
               x
             nil)))

  (defthm member-of-append
    (iff (member a (append x y))
         (or (member a x)
             (member a y))))

  (local (defthm l0
           (implies (member a y)
                    (not (member a (set-difference-equal x y))))))

  (defthm member-of-set-difference-equal
    (iff (member a (set-difference-equal x y))
         (and (member a x)
              (not (member a y))))
    :hints(("Goal" :induct (len x))))

  (local (defthm l1
           (implies (not (member a y))
                    (not (member a (intersection-equal x y))))))

  (defthm member-of-intersection-equal
    (iff (member a (intersection-equal x y))
         (and (member a x)
              (member a y)))
    :hints(("Goal" :induct (len x))))

  (local (defthm l2
           (not (member a (remove a x)))))

  (defthm member-of-remove
    (iff (member a (remove b x))
         (and (member a x)
              (not (equal a b))))
    :hints(("Goal" :induct (len x))))

  (defthm acl2-count-when-member
    (implies (member a x)
             (< (acl2-count a) (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable member acl2-count))))

  (defthm member-self
    (not (member x x))
    :hints(("Goal"
            :in-theory (disable acl2-count-when-member)
            :use ((:instance acl2-count-when-member (a x)))))))




(defsection basic-subsetp-lemmas
  :parents (std/lists/subsetp)
  :short "Very basic lemmas about @(see subsetp)."

  (defthm subsetp-when-atom-left
    (implies (atom x)
             (subsetp x y)))

  (defthm subsetp-when-atom-right
    (implies (atom y)
             (equal (subsetp x y)
                    (atom x)))
    :hints(("Goal" :in-theory (enable subsetp))))

  (defthm subsetp-nil
    (subsetp nil x))

  (defthm subsetp-of-cons
    (equal (subsetp (cons a x) y)
           (if (member a y)
               (subsetp x y)
             nil)))

  (defthm subsetp-member
    (implies (and (member a x)
                  (subsetp x y))
             (member a y))
    :rule-classes ((:rewrite)
                   (:rewrite :corollary (implies (and (subsetp x y)
                                                      (member a x))
                                                 (member a y)))
                   (:rewrite :corollary (implies (and (not (member a y))
                                                      (subsetp x y))
                                                 (not (member a x))))
                   (:rewrite :corollary (implies (and (subsetp x y)
                                                      (not (member a y)))
                                                 (not (member a x)))))
    :hints(("Goal" :induct (len x)))))



(defsection subsetp-witness
  :parents (std/lists)
  :short "@(call subsetp-witness) finds an element of @('x') that is not a
member of @('y'), if one exists."

  :long "<p>This function is useful for basic pick-a-point style reasoning
about subsets.</p>"

  (defund subsetp-witness (x y)
    (if (atom x)
        nil
      (if (member (car x) y)
          (subsetp-witness (cdr x) y)
        (car x))))

  (local (in-theory (enable subsetp-witness)))

  (defthmd subsetp-witness-correct
    (let ((a (subsetp-witness x y)))
      (iff (subsetp x y)
           (implies (member a x)
                    (member a y)))))

  (defthm subsetp-witness-rw
    (implies (rewriting-positive-literal `(subsetp-equal ,x ,y))
             (let ((a (subsetp-witness x y)))
               (iff (subsetp x y)
                    (implies (member a x)
                             (member a y)))))
    :hints(("Goal" :in-theory (enable subsetp-witness-correct)))))


(defsection intersectp-witness
  :parents (std/lists intersectp)
  :short "@(call intersectp-witness) finds a some element that is a member
of both @('x') and @('y'), if one exists."

  :long "<p>This function is useful for basic pick-a-point style reasoning
about set intersection.</p>"

  (defund intersectp-witness (x y)
    (if (atom x)
        nil
      (if (member (car x) y)
          (car x)
        (intersectp-witness (cdr x) y))))

  (local (in-theory (enable intersectp-witness)))

  (defthmd intersectp-witness-correct
    (let ((a (intersectp-witness x y)))
      (equal (intersectp x y)
             (and (member a x)
                  (member a y)
                  t)))
    :hints(("Goal" :in-theory (enable member))))

  (defthm intersectp-witness-rw
    (implies (rewriting-negative-literal `(intersectp-equal ,x ,y))
             (let ((a (intersectp-witness x y)))
               (equal (intersectp x y)
                      (and (member a x)
                           (member a y)
                           t))))
    :hints(("Goal" :in-theory (enable intersectp-witness-correct)))))


(defsection more-basic-subsetp-lemmas
  :extension basic-subsetp-lemmas

  (defthm subsetp-refl
    (subsetp x x))

  (defthm subsetp-trans
    (implies (and (subsetp x y)
                  (subsetp y z))
             (subsetp x z))
    :hints(("Goal" :in-theory (enable subsetp-member))))

  (defthm subsetp-trans2
    (implies (and (subsetp y z)
                  (subsetp x y))
             (subsetp x z))
    :hints(("Goal" :in-theory (enable subsetp-member))))

  (defthm subsetp-implies-subsetp-cdr
    (implies (subsetp x y)
             (subsetp (cdr x) y)))

  (defthm subsetp-of-cdr
    (subsetp (cdr x) x)))



(defthmd intersectp-member
  ;; BOZO what is this doing here?
  (implies (and (member a x)
                (member a y))
           (equal (intersectp x y) t)))


(local (in-theory (enable subsetp-member)))

(defsection set-equiv
  :parents (std/lists)
  :short "@(call set-equiv) is an @(see equivalence) relation that determines
whether @('x') and @('y') have the same members, in the sense of @(see
member)."

  :long "<p>This is a very useful equivalence relation; typically any function
that treats lists as sets will have good @('set-equiv') @(see congruence)
properties.</p>

<p>We prove various congruences and rewrites relating @('set-equiv') to basic
list functions like @(see append), @(see reverse), @(see set-difference$),
@(see union$), etc.  This is often sufficient for lightweight set reasoning.  A
heavier-weight (but not necessarily recommended) alternative is to use the
@(see std/osets) library.</p>"

  (defun set-equiv (x y)
    (declare (xargs :guard (and (true-listp x)
                                (true-listp y))))
    (and (subsetp-equal x y)
         (subsetp-equal y x)))

  (defthm set-equiv-implies-iff
    (implies (set-equiv x y)
             (equal (iff (member a x)
                         (member a y))
                    t)))

  (encapsulate
    ()
    (local (defthm set-equiv-refl
             ;; Automatic after defequiv
             (set-equiv x x)))

    (defthm set-equiv-asym
      ;; NOT automatic after defequiv, so make it non-local
      (equal (set-equiv x y)
             (set-equiv y x)))

    (local (defthm set-equiv-trans
             ;; Automatic after defequiv
             (implies (and (set-equiv x y)
                           (set-equiv y z))
                      (set-equiv x z))))

    (defequiv set-equiv))

  (defrefinement list-equiv set-equiv))


(defsection set-equiv-congruences
  :parents (set-equiv)
  :short "Basic congruence rules relating @(see set-equiv) to list functions."

  (defcong set-equiv iff (member x y) 2)

  (defcong set-equiv equal (subsetp x y) 2)
  (defcong set-equiv equal (subsetp x y) 1))

(local (in-theory (disable member)))
(in-theory (disable subsetp intersectp set-equiv))

(defsection set-unequal-witness
  :parents (set-equiv)
  :short "@(call set-unequal-witness) finds a member of @('x') that is not
a member of @('y'), or vice versa."

  :long "<p>This function is useful for basic pick-a-point style reasoning
about set equivalence.</p>"

  (defund set-unequal-witness (x y)
    (cond ((not (subsetp x y))
           (subsetp-witness x y))
          ((not (subsetp y x))
           (subsetp-witness y x))))

  (local (in-theory (enable set-unequal-witness
                            subsetp-member
                            set-equiv)))

  (defthmd set-unequal-witness-correct
    (equal (set-equiv x y)
           (iff (member (set-unequal-witness x y) x)
                (member (set-unequal-witness x y) y))))

  (defthm set-unequal-witness-rw
    (implies (rewriting-positive-literal `(set-equiv ,x ,y))
             (equal (set-equiv x y)
                    (iff (member (set-unequal-witness x y) x)
                         (member (set-unequal-witness x y) y))))))


(defsection more-set-equiv-congruences
  :extension set-equiv-congruences

  (defcong set-equiv equal (intersection-equal x y) 2)
  (defcong set-equiv set-equiv (intersection-equal x y) 1)

  (defcong set-equiv equal (set-difference-equal x y) 2)
  (defcong set-equiv set-equiv (set-difference-equal x y) 1))


(deftheory set-reasoning-witnesses
  '(set-unequal-witness-rw
    subsetp-witness-rw
    intersectp-witness-rw))

(in-theory (disable set-reasoning-witnesses))


(defsection more-set-equiv-congruences
  :extension set-equiv-congruences

  (defcong set-equiv equal (consp x) 1
    :hints(("Goal" :in-theory (enable set-equiv subsetp))))

  (defcong set-equiv equal (atom x) 1)

  (defthmd intersectp-iff-intersection-equal
    ;; BOZO this seems like a good rule, why disable it?
    (iff (consp (intersection-equal x y))
         (intersectp x y))
    :hints(("Goal" :in-theory (enable intersection-equal
                                      intersectp))))

  (defcong set-equiv equal (intersectp x y) 1
    :hints(("Goal" :use ((:instance intersectp-iff-intersection-equal)
                         (:instance intersectp-iff-intersection-equal (x x-equiv))))))

  (defcong set-equiv equal (intersectp x y) 2
    :hints(("Goal" :use ((:instance intersectp-iff-intersection-equal)
                         (:instance intersectp-iff-intersection-equal (y y-equiv)))))))

(local (in-theory (disable set-difference-equal intersection-equal)))



(defsection more-subsetp-rules
  :extension basic-subsetp-lemmas

  (defthm subsetp-cons-same
    (implies (subsetp a b)
             (subsetp (cons x a) (cons x b)))
    :hints(("Goal" :in-theory (enable subsetp))))

  (defthm subsetp-cons-2
    (implies (subsetp a b)
             (subsetp a (cons x b)))
    :hints(("Goal" :in-theory (enable subsetp))))

  (defthm subsetp-append1
    (equal (subsetp (append a b) c)
           (and (subsetp a c)
                (subsetp b c))))

  (defthm subsetp-append2
    (subsetp a (append a b)))

  (defthm subsetp-append3
    (subsetp b (append a b)))

  (defthm subsetp-of-append-when-subset-of-either
    (implies (or (subsetp a b)
                 (subsetp a c))
             (subsetp a (append b c))))

  (defthm subsetp-car-member
    (implies (and (subsetp x y)
                  (consp x))
             (member (car x) y))
    :hints(("Goal" :in-theory (enable subsetp))))

  (defthm subsetp-intersection-equal
    (iff (subsetp a (intersection-equal b c))
         (and (subsetp a b)
              (subsetp a c)))
    :hints(("Goal" :in-theory (enable subsetp)))))


(defthm union-equal-under-set-equiv
  (set-equiv (union-equal a b)
             (append a b))
  :hints(("Goal" :in-theory (enable set-equiv))))

(defcong set-equiv set-equiv (append x y) 2
  :hints(("Goal" :in-theory (enable set-equiv))))

(defcong set-equiv set-equiv (append x y) 1
  :hints(("Goal" :in-theory (enable set-equiv))))





; Some additional rules that are useful for canoncializing APPEND nests under SET-EQUIV

(defthm commutativity-of-append-under-set-equiv
  (set-equiv (append x y)
              (append y x))
  :hints(("Goal" :in-theory (enable set-equiv))))

(defthm commutativity-2-of-append-under-set-equiv
  (set-equiv (append x (append y z))
              (append y (append x z)))
  :hints(("Goal" :in-theory (enable set-equiv))))

(defthm cancel-append-self-under-set-equiv
  (set-equiv (append x x)
              x)
  :hints(("Goal" :in-theory (enable set-equiv))))

(defthm cancel-append-self-2-under-set-equiv
  (set-equiv (append x x y)
              (append x y))
  :hints(("Goal" :in-theory (enable set-equiv))))

(encapsulate
  ()
  (local (defthm l0
           (implies (set-equiv x (append x y))
                    (subsetp y x))))

  (local (defthm l1
           (implies (subsetp y x)
                    (set-equiv (append x y) x))
           :hints(("Goal" :in-theory (enable set-equiv)))))

  (defthm set-equiv-with-append-other-right
    (equal (set-equiv x (append x y))
           (subsetp y x))
    :hints(("Goal"
            :use ((:instance l0)
                  (:instance l1)))))

  (defthm set-equiv-with-append-other-left
    (equal (set-equiv x (append y x))
           (subsetp y x))))

(defthm append-singleton-under-set-equiv
  (set-equiv (append x (list a))
             (cons a x))
  :hints(("Goal" :in-theory (enable set-equiv))))



(encapsulate
  ()
  (local (in-theory (disable revappend-removal)))

  (defthm member-of-revappend
    (iff (member x (revappend a b))
         (or (member x a)
             (member x b))))

  (local (defthm subsetp-revappend1
           (equal (subsetp (revappend a b) c)
                  (and (subsetp a c)
                       (subsetp b c)))))

  (local (defthm subsetp-revappend-2
           (subsetp a (revappend a b))))

  (local (defthm subsetp-revappend3
           (subsetp b (revappend a b))))

  (local (defthm subsetp-of-revappend-when-subset-of-either
           (implies (or (subsetp a b)
                        (subsetp a c))
                    (subsetp a (revappend b c)))))

  (defthm revappend-under-set-equiv
    (set-equiv (revappend x y)
                (append x y))
    :hints(("Goal" :in-theory (enable set-equiv)))))


(defthm reverse-under-set-equiv
  ;; Goofy, since reverse works on strings, but hey, a reversed string
  ;; is still set-equivalent to an unreversed string, so why not?
  (set-equiv (reverse x) x)
  :hints(("Goal" :in-theory (enable set-equiv))))



(encapsulate ()

  (defthm member-of-remove-duplicates-equal
    (iff (member a (remove-duplicates-equal x))
         (member a x))
    :hints(("Goal" :in-theory (enable remove-duplicates-equal))))

  (defthm remove-duplicates-equal-under-set-equiv
    (set-equiv (remove-duplicates-equal x)
               x)
    :hints(("Goal" :in-theory (enable set-equiv)))))



(defthm set-equiv-of-cons-self
   (equal (set-equiv x (cons a x))
          (if (member a x)
              t
            nil))
   :hints(("Goal" :in-theory (enable set-equiv))))

(defcong set-equiv set-equiv (cons a x) 2
  :hints(("Goal" :in-theory (enable set-equiv))))

(defthm subsetp-of-remove1
  (equal (subsetp x (remove a y))
         (and (subsetp x y)
              (not (member a x))))
  :hints(("Goal" :in-theory (enable remove subsetp member))))

(defthm subsetp-of-remove2
  (implies (subsetp x y)
           (subsetp (remove a x) y)))

(defcong set-equiv set-equiv (remove a x) 2
  :hints(("Goal" :in-theory (enable set-equiv))))

(defthm rev-under-set-equiv
  (set-equiv (rev x) x)
  :hints(("Goal"
          :in-theory (disable revappend-removal)
          :use ((:instance revappend-removal (x x) (y nil))))))

(encapsulate ()

  (local (in-theory (enable flatten)))

  (local (defthm l1
           (implies (and (member e X)
                         (member a e))
                    (member a (flatten X)))))

  (local (defthm l3
           (implies (member a x)
                    (subsetp a (flatten x)))
           :hints(("goal" :induct (len x)))))

  (local (defthm l5
           (implies (subsetp x y)
                    (subsetp (flatten x) (flatten y)))
           :hints(("goal" :induct (len x)))))

  (local (defthm l6
           (implies (subsetp x y)
                    (subsetp (flatten x) (flatten y)))
           :hints(("goal" :induct (len x)))))

  (defcong set-equiv set-equiv (flatten x) 1
    :hints(("Goal" :in-theory (enable set-equiv)))))


(defthm rcons-under-set-equiv
  (set-equiv (rcons a x)
             (cons a x))
  :hints(("Goal" :in-theory (enable rcons))))

