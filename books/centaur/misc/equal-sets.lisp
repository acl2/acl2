; Centaur Miscellaneous Books
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(local (defthm equal-of-booleans-to-iff
         (implies (and (booleanp a) (booleanp b))
                  (equal (equal a b) (iff a b)))))


;; built into ACL2 now.
;; (defun intersection-equal (x y)
;;   (declare (xargs :guard (and (true-listp x) (true-listp y))))
;;   (cond ((endp x) nil)
;;         ((member-equal (car x) y)
;;          (cons (car x)
;;                (intersection-equal (cdr x) y)))
;;         (t (intersection-equal (cdr x) y))))

(defthm set-difference-equal-member
  (iff (member-equal x (set-difference-equal a b))
       (and (member-equal x a)
            (not (member-equal x b)))))

(defthm intersection-equal-member
  (iff (member-equal x (intersection-equal a b))
       (and (member-equal x a)
            (member-equal x b))))


(defthmd subsetp-equal-member
  (implies (and (subsetp-equal x y)
                (member-equal a x))
           (member-equal a y)))

(defthmd subsetp-equal-member2
  (implies (and (member-equal a x)
                (subsetp-equal x y))
           (member-equal a y)))

(defthmd subsetp-equal-not-member
  (implies (and (subsetp-equal a b)
                (not (member-equal k b)))
           (not (member-equal k a)))
  :hints(("Goal" :in-theory (enable subsetp-equal-member))))

(defthmd subsetp-equal-not-member2
  (implies (and (not (member-equal k b))
                (subsetp-equal a b))
           (not (member-equal k a)))
  :hints(("Goal" :in-theory (enable subsetp-equal-member))))

(defthm cons-member-equal
  (iff (member-equal a (cons x y))
       (or (equal x a)
           (member-equal a y))))

(defthm member-equal-atom
  (implies (atom a)
           (not (member-equal x a))))

(defun subsetp-equal-witness (x y)
  (if (atom x)
      nil
    (if (member-equal (car x) y)
        (subsetp-equal-witness (cdr x) y)
      (car x))))

(defthmd subsetp-equal-witness-correct
  (let ((a (subsetp-equal-witness x y)))
    (iff (subsetp-equal x y)
         (implies (member-equal a x)
                  (member-equal a y)))))

(include-book "coi/util/in-conclusion" :dir :system)


(defthm subsetp-equal-witness-rw
  (implies (in-conclusion-check (subsetp-equal x y)
                                :top :negated)
           (let ((a (subsetp-equal-witness x y)))
             (iff (subsetp-equal x y)
                  (implies (member-equal a x)
                           (member-equal a y)))))
  :hints(("Goal" :in-theory (enable subsetp-equal-witness-correct))))

(in-theory (disable subsetp-equal-witness))

(defthm subsetp-equal-refl
  (subsetp-equal x x))


(defthm subsetp-equal-trans
  (implies (and (subsetp-equal x y)
                (subsetp-equal y z))
           (subsetp-equal x z))
  :hints(("Goal" :in-theory (enable subsetp-equal-member))))

(defthmd subsetp-equal-trans2
  (implies (and (subsetp-equal y z)
                (subsetp-equal x y))
           (subsetp-equal x z))
  :hints(("Goal" :in-theory (enable subsetp-equal-member))))

(defun intersectp-equal-witness (x y)
  (if (atom x)
      nil
    (if (member-equal (car x) y)
        (car x)
      (intersectp-equal-witness (cdr x) y))))

(defthmd intersectp-equal-witness-correct
  (let ((a (intersectp-equal-witness x y)))
    (equal (intersectp-equal x y)
           (and (member-equal a x)
                (member-equal a y)
                t)))
  :hints(("Goal" :in-theory (enable member-equal))))

(defthm intersectp-equal-witness-rw
  (implies (in-conclusion-check (intersectp-equal x y)
                                :top t)
           (let ((a (intersectp-equal-witness x y)))
             (equal (intersectp-equal x y)
                    (and (member-equal a x)
                         (member-equal a y)
                         t))))
  :hints(("Goal" :in-theory (enable intersectp-equal-witness-correct))))

(in-theory (disable intersectp-equal-witness))

(defthmd intersectp-equal-member
  (implies (and (member-equal a x)
                (member-equal a y))
           (equal (intersectp-equal x y) t)))


(defthm subsetp-equal-nil
  (subsetp-equal nil x))

(defthm subsetp-equal-implies-subsetp-equal-cdr
  (implies (subsetp-equal x y)
           (subsetp-equal (cdr x) y)))


(defun set-equivp (x y)
  (and (subsetp-equal x y)
       (subsetp-equal y x)))

(local (in-theory (enable subsetp-equal-member)))

(defthm set-equivp-implies-iff
  (implies (set-equivp x y)
           (equal (iff (member-equal a x)
                       (member-equal a y))
                  t)))

(defthm set-equivp-refl
  (set-equivp x x))

(defthm set-equivp-asym
  (implies (set-equivp x y) (set-equivp y x)))


(defthm set-equivp-trans
  (implies (and (set-equivp x y)
                (set-equivp y z))
           (set-equivp x z)))

(defequiv set-equivp)

(defcong set-equivp iff (member-equal x y) 2)

(defcong set-equivp equal (subsetp-equal x y) 2)

(defcong set-equivp equal (subsetp-equal x y) 1)

(defun set-unequal-witness (x y)
  (cond ((not (subsetp-equal x y))
         (subsetp-equal-witness x y))
        ((not (subsetp-equal y x))
         (subsetp-equal-witness y x))))

(defthmd set-unequal-witness-correct
  (equal (set-equivp x y)
         (iff (member-equal (set-unequal-witness x y) x)
              (member-equal (set-unequal-witness x y) y))))

(defthm set-unequal-witness-rw
  (implies (in-conclusion-check (set-equivp x y)
                                :top :negated)
           (equal (set-equivp x y)
                  (iff (member-equal (set-unequal-witness x y) x)
                       (member-equal (set-unequal-witness x y) y)))))


(in-theory (disable subsetp-equal
                    intersectp-equal set-unequal-witness))

(local (in-theory (disable member-equal set-equivp)))

(defcong set-equivp equal (intersection-equal x y) 2)

(defcong set-equivp set-equivp (intersection-equal x y) 1)

(defcong set-equivp equal (set-difference-equal x y) 2)

(defcong set-equivp set-equivp (set-difference-equal x y) 1)

(in-theory (disable set-equivp))



;; Set reasoning for WITNESS-CP.

(include-book "witness-cp")

(defwitness subsetp-equal-witnessing
  :predicate (not (subsetp-equal x y))
  :expr (and (member-equal (subsetp-equal-witness
                            x y) x)
             (not (member-equal (subsetp-equal-witness
                                 x y) y)))
  :hints ('(:in-theory (e/d
                        (subsetp-equal-witness-correct)
                        (subsetp-equal
                         member-equal))))
  :generalize (((subsetp-equal-witness x y) . ssew)))

(defwitness intersectp-equal-witnessing
  :predicate (intersectp-equal x y)
  :expr (and (member-equal (intersectp-equal-witness x y) x)
             (member-equal (intersectp-equal-witness x y) y))
  :hints ('(:in-theory (e/d
                        (intersectp-equal-witness-correct)
                        (intersectp-equal
                         member-equal))))
  :generalize (((intersectp-equal-witness x y) . iew)))

(defwitness set-equivp-witnessing
  :predicate (not (set-equivp x y))
  :expr (not (iff (member-equal (set-unequal-witness x y) x)
                  (member-equal (set-unequal-witness x y) y)))
  :hints ('(:in-theory (e/d
                        (set-unequal-witness-correct)
                        (set-equivp member-equal))))
  :generalize (((set-unequal-witness x y) . seqw)))

(defwitness set-consp-witnessing
  :predicate (consp x)
  :expr (member-equal (car x) x)
  :hints ('(:in-theory (enable member-equal)))
  :generalize nil)


(definstantiate subsetp-equal-instancing
  :predicate (subsetp-equal x y)
  :vars (k)
  :expr (implies (member-equal k x)
                 (member-equal k y))
  :hints ('(:in-theory (e/d (subsetp-equal-member)
                            (subsetp-equal
                             member-equal)))))

(definstantiate set-equivp-instancing
  :predicate (set-equivp x y)
  :vars (k)
  :expr (iff (member-equal k x)
             (member-equal k y))
  :hints ('(:in-theory (e/d ()
                            (set-equivp member-equal)))))

(definstantiate intersectp-equal-instancing
  :predicate (not (intersectp-equal x y))
  :vars (k)
  :expr (or (not (member-equal k x))
            (not (member-equal k y)))
  :hints ('(:in-theory (e/d (intersectp-equal-member)
                            (intersectp-equal
                             member-equal)))))

(definstantiate consp-instancing
  :predicate (not (consp x))
  :vars (k)
  :expr (not (member-equal k x))
  :hints ('(:in-theory (enable member-equal))))


(defexample intersectp-equal-member-template
  :pattern (member-equal k y)
  :templates (k)
  :instance-rulename intersectp-equal-instancing)

(defexample subsetp-equal-member-template
  :pattern (member-equal k y)
  :templates (k)
  :instance-rulename subsetp-equal-instancing)

(defexample set-equivp-member-template
  :pattern (member-equal k y)
  :templates (k)
  :instance-rulename set-equivp-instancing)

(defexample consp-member-template
  :pattern (member-equal k y)
  :templates (k)
  :instance-rulename consp-instancing)


(def-witness-ruleset set-reasoning-rules
  '(subsetp-equal-witnessing
    intersectp-equal-witnessing
    set-equivp-witnessing
    set-consp-witnessing
    subsetp-equal-instancing
    set-equivp-instancing
    intersectp-equal-instancing
    consp-instancing
    intersectp-equal-member-template
    subsetp-equal-member-template
    consp-member-template
    set-equivp-member-template))

(def-witness-ruleset set-reasoning-no-consp
  '(subsetp-equal-witnessing
    intersectp-equal-witnessing
    set-equivp-witnessing
    subsetp-equal-instancing
    set-equivp-instancing
    intersectp-equal-instancing
    intersectp-equal-member-template
    subsetp-equal-member-template
    set-equivp-member-template))


(defmacro set-reasoning ()
  '(witness :ruleset set-reasoning-rules))




(defcong set-equivp equal (intersectp-equal x y) 1
  :hints ((set-reasoning)))

(defcong set-equivp equal (intersectp-equal x y) 2
  :hints((set-reasoning)))

(defcong set-equivp equal (atom x) 1
  :hints ((set-reasoning)))

(defcong set-equivp equal (consp x) 1
  :hints ((set-reasoning)))


(in-theory (disable set-difference-equal intersection-equal))




(defthmd intersectp-equal-iff-intersection-equal
  (iff (consp (intersection-equal x y))
       (intersectp-equal x y))
  :hints((set-reasoning)))



(defthmd intersectp-of-superset
  (implies (and (intersectp-equal a b)
                (subsetp-equal a c))
           (intersectp-equal c b))
  :hints ((set-reasoning))
  :rule-classes ((:rewrite :match-free :all)))

(defthmd intersectp-of-superset2
  (implies (and (subsetp-equal a c)
                (intersectp-equal b a))
           (intersectp-equal b c))
  :hints ((set-reasoning))
  :rule-classes ((:rewrite :match-free :all)))




(defthm subsetp-equal-cons-same
  (implies (subsetp-equal a b)
           (subsetp-equal (cons x a) (cons x b)))
  :hints ((set-reasoning)))

(defthm subsetp-equal-cons-2
  (implies (subsetp-equal a b)
           (subsetp-equal a (cons x b)))
  :hints ((set-reasoning)))


(defthm append-member
  (iff (member-equal x (append a b))
       (or (member-equal x a)
           (member-equal x b)))
  :hints(("Goal" :in-theory (enable member-equal))))

(defthm subsetp-equal-append1
  (equal (subsetp-equal (append a b) c)
         (and (subsetp-equal a c)
              (subsetp-equal b c))))

(defthm subsetp-equal-append2
  (subsetp-equal a (append a b)))

(defthm subsetp-equal-append3
  (subsetp-equal b (append a b)))

(defthm subsetp-equal-of-append-when-subset-of-either
  (implies (or (subsetp-equal a b)
               (subsetp-equal a c))
           (subsetp-equal a (append b c))))

(defthm subsetp-car-member-equal
  (implies (and (subsetp-equal x y)
                (consp x))
           (member-equal (car x) y))
  :hints(("Goal" :in-theory (enable subsetp-equal))))



(defthm subsetp-equal-atom
  (implies (atom y)
           (equal (subsetp-equal x y)
                  (atom x)))
  :hints(("Goal" :in-theory (enable subsetp-equal))))


(defthm subsetp-equal-intersection-equal
  (iff (subsetp-equal a (intersection-equal b c))
       (and (subsetp-equal a b)
            (subsetp-equal a c)))
  :hints ((set-reasoning)))


(defthm union-equal-is-append
  (set-equivp (union-equal a b)
              (append a b)))


(defcong set-equivp set-equivp (append x y) 2)

(defcong set-equivp set-equivp (append x y) 1)


(deftheory set-reasoning-witnesses
  '(set-unequal-witness-rw
    subsetp-equal-witness-rw
    intersectp-equal-witness-rw))

(in-theory (disable set-reasoning-witnesses))


(include-book "finite-set-theory/osets/sets" :dir :system)
(local (include-book "finite-set-theory/osets/set-order" :dir :system))


;; BOZO talk to sol about whether these should become defwitness nonsense

(local (defthm l0
         (implies (sets::setp x)
                  (iff (member-equal a x)
                       (sets::in a x)))
         :hints(("Goal" :in-theory (enable sets::primitive-reasoning)))))

(defthm sets::insert-under-set-equivp
  (implies (sets::setp x)
           (set-equivp (sets::insert a x)
                       (cons a (double-rewrite x))))
  :hints((set-reasoning)))

(defthm member-equal-of-remove-equal
  (iff (member-equal a (remove-equal b x))
       (and (member-equal a x)
            (not (equal a b)))))

(defthm sets::delete-under-set-equivp
  (implies (sets::setp x)
           (set-equivp (sets::delete a x)
                       (remove-equal a (double-rewrite x))))
  :hints((set-reasoning)))

(defthm sets::union-under-set-equivp
  (implies (and (sets::setp x)
                (sets::setp y))
           (set-equivp (sets::union x y)
                       (append (double-rewrite x)
                               (double-rewrite y))))
  :hints((set-reasoning)))

(defthm sets::intersect-under-set-equivp
  (implies (and (sets::setp x)
                (sets::setp y))
           (set-equivp (sets::intersect x y)
                       (intersection-equal (double-rewrite x)
                                           (double-rewrite y))))
  :hints((set-reasoning)))

(defthm sets::difference-under-set-equivp
  (implies (and (sets::setp x)
                (sets::setp y))
           (set-equivp (sets::difference x y)
                       (set-difference-equal (double-rewrite x)
                                             (double-rewrite y))))
  :hints((set-reasoning)))

(local (defthm sets::in-list-removal
         (equal (sets::in-list a x)
                (if (member-equal a x)
                    t
                  nil))))

(defthm sets::mergesort-under-set-equiv
  (set-equivp (sets::mergesort x)
              x)
  :hints((set-reasoning)))

(defthm set-equivp-append-nil
  (set-equivp (append x nil) x)
  :hints ((set-reasoning)))
