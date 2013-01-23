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
(include-book "finite-set-theory/osets/sets" :dir :system)
(include-book "std/lists/equiv" :dir :system)
(include-book "mfc-utils")
(include-book "witness-cp")

(local (defthm equal-of-booleans-to-iff
         (implies (and (booleanp a) (booleanp b))
                  (equal (equal a b) (iff a b)))))


(defsection member-equal

  (defthm member-equal-when-atom
    (implies (atom x)
             (not (member-equal a x))))

  (defthm member-equal-of-cons
    (equal (member-equal a (cons b x))
           (if (equal a b)
               (cons b x)
             (member-equal a x))))

  (defthm member-equal-of-car
    (equal (member-equal (car x) x)
           (if (consp x)
               x
             nil)))

  ;; We don't need member-equal-of-append, it's already in witness-cp

  (local (defthm l0
           (implies (member-equal a y)
                    (not (member-equal a (set-difference-equal x y))))))

  (defthm member-equal-of-set-difference-equal
    (iff (member-equal a (set-difference-equal x y))
         (and (member-equal a x)
              (not (member-equal a y))))
    :hints(("Goal" :induct (len x))))

  (local (defthm l1
           (implies (not (member-equal a y))
                    (not (member-equal a (intersection-equal x y))))))

  (defthm member-equal-of-intersection-equal
    (iff (member-equal a (intersection-equal x y))
         (and (member-equal a x)
              (member-equal a y)))
    :hints(("Goal" :induct (len x))))

  (local (defthm l2
           (not (member-equal a (remove-equal a x)))))

  (defthm member-equal-of-remove-equal
    (iff (member-equal a (remove-equal b x))
         (and (member-equal a x)
              (not (equal a b))))
    :hints(("Goal" :induct (len x))))

  (defthm acl2-count-when-member-equal
    (implies (member-equal a x)
             (< (acl2-count a) (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable member-equal acl2-count))))

  (defthm member-equal-self
    (not (member-equal x x))
    :hints(("Goal"
            :in-theory (disable acl2-count-when-member-equal)
            :use ((:instance acl2-count-when-member-equal (a x)))))))




(defthm subsetp-equal-when-atom
    (implies (atom x)
             (subsetp-equal x y)))

(defthm subsetp-equal-nil
    (subsetp-equal nil x))

(defthm subsetp-equal-of-cons
    (equal (subsetp-equal (cons a x) y)
           (if (member-equal a y)
               (subsetp-equal x y)
             nil)))

(defthmd subsetp-equal-member
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




(defthm subsetp-equal-witness-rw
  (implies (rewriting-positive-literal `(subsetp-equal ,x ,y))
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
  (implies (rewriting-negative-literal `(intersectp-equal ,x ,y))
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



(defthm subsetp-equal-implies-subsetp-equal-cdr
  (implies (subsetp-equal x y)
           (subsetp-equal (cdr x) y)))

(defthm subsetp-equal-of-cdr
  (subsetp-equal (cdr x) x))



(defun set-equivp (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (and (subsetp-equal x y)
       (subsetp-equal y x)))

(local (in-theory (enable subsetp-equal-member)))

(defthm set-equivp-implies-iff
  (implies (set-equivp x y)
           (equal (iff (member-equal a x)
                       (member-equal a y))
                  t)))

(encapsulate
  ()
  (local (defthm set-equivp-refl
           ;; Automatic after defequiv
           (set-equivp x x)))

  (defthm set-equivp-asym
    ;; NOT automatic after defequiv, so make it non-local
    (equal (set-equivp x y)
           (set-equivp y x)))

  (local (defthm set-equivp-trans
           ;; Automatic after defequiv
           (implies (and (set-equivp x y)
                         (set-equivp y z))
                    (set-equivp x z))))

  (defequiv set-equivp))


(defrefinement list-equiv set-equivp)


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
  (implies (rewriting-positive-literal `(set-equivp ,x ,y))
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

;; BOZO maybe change the variable names from all Ks to appropriate short names,
;; i.e. ssew for subsetp-equal-witness?
(defquantexpr subsetp-equal
  :predicate (subsetp-equal x y)
  :quantifier :forall
  :witnesses ((k (subsetp-equal-witness x y)))
  :expr (implies (member-equal k x)
                 (member-equal k y))
  :witness-hints ('(:in-theory '(subsetp-equal-witness-correct)))
  :instance-hints ('(:in-theory '(subsetp-equal-member))))

(defquantexpr intersectp-equal
  :predicate (intersectp-equal x y)
  :quantifier :exists
  :witnesses ((k (intersectp-equal-witness x y)))
  :expr (and (member-equal k x)
             (member-equal k y))
  :witness-hints ('(:in-theory '(intersectp-equal-witness-correct)))
  :instance-hints ('(:in-theory '(intersectp-equal-member))))

(defquantexpr set-equivp
  :predicate (set-equivp x y)
  :quantifier :forall
  :witnesses ((k (set-unequal-witness x y)))
  :expr (iff (member-equal k x)
             (member-equal k y))
  :witness-hints ('(:in-theory '(set-unequal-witness-correct)))
  :instance-hints ('(:in-theory '(set-equivp-implies-iff-member-equal-2))))

(defquantexpr set-consp
  :predicate (consp x)
  :quantifier :exists
  :witnesses ((k (car x)))
  :expr (member-equal k x)
  :generalize nil
  :witness-hints ('(:in-theory nil
                    :expand ((:with member-equal
                              (:free (k) (member-equal k x))))))
  :instance-hints ('(:in-theory nil
                    :expand ((:with member-equal
                              (:free (k) (member-equal k x)))))))


(defexample set-reasoning-member-equal-template
  :pattern (member-equal k y)
  :templates (k)
  :instance-rules
  (subsetp-equal-instancing
   intersectp-equal-instancing
   set-equivp-instancing
   set-consp-instancing))

(defexample set-reasoning-no-consp-member-equal-template
  :pattern (member-equal k y)
  :templates (k)
  :instance-rules
  (subsetp-equal-instancing
   intersectp-equal-instancing
   set-equivp-instancing))

(def-witness-ruleset set-reasoning-rules
  '(subsetp-equal-witnessing
    intersectp-equal-witnessing
    set-equivp-witnessing
    set-consp-witnessing
    subsetp-equal-instancing
    set-equivp-instancing
    intersectp-equal-instancing
    set-consp-instancing
    set-reasoning-member-equal-template))

(def-witness-ruleset set-reasoning-no-consp
  '(subsetp-equal-witnessing
    intersectp-equal-witnessing
    set-equivp-witnessing
    subsetp-equal-instancing
    set-equivp-instancing
    intersectp-equal-instancing
    intersectp-equal-member-template
    subsetp-equal-member-template
    set-equivp-member-template
    set-reasoning-no-consp-member-equal-template))

(def-witness-ruleset set-reasoning-no-consp-manual-examples
  '(subsetp-equal-witnessing
    intersectp-equal-witnessing
    set-equivp-witnessing
    subsetp-equal-instancing
    set-equivp-instancing
    intersectp-equal-instancing
    intersectp-equal-member-template
    subsetp-equal-member-template
    set-equivp-member-template))

(def-witness-ruleset set-reasoning-manual-examples
  '(subsetp-equal-witnessing
    intersectp-equal-witnessing
    set-equivp-witnessing
    set-consp-witnessing
    subsetp-equal-instancing
    set-equivp-instancing
    intersectp-equal-instancing
    set-consp-instancing))


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





;; BOZO talk to sol about whether these should become defwitness nonsense

(local (defthm promote-member-equal-to-in
         (implies (sets::setp x)
                  (iff (member-equal a x)
                       (sets::in a x)))
         :hints(("Goal" :in-theory (enable sets::in-to-member)))))

(defthm sets::insert-under-set-equivp
  (implies (sets::setp x)
           (set-equivp (sets::insert a x)
                       (cons a (double-rewrite x))))
  :hints((set-reasoning)))


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

(defthm sets::mergesort-under-set-equiv
  (set-equivp (sets::mergesort x)
              x)
  :hints((set-reasoning)))

(defthm set-equivp-append-nil
  (set-equivp (append x nil) x)
  :hints ((set-reasoning)))


; Some additional rules that are useful for canoncializing APPEND nests under SET-EQUIV

(defthm commutativity-of-append-under-set-equivp
  (set-equivp (append x y)
              (append y x))
  :hints((set-reasoning)))

(defthm commutativity-2-of-append-under-set-equivp
  (set-equivp (append x (append y z))
              (append y (append x z)))
  :hints((set-reasoning)))

(defthm cancel-append-self-under-set-equivp
  (set-equivp (append x x)
              x)
  :hints((set-reasoning)))

(defthm cancel-append-self-2-under-set-equivp
  (set-equivp (append x x y)
              (append x y))
  :hints((set-reasoning)))

(encapsulate
  ()
  (local (defthm l0
           (implies (set-equivp x (append x y))
                    (subsetp-equal y x))))

  (local (defthm l1
           (implies (subsetp-equal y x)
                    (set-equivp (append x y) x))
           :hints((set-reasoning))))

  (defthm set-equivp-with-append-other-right
    (equal (set-equivp x (append x y))
           (subsetp-equal y x))
    :hints(("Goal"
            :use ((:instance l0)
                  (:instance l1)))))

  (defthm set-equivp-with-append-other-left
    (equal (set-equivp x (append y x))
           (subsetp-equal y x))))

(defthm append-singleton-under-set-equivp
  (set-equivp (append x (list a))
              (cons a x))
  :hints((set-reasoning)))


(defsection revappend

  (local (defthm l0
           (iff (member-equal x (revappend a b))
                (or (member-equal x a)
                    (member-equal x b)))))

  (defcong set-equivp set-equivp (revappend x y) 1
    :hints((set-reasoning)))

  (defcong set-equivp set-equivp (revappend x y) 2
    :hints((set-reasoning)))

  (defthm revappend-under-set-equivp
    (set-equivp (revappend x y)
                (append x y))
    :hints((set-reasoning))))


(defthm reverse-under-set-equivp
  (implies (true-listp x)
           (set-equivp (reverse x)
                       x))
  :hints((set-reasoning)))


(defsection remove-duplicates-equal

  (local (defthm l0
           (iff (member-equal a (remove-duplicates-equal x))
                (member-equal a x))))

  (defthm remove-duplicates-equal-under-set-equivp
    (set-equivp (remove-duplicates-equal x)
                x)
    :hints((set-reasoning)))

  (defcong set-equivp set-equivp (remove-duplicates-equal x) 1
    :hints((set-reasoning))))



(defthm set-equivp-of-cons-self
   (equal (set-equivp x (cons a x))
          (if (member-equal a x)
              t
            nil))
   :hints((set-reasoning)))

(defcong set-equivp set-equivp (cons a x) 2
  :hints((set-reasoning)))


(defcong set-equivp set-equivp (remove-equal k a) 2
  :hints ((set-reasoning)))
