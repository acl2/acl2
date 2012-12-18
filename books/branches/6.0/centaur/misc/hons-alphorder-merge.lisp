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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "misc/total-order" :dir :system)
(include-book "equal-sets")


; Abuse of atom-listp on ordered sets

(defthm atom-of-head
  (implies (atom-listp x)
           (atom (sets::head x)))
  :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules)))))

(defthm atom-listp-of-tail
  (implies (atom-listp x)
           (atom-listp (sets::tail x)))
  :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules)))))

(defthm atom-listp-of-sfix
  (implies (atom-listp x)
           (atom-listp (sets::sfix x)))
  :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules)))))

(defthm atom-listp-of-insert
  (implies (and (atom a)
                (atom-listp x))
           (atom-listp (sets::insert a x)))
  :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules) sets::insert))))

(defthm atom-listp-of-union
  (implies (and (atom-listp x)
                (atom-listp y))
           (atom-listp (sets::union x y))))




(defsection hons-alphorder-merge
  :parents (alphorder)
  :short "Merge two already-@(see alphorder)ed lists of atoms."

  :long "<p>This is just a completely standard ordered-union operation for
@(see atom-listp)s, except that:</p>

<ul>
 <li>The resulting set is constructed with @(see hons), and</li>
 <li>We @(see memoize) non-recursive calls</li>
</ul>

<p>This is used in @(see aig-vars) and @(see 4v-sexpr-vars).</p>

<p>When the inputs happen to be ordered sets, the result is also an ordered set
and @('hons-alphorder-merge') is nothing more than @(see sets::union).</p>"

  (defun hons-alphorder-merge (a b)
    (declare (xargs :guard (and (atom-listp a)
                                (atom-listp b))
                    :guard-hints(("Goal" :in-theory (enable alphorder symbol-<)))
                    :measure (+ (len a) (len b))))
    (cond ((atom a) b)
          ((atom b) a)
          ((equal (car a) (car b))
           (hons-alphorder-merge (cdr a) b))
          ((fast-alphorder (car b) (car a))
           (hons (car b) (hons-alphorder-merge a (cdr b))))
          (t (hons (car a) (hons-alphorder-merge (cdr a) b)))))

  (memoize 'hons-alphorder-merge
           :condition '(or (consp a) (consp b))
           :inline nil)

  (defthm atom-listp-hons-alphorder-merge
    (implies (and (atom-listp a)
                  (atom-listp b))
             (atom-listp (hons-alphorder-merge a b)))
    :hints(("Goal" :in-theory (enable hons-alphorder-merge atom-listp))))

  (defthm member-equal-hons-alphorder-merge
    (iff (member-equal k (hons-alphorder-merge a b))
         (or (member-equal k a)
             (member-equal k b))))

  (defthm hons-set-equiv-hons-alphorder-merge-append
    (set-equivp (hons-alphorder-merge a b)
                (append a b))
    :hints ((set-reasoning)))

  (local (in-theory (disable sets::insert-under-set-equivp
                             sets::double-containment
                             default-car
                             default-cdr)))

  (local (defthm l0
           (implies (and (force (atom x))
                         (force (atom y)))
                    (equal (alphorder x y)
                           (or (<< x y)
                               (equal x y))))
           :hints(("Goal" :in-theory (enable << lexorder)))))

  (local (defthm l1
           (implies (atom-listp x)
                    (atom (car x)))))

  (local (defthm l2
           (implies (atom-listp x)
                    (atom-listp (cdr x)))))

  (local (defthm l3
           (implies (and (sets::setp x)
                         (sets::setp y)
                         (atom-listp x)
                         (atom-listp y))
                    (equal (car (hons-alphorder-merge x y))
                           (cond ((atom x) (car y))
                                 ((atom y) (car x))
                                 ((sets::<< (car y) (car x))
                                  (car y))
                                 (t
                                  (car x)))))
           :hints(("Goal"
                   :induct (hons-alphorder-merge x y)
                   :in-theory (e/d* (hons-alphorder-merge
                                     (:ruleset sets::primitive-rules))
                                    ;; just speed hints
                                    (sets::nonempty-means-set
                                     sets::setp-of-cons
                                     <<-trichotomy
                                     <<-asymmetric
                                     <<-transitive))))))


  (defthm setp-of-hons-alphorder-merge
    (implies (and (sets::setp x)
                  (sets::setp y)
                  (atom-listp x)
                  (atom-listp y))
             (sets::setp (hons-alphorder-merge x y)))
    :hints(("Goal"
            :induct (hons-alphorder-merge x y)
            :in-theory (e/d* (hons-alphorder-merge
                              (:ruleset sets::low-level-rules))
                             ;; just speed hints
                             (sets::nonempty-means-set
                              sets::setp-of-cons
                              <<-asymmetric
                              <<-transitive
                              )))))

  (defthm in-of-hons-alphorder-merge
    (implies (and (sets::setp x)
                  (sets::setp y)
                  (atom-listp x)
                  (atom-listp y))
             (equal (sets::in a (hons-alphorder-merge x y))
                    (or (sets::in a x)
                        (sets::in a y))))
    :hints(("Goal"
            :induct (hons-alphorder-merge x y)
            :in-theory (e/d* (hons-alphorder-merge
                              (:ruleset sets::low-level-rules))
                             ;; just speed hints
                             (sets::subset-in
                              sets::subsetp
                              sets::setp-of-cons
                              sets::nonempty-means-set
                              sets::in-tail
                              sets::head-minimal
                              sets::in-set
                              <<-transitive
                              <<-asymmetric)))))

  (defthm hons-alphorder-merge-is-union-for-sets-of-atoms
    (implies (and (sets::setp x)
                  (sets::setp y)
                  (atom-listp x)
                  (atom-listp y))
             (equal (hons-alphorder-merge x y)
                    (sets::union x y)))
    :hints(("Goal" :in-theory (enable sets::double-containment)))))







;; (defsection strict-alphorder-sortedp
;;   :parents (alphorder)
;;   :short "@(call strict-alphorder-sortedp) recognizes @(see atom-listp)s whose
;; members are in strict @(see alphorder)."

;;   :long "<p>BOZO this is just sets::setp for atom-lists...</p>"

;;   (defun strict-alphorder-sortedp (x)
;;     (declare (xargs :guard (atom-listp x)))
;;     (or (atom x)
;;         (atom (cdr x))
;;         (and (alphorder (car x) (cadr x))
;;              (not (equal (car x) (cadr x)))
;;              (strict-alphorder-sortedp (cdr x)))))

;;   (local (defthm nonmember-when-strict-alphorder-sorted
;;            (implies (and (strict-alphorder-sortedp x)
;;                          (atom-listp x)
;;                          (alphorder k (car x))
;;                          (not (equal k (car x)))
;;                          (atom k))
;;                     (not (member-equal k x)))))

;;   (local (defun cdr-two-ind (a b)
;;            (if (atom a)
;;                b
;;              (and (consp b)
;;                   (cdr-two-ind (cdr a) (cdr b))))))

;;   (local (defexample set-equivp-silly-example1
;;            :pattern (set-equivp a b)
;;            :templates ((car a))
;;            :instance-rulename set-equivp-instancing))

;;   (local (defexample set-equivp-silly-example2
;;            :pattern (set-equivp a b)
;;            :templates ((car b))
;;            :instance-rulename set-equivp-instancing))

;;   (local (defthm not-consp-car-atom-listp
;;            (implies (atom-listp x)
;;                     (not (consp (Car x))))))

;;   (local (defthm not-crossing-members-when-strict-alphorder-sorted
;;            (implies (and (atom-listp a)
;;                          (atom-listp b)
;;                          (strict-alphorder-sortedp a)
;;                          (strict-alphorder-sortedp b)
;;                          (member-equal (car a) (cdr b)))
;;                     (not (member-equal (car b) (cdr a))))
;;            :hints (("goal" :use ((:instance
;;                                   nonmember-when-strict-alphorder-sorted
;;                                   (k (car a)) (x (cdr b)))
;;                                  (:instance
;;                                   nonmember-when-strict-alphorder-sorted
;;                                   (k (car b)) (x (cdr a))))
;;                     :in-theory (disable nonmember-when-strict-alphorder-sorted)
;;                     :do-not-induct t))))

;;   (defthm equal-when-set-equiv-and-strict-alphorder-sorted
;;     (implies (and (set-equivp a b)
;;                   (strict-alphorder-sortedp a)
;;                   (strict-alphorder-sortedp b)
;;                   (atom-listp a)
;;                   (atom-listp b))
;;              (equal a b))
;;     :hints (("goal"
;;              :induct (cdr-two-ind a b)
;;              :in-theory (disable strict-alphorder-sortedp default-cdr)
;;              :expand ((strict-alphorder-sortedp a)
;;                       (strict-alphorder-sortedp b))
;;              :do-not-induct t)
;;             (witness :ruleset (set-equivp-silly-example1
;;                                set-equivp-silly-example2
;;                                set-equivp-witnessing
;;                                set-equivp-member-template)))
;;     :rule-classes nil
;;     :otf-flg t))


;; (defthm strict-alphorder-sortedp-hons-alphorder-merge
;;   (implies (and (strict-alphorder-sortedp a)
;;                 (strict-alphorder-sortedp b)
;;                 (atom-listp a)
;;                 (atom-listp b))
;;            (strict-alphorder-sortedp (hons-alphorder-merge a b)))
;;   :hints(("Goal" :in-theory
;;           (disable hons-alphorder-merge-is-union-for-sets-of-atoms
;;                    (:type-prescription alphorder)
;;                    (:type-prescription strict-alphorder-sortedp)
;;                    (:type-prescription hons-alphorder-merge)
;;                    (:type-prescription atom-listp)
;;                    default-car default-cdr
;;                    alphorder-transitive)
;;           :induct (hons-alphorder-merge a b))))
