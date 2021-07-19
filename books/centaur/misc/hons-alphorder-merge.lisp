; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "misc/total-order" :dir :system)
(include-book "equal-sets")
(include-book "std/typed-lists/atom-listp" :dir :system)

(local (in-theory (acl2::enable* set::definitions set::expensive-rules)))

; Abuse of atom-listp on ordered sets

(defthm atom-of-head
  (implies (atom-listp x)
           (atom (set::head x)))
  :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules)))))

(defthm atom-listp-of-tail
  (implies (atom-listp x)
           (atom-listp (set::tail x)))
  :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules)))))

;; (defthm atom-listp-of-sfix
;;   (implies (atom-listp (double-rewrite x))
;;            (equal (atom-listp (set::sfix x))
;;                   t))
;;   :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules)))))

;; (defthm atom-listp-of-insert
;;   (implies (and (atom a)
;;                 (atom-listp x))
;;            (atom-listp (set::insert a x)))
;;   :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules) set::insert))))

;; (defthm atom-listp-of-union
;;   (equal (atom-listp (set::union x y))
;;          (and (atom-listp (set::sfix x))
;;               (atom-listp (set::sfix y)))))




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
and @('hons-alphorder-merge') is nothing more than @(see set::union).</p>"

  (defun hons-alphorder-merge (a b)
    (declare (xargs :guard (and (atom-listp a)
                                (atom-listp b))
                    :guard-hints(("Goal" :in-theory (enable alphorder symbol<)))
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
           :recursive nil)

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
    (set-equiv (hons-alphorder-merge a b)
                (append a b))
    :hints ((set-reasoning)))

  (local (in-theory (disable set::insert-under-set-equiv
                             set::double-containment
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
           (implies (and (set::setp x)
                         (set::setp y)
                         (atom-listp x)
                         (atom-listp y))
                    (equal (car (hons-alphorder-merge x y))
                           (cond ((atom x) (car y))
                                 ((atom y) (car x))
                                 ((set::<< (car y) (car x))
                                  (car y))
                                 (t
                                  (car x)))))
           :hints(("Goal"
                   :induct (hons-alphorder-merge x y)
                   :in-theory (e/d* (hons-alphorder-merge
                                     (:ruleset set::primitive-rules))
                                    ;; just speed hints
                                    (set::nonempty-means-set
                                     set::setp-of-cons
                                     <<-trichotomy
                                     <<-asymmetric
                                     <<-transitive))))))


  (defthm setp-of-hons-alphorder-merge
    (implies (and (set::setp x)
                  (set::setp y)
                  (atom-listp x)
                  (atom-listp y))
             (set::setp (hons-alphorder-merge x y)))
    :hints(("Goal"
            :induct (hons-alphorder-merge x y)
            :in-theory (e/d* (hons-alphorder-merge
                              (:ruleset set::low-level-rules))
                             ;; just speed hints
                             (set::nonempty-means-set
                              set::setp-of-cons
                              <<-asymmetric
                              <<-transitive
                              )))))

  (defthm in-of-hons-alphorder-merge
    (implies (and (set::setp x)
                  (set::setp y)
                  (atom-listp x)
                  (atom-listp y))
             (equal (set::in a (hons-alphorder-merge x y))
                    (or (set::in a x)
                        (set::in a y))))
    :hints(("Goal"
            :induct (hons-alphorder-merge x y)
            :in-theory (e/d* (hons-alphorder-merge
                              (:ruleset set::low-level-rules))
                             ;; just speed hints
                             (set::subset-in
                              set::subsetp
                              set::setp-of-cons
                              set::nonempty-means-set
                              set::in-tail
                              set::head-minimal
                              set::in-set
                              <<-transitive
                              <<-asymmetric)))))

  (defthm hons-alphorder-merge-is-union-for-sets-of-atoms
    (implies (and (set::setp x)
                  (set::setp y)
                  (atom-listp x)
                  (atom-listp y))
             (equal (hons-alphorder-merge x y)
                    (set::union x y)))
    :hints(("Goal" :in-theory (enable set::double-containment)))))







;; (defsection strict-alphorder-sortedp
;;   :parents (alphorder)
;;   :short "@(call strict-alphorder-sortedp) recognizes @(see atom-listp)s whose
;; members are in strict @(see alphorder)."

;;   :long "<p>BOZO this is just set::setp for atom-lists...</p>"

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

;;   (local (defexample set-equiv-silly-example1
;;            :pattern (set-equiv a b)
;;            :templates ((car a))
;;            :instance-rulename set-equiv-instancing))

;;   (local (defexample set-equiv-silly-example2
;;            :pattern (set-equiv a b)
;;            :templates ((car b))
;;            :instance-rulename set-equiv-instancing))

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
;;     (implies (and (set-equiv a b)
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
;;             (witness :ruleset (set-equiv-silly-example1
;;                                set-equiv-silly-example2
;;                                set-equiv-witnessing
;;                                set-equiv-member-template)))
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
