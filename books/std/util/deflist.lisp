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
;
; Additional Copyright Notice.
;
; This file is adapted from the Milawa Theorem Prover, Copyright (C) 2005-2009
; Kookamara LLC, which is also available under an MIT/X11 style license.

(in-package "STD")
(include-book "deflist-base")
(include-book "std/osets/element-list" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(include-book "std/lists/sets" :dir :system)
(include-book "std/lists/list-fix" :dir :system)
(include-book "std/lists/take" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "std/lists/rev" :dir :system)
(local
 (progn
   (include-book "std/lists/nth" :dir :system)
   (include-book "std/lists/update-nth" :dir :system)
   (include-book "std/lists/butlast" :dir :system)
   (include-book "std/lists/nthcdr" :dir :system)
   (include-book "std/lists/append" :dir :system)
   (include-book "std/lists/last" :dir :system)
   (include-book "std/lists/rcons" :dir :system)
   (include-book "std/lists/remove" :dir :system)
   (include-book "std/lists/revappend" :dir :system)
   (include-book "defredundant")))


;; Harvest the listp rules from the above books by non-locally setting the
;; listp-rules table to its (local) value.  Redundantly define the theorems
;; referenced by the table.
(make-event
 (let ((tab (table-alist 'acl2::listp-rules (w state))))
   `(table acl2::listp-rules nil ',tab :clear)))

(make-event
 (defredundant-fn (strip-cars (table-alist 'acl2::listp-rules (w state))) nil state))


(defsection deflist-lemmas

  ;; Deflist does most of its work in a very minimal theory.  These are a few
  ;; lemmas that we enable so that it will work.

  (local (include-book "std/osets/under-set-equiv" :dir :system))
  (local (in-theory (acl2::enable* set::definitions set::expensive-rules)))

  (defthmd deflist-lemma-member-of-car
    (iff (member-equal (car x) x)
         (consp x)))

  (defthmd deflist-lemma-subsetp-of-set-difference-equal
    (subsetp-equal (set-difference-equal x y) x))

  (defthmd deflist-lemma-subsetp-of-intersection-equal
    (and (subsetp-equal (intersection-equal x y) x)
         (subsetp-equal (intersection-equal x y) y)))

  (defthmd deflist-lemma-subsetp-equal-of-duplicated-members
    (subsetp-equal (duplicated-members x) x)
    :hints(("Goal" :in-theory (enable acl2::duplicity)))
    :otf-flg t)

  (defthmd deflist-lemma-subsetp-of-nthcdr
    (subsetp-equal (nthcdr n x) x))

  (defthmd deflist-lemma-true-listp-of-nthcdr
    (equal (true-listp (nthcdr n x))
           (or (< (len x) (nfix n))
               (true-listp x)))
    :hints(("Goal" :induct (nthcdr n x))))

  (defthmd deflist-lemma-subsetp-of-last
    (subsetp-equal (last x) x))

  (defthmd deflist-lemma-true-listp-of-last
    (equal (true-listp (last x))
           (true-listp x)))

  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (defthmd c0
           (equal (< (+ a b) (+ a c))
                  (< b c))))

  (defthmd deflist-lemma-cancel-negative-constant
    (implies (syntaxp (and (quotep a)
                           (< (acl2::unquote a) 0)))
             (equal (< (+ a b) c)
                    (< b (+ (- a) c))))
    :hints(("Goal"
            :use ((:instance c0
                             (a (- a))
                             (b (+ a b))
                             (c c))))))

  (defthmd deflist-lemma-len-over-zero
    (equal (< 0 (len x))
           (consp x)))

  (defthmd deflist-lemma-nth-when-zp
    (implies (zp n)
             (equal (nth n x)
                    (car x))))

  (defthmd deflist-lemma-nth-when-atom
    (implies (atom x)
             (equal (nth n x)
                    nil)))

  (defthmd deflist-lemma-nth-of-cons
    (equal (nth n (cons a x))
           (if (zp n)
               a
             (nth (+ -1 n) x))))


  (local (defthm l0
           (implies (and (member a (take n x))
                         (<= (nfix n) (len x)))
                    (member a x))
           :hints(("Goal" :in-theory (enable acl2::take)))))

  (local (defthm l1
           (implies (<= (nfix n) (len x))
                    (subsetp-equal (take n x) x))
           :hints(("Goal" :in-theory (enable acl2::take)))))

  (defthmd deflist-lemma-subsetp-of-butlast
    (subsetp-equal (butlast x n) x))

  (defthmd deflist-lemma-true-listp-of-butlast
    (true-listp (butlast x n))
    :rule-classes :type-prescription)

  (defthmd deflist-lemma-sfix-when-not-setp
    (implies (not (setp x))
             (equal (sfix x) nil))
    :hints(("Goal" :in-theory (enable sfix empty))))

  (defthmd deflist-lemma-sfix-when-setp
    (implies (setp x)
             (equal (sfix x)
                    x))
    :hints(("Goal" :in-theory (enable sfix empty))))

  (defthmd deflist-lemma-subsetp-of-difference
    (subsetp-equal (difference x y) x))

  (local (defthm g1
           (implies (member a (sfix x))
                    (member a x))
           :hints(("Goal"
                   :do-not-induct t
                   :use ((:instance set::in-to-member
                                    (set::a a)
                                    (set::x (sfix x))))))))

  (defthmd deflist-lemma-subsetp-of-intersect
    (and (subsetp-equal (intersect x y) x)
         (subsetp-equal (intersect x y) y))
    :hints(("Goal" :do-not-induct t)))

  (defthmd deflist-lemma-true-listp-of-sfix
    (true-listp (sfix x))
    :rule-classes :type-prescription)

  (defthmd deflist-lemma-subsetp-of-union
    (and (subsetp-equal (sfix x) (union x y))
         (subsetp-equal (sfix y) (union x y))
         (subsetp-equal (union x y) (append (sfix x) (sfix y))))))


(deftheory deflist-support-lemmas
  '((:type-prescription intersection-equal)
    (:type-prescription set-difference-equal)
    (:type-prescription duplicated-members)
    (:t list-fix)
    (:type-prescription rev)
    (:type-prescription len)
    deflist-lemma-member-of-car
    deflist-lemma-subsetp-of-set-difference-equal
    deflist-lemma-subsetp-of-intersection-equal
    deflist-lemma-subsetp-equal-of-duplicated-members
    deflist-lemma-cancel-negative-constant
    deflist-lemma-len-over-zero
    deflist-lemma-nth-when-zp
    deflist-lemma-nth-when-atom
    deflist-lemma-nth-of-cons
    deflist-lemma-sfix-when-not-setp
    deflist-lemma-sfix-when-setp
    deflist-lemma-subsetp-of-nthcdr
    deflist-lemma-subsetp-of-last
    deflist-lemma-subsetp-of-butlast
    deflist-lemma-true-listp-of-last
    deflist-lemma-true-listp-of-butlast
    deflist-lemma-true-listp-of-nthcdr
    deflist-lemma-subsetp-of-difference
    deflist-lemma-subsetp-of-intersect
    deflist-lemma-true-listp-of-sfix
    deflist-lemma-subsetp-of-union
    car-cons
    cdr-cons
    car-cdr-elim
    zp
    len
    natp
    nth
    update-nth
    nfix
    acl2::default-+-2
    acl2::default-<-1
    acl2::default-unary-minus
    acl2::unicity-of-0
    acl2::take
    acl2::list-fix-when-not-consp
    acl2::list-fix-when-true-listp
    acl2::list-fix-of-cons
    set::sets-are-true-lists
    set::mergesort-set
    set::union-set
    set::intersect-set
    set::difference-set
    acl2::set-equiv-implies-equal-subsetp-1
    acl2::set-equiv-implies-equal-subsetp-2
    acl2::subsetp-refl
    acl2::list-fix-under-list-equiv
    set::mergesort-under-set-equiv
    acl2::binary-append-without-guard))
