; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "deflist")
(include-book "cons-listp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; (member-of-nonep a xs)
;;
;; a is interpreted as an element and xs is interpreted as a chain.  We return
;; true if a is not a member of any x in xs.

(deflist member-of-nonep (e x)
  (memberp e x)
  :negatedp t
  :elementp-of-nil nil)



;; (defund member-of-nonep (a xs)
;;   (if (consp xs)
;;       (and (not (memberp a (car xs)))
;;            (member-of-nonep a (cdr xs)))
;;     t))

;; (defthm member-of-nonep-when-not-consp
;;   (implies (not (consp xs))
;;            (equal (member-of-nonep a xs)
;;                   t))
;;   :hints(("Goal" :in-theory (enable member-of-nonep))))

;; (defthm member-of-nonep-of-cons
;;   (equal (member-of-nonep a (cons x xs))
;;          (and (not (memberp a x))
;;               (member-of-nonep a xs)))
;;   :hints(("Goal" :in-theory (enable member-of-nonep))))

;; (defthm booleanp-of-member-of-nonep
;;   (equal (booleanp (member-of-nonep a xs))
;;          t)
;;   :hints(("Goal" :induct (cdr-induction xs))))

;; (defthm member-of-nonep-of-list-fix
;;   (equal (member-of-nonep a (list-fix xs))
;;          (member-of-nonep a xs))
;;   :hints(("Goal" :induct (cdr-induction xs))))

;; (defthm member-of-nonep-of-app
;;   (equal (member-of-nonep a (app xs ys))
;;          (and (member-of-nonep a xs)
;;               (member-of-nonep a ys)))
;;   :hints(("Goal" :induct (cdr-induction xs))))

;; (defthm member-of-nonep-of-rev
;;   (equal (member-of-nonep a (rev xs))
;;          (member-of-nonep a xs))
;;   :hints(("Goal" :induct (cdr-induction xs))))

;; (defthm member-of-nonep-of-remove-all-when-member-of-nonep
;;   (implies (member-of-nonep a xs)
;;            (equal (member-of-nonep a (remove-all x xs))
;;                   t))
;;   :hints(("Goal" :induct (cdr-induction xs))))

;; (defthm memberp-when-memberp-of-member-of-nonep
;;   (implies (and (member-of-nonep a xs)
;;                 (memberp x xs))
;;            (equal (memberp a x)
;;                   nil))
;;   :hints(("Goal" :induct (cdr-induction xs))))

;; (defthm memberp-when-memberp-of-member-of-nonep-alt
;;   (implies (and (memberp x xs)
;;                 (member-of-nonep a xs))
;;            (equal (memberp a x)
;;                   nil)))

;; (defthm member-of-nonep-when-subsetp-of-member-of-nonep
;;   (implies (and (member-of-nonep a ys)
;;                 (subsetp xs ys))
;;            (equal (member-of-nonep a xs)
;;                   t))
;;   :hints(("Goal" :induct (cdr-induction xs))))

;; (defthm member-of-nonep-when-subsetp-of-member-of-nonep-two
;;   (implies (and (subsetp xs ys)
;;                 (member-of-nonep a ys))
;;            (equal (member-of-nonep a xs)
;;                   t)))

;; (thm (implies (member-of-nonep a (remove-all x xs))
;;                (member-of-nonep a (remove-all x (remove-all y xs)))))
;;
;; (thm (implies (member-of-nonep a (remove-all x xs))
;;               (member-of-nonep a (remove-all y (remove-all x xs)))))






;; (lists-lookup a xs)
;;
;; a is interpreted as an element and xs as a list of lists.  We return the
;; first x in xs which includes a as a member, or nil if no such list exists.

(defund lists-lookup (a xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (memberp a (car xs))
          (car xs)
        (lists-lookup a (cdr xs)))
    nil))

(defthm lists-lookup-when-not-consp
  (implies (not (consp xs))
           (equal (lists-lookup a xs)
                  nil))
  :hints(("Goal" :in-theory (enable lists-lookup))))

(defthm lists-lookup-of-cons
  (equal (lists-lookup a (cons x xs))
         (if (memberp a x)
             x
           (lists-lookup a xs)))
  :hints(("Goal" :in-theory (enable lists-lookup))))

(defthm lists-lookup-of-list-fix
  (equal (lists-lookup a (list-fix xs))
         (lists-lookup a xs))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm lists-lookup-of-app
  (equal (lists-lookup a (app xs ys))
         (if (lists-lookup a xs)
             (lists-lookup a xs)
           (lists-lookup a ys)))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm consp-of-lists-lookup
  (equal (consp (lists-lookup a xs))
         (not (member-of-nonep a xs)))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm lists-lookup-under-iff
  (iff (lists-lookup a xs)
       (not (member-of-nonep a xs)))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm lists-lookup-of-rev-under-iff
  (iff (lists-lookup a (rev xs))
       (not (member-of-nonep a xs)))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm memberp-of-element-in-lists-lookup
  (implies (not (member-of-nonep a xs))
           (equal (memberp a (lists-lookup a xs))
                  t))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm memberp-of-in-lists-lookup-in-lists
  (implies (not (member-of-nonep a xs))
           (equal (memberp (lists-lookup a xs) xs)
                  t))
  :hints(("Goal" :induct (cdr-induction xs))))





;; (none-consp x)
;;
;; x is interpreted as a list.
;;
;; We return true if all of x's members are not conses.

(deflist none-consp (x)
  (consp x)
  :negatedp t
  :elementp-of-nil nil)

;; (defund none-consp (x)
;;   (declare (xargs :guard t))
;;   (if (consp x)
;;       (and (not (consp (car x)))
;;            (none-consp (cdr x)))
;;     t))

;; (defthm none-consp-when-not-consp
;;   (implies (not (consp x))
;;            (equal (none-consp x)
;;                   t))
;;   :hints(("Goal" :in-theory (enable none-consp))))

;; (defthm none-consp-of-cons
;;   (equal (none-consp (cons a x))
;;          (and (not (consp a))
;;               (none-consp x)))
;;   :hints(("Goal" :in-theory (enable none-consp))))

;; (defthm none-consp-of-list-fix
;;   (equal (none-consp (list-fix x))
;;          (none-consp x))
;;   :hints(("Goal" :induct (cdr-induction x))))

;; (defthm booleanp-of-none-consp
;;   (equal (booleanp (none-consp x))
;;          t)
;;   :hints(("Goal" :induct (cdr-induction x))))

;; (defthm none-consp-of-app
;;   (equal (none-consp (app x y))
;;          (and (none-consp x)
;;               (none-consp y)))
;;   :hints(("Goal" :induct (cdr-induction x))))

;; (defthm none-consp-of-rev
;;   (equal (none-consp (rev x))
;;          (none-consp x))
;;   :hints(("Goal" :induct (cdr-induction x))))

;; (defthm none-consp-of-cdr-when-none-consp
;;   (implies (none-consp x)
;;            (equal (none-consp (cdr x))
;;                   t)))

;; (defthm consp-of-car-when-none-consp
;;   (implies (none-consp x)
;;            (equal (consp (car x))
;;                   nil)))






;; (disjoint-from-allp x ys)
;;
;; x is interpreted as a list, and ys is interpreted as a chain.  We return
;; true if x is disjoint from every list in ys.  We can think about this
;; function in two ways:
;;
;;   - We are checking that each y in ys is disjoint from x.
;;   - We are checking that each a in x is a member of none of the ys.
;;
;; This is a little odd and it leads us to different styles of rules based on
;; which argument is being manipulated.  I've arbitrarily implemented the
;; function using the first approach.

(deflist disjoint-from-allp (e x)
  (disjointp e x)
  :elementp-of-nil t)

;; (defund disjoint-from-allp (x ys)
;;   (declare (xargs :guard t))
;;   (if (consp ys)
;;       (and (disjointp x (car ys))
;;            (disjoint-from-allp x (cdr ys)))
;;     t))

;; (defthm disjoint-from-allp-when-not-consp-two
;;   (implies (not (consp x))
;;            (equal (disjoint-from-allp e x)
;;                   t))
;;   :hints(("Goal" :in-theory (enable disjoint-from-allp))))

;; (defthm disjoint-from-allp-of-cons-two
;;   (equal (disjoint-from-allp x (cons y ys))
;;          (and (disjointp x y)
;;               (disjoint-from-allp x ys)))
;;   :hints(("Goal" :in-theory (enable disjoint-from-allp))))

;; (defthm booleanp-of-disjoint-from-allp
;;   (equal (booleanp (disjoint-from-allp e x))
;;          t)
;;   :hints(("Goal" :induct (cdr-induction x))))

(defthm disjoint-from-allp-when-not-consp-left
  (implies (not (consp e))
           (equal (disjoint-from-allp e x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjoint-from-allp-of-cons-left
  (equal (disjoint-from-allp (cons a e) x)
         (and (member-of-nonep a x)
              (disjoint-from-allp e x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjoint-from-allp-of-cdr-left
  (implies (disjoint-from-allp e x)
           (disjoint-from-allp (cdr e) x)))

(defthm member-of-nonep-when-memberp-of-disjoint-from-allp
  (implies (and (disjoint-from-allp e x)
                (memberp a e))
           (equal (member-of-nonep a x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm member-of-nonep-when-memberp-of-disjoint-from-allp-alt
  (implies (and (memberp a e)
                (disjoint-from-allp e x))
           (equal (member-of-nonep a x)
                  t)))

;; BOZO rename vars
(defthm disjointp-when-memberp-of-disjoint-from-allp-one
  (implies (and (disjoint-from-allp x ys)
                (memberp y ys))
           (equal (disjointp x y)
                  t))
  :hints(("Goal" :induct (cdr-induction ys))))

;; BOZO rename vars
(defthm disjointp-when-memberp-of-disjoint-from-allp-two
  (implies (and (memberp y ys)
                (disjoint-from-allp x ys))
           (equal (disjointp x y)
                  t))
  :hints(("Goal" :induct (cdr-induction ys))))

;; BOZO rename vars
(defthm disjointp-when-memberp-of-disjoint-from-allp-three
  (implies (and (disjoint-from-allp x ys)
                (memberp y ys))
           (equal (disjointp y x)
                  t)))

;; BOZO rename vars
(defthm disjointp-when-memberp-of-disjoint-from-allp-four
  (implies (and (memberp y ys)
                (disjoint-from-allp x ys))
           (equal (disjointp y x)
                  t)))


;; disjoint-from-allp-when-subsetp-of-disjoint-from-allp-[one,...]
;;
;; If we know that (disjoint-from-allp z zs), then
;;
;;   (subsetp x z) -> (disjoint-from-allp x zs)
;;   (subsetp ys zs) -> (disjoint-from-allp x ys)

;; BOZO rename vars
(defthm disjoint-from-allp-when-subsetp-of-disjoint-from-allp-one
  (implies (and (disjoint-from-allp z zs)
                (subsetp x z))
           (equal (disjoint-from-allp x zs)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

;; BOZO rename vars
(defthm disjoint-from-allp-when-subsetp-of-disjoint-from-allp-two
  (implies (and (subsetp x z)
                (disjoint-from-allp z zs))
           (equal (disjoint-from-allp x zs)
                  t)))

;; BOZO rename vars
(defthm disjoint-from-allp-when-subsetp-of-disjoint-from-allp-three
  (implies (and (disjoint-from-allp z zs)
                (subsetp ys zs))
           (equal (disjoint-from-allp z ys)
                  t))
  :hints(("Goal" :induct (cdr-induction ys))))

;; BOZO rename vars
(defthm disjoint-from-allp-when-subsetp-of-disjoint-from-allp-four
  (implies (and (subsetp ys zs)
                (disjoint-from-allp z zs))
           (equal (disjoint-from-allp z ys)
                  t)))

;; BOZO rename vars  (im not going to keep writing this, through teh file)
(defthm disjoint-from-allp-when-memberp
  (implies (memberp x ys)
           (equal (disjoint-from-allp x ys)
                  (not (consp x))))
  :hints(("Goal" :induct (cdr-induction ys))))


(defthm disjoint-from-allp-of-list-fix-left
  (equal (disjoint-from-allp (list-fix x) ys)
         (disjoint-from-allp x ys)))

;; (defthm disjoint-from-allp-of-list-fix
;;   (equal (disjoint-from-allp x (list-fix ys))
;;          (disjoint-from-allp x ys)))


(defthm disjoint-from-allp-of-app-left
  (equal (disjoint-from-allp (app x y) zs)
         (and (disjoint-from-allp x zs)
              (disjoint-from-allp y zs)))
  :hints(("Goal" :induct (cdr-induction x))))

;; (defthm disjoint-from-allp-of-app
;;   (equal (disjoint-from-allp x (app ys zs))
;;          (and (disjoint-from-allp x ys)
;;               (disjoint-from-allp x zs)))
;;   :hints(("Goal" :induct (cdr-induction ys))))


(defthm disjoint-from-allp-of-rev-left
  (equal (disjoint-from-allp (rev x) ys)
         (disjoint-from-allp x ys))
  :hints(("Goal" :induct (cdr-induction x))))

;; (defthm disjoint-from-allp-of-rev
;;   (equal (disjoint-from-allp e (rev x))
;;          (disjoint-from-allp e x))
;;   :hints(("Goal" :induct (cdr-induction x))))

(defthm remove-all-when-disjoint-from-allp-and-cons-listp
  (implies (and (disjoint-from-allp a x)
                (cons-listp x))
           (equal (remove-all a x)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))


;; These test theorems should prove easily.
;;
;; (thm (implies (disjoint-from-allp x ys) (disjoint-from-allp (remove-all a x) ys)))
;; (thm (implies (disjoint-from-allp x ys) (disjoint-from-allp x (remove-all b ys))))




;; (all-disjoint-from-allp xs ys)
;;
;; xs and ys are interpreted as chains.  We return true if every x in xs is
;; disjoint from every y in ys.

;; BOZO migrate to deflist

(defund all-disjoint-from-allp (xs ys)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (disjoint-from-allp (car xs) ys)
           (all-disjoint-from-allp (cdr xs) ys))
    t))

(defthm all-disjoint-from-allp-when-not-consp-one
  (implies (not (consp xs))
           (equal (all-disjoint-from-allp xs ys)
                  t))
  :hints(("Goal" :in-theory (enable all-disjoint-from-allp))))

(defthm all-disjoint-from-allp-of-cons-one
  (equal (all-disjoint-from-allp (cons x xs) ys)
         (and (disjoint-from-allp x ys)
              (all-disjoint-from-allp xs ys)))
  :hints(("Goal" :in-theory (enable all-disjoint-from-allp))))

(defthm all-disjoint-from-allp-when-not-consp-two
  (implies (not (consp ys))
           (equal (all-disjoint-from-allp xs ys)
                  t))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm all-disjoint-from-allp-of-cons-two
  (equal (all-disjoint-from-allp xs (cons y ys))
         (and (disjoint-from-allp y xs)
              (all-disjoint-from-allp xs ys)))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm booleanp-of-all-disjoint-from-allp
  (equal (booleanp (all-disjoint-from-allp xs ys))
         t)
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm symmetry-of-all-disjoint-from-allp
  (equal (all-disjoint-from-allp xs ys)
         (all-disjoint-from-allp ys xs))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm all-disjoint-from-allp-of-list-fix-two
  (equal (all-disjoint-from-allp xs (list-fix ys))
         (all-disjoint-from-allp xs ys))
  :hints(("Goal" :induct (cdr-induction ys))))

(defthm all-disjoint-from-allp-of-list-fix-one
  (equal (all-disjoint-from-allp (list-fix xs) ys)
         (all-disjoint-from-allp xs ys)))

(defthm all-disjoint-from-allp-of-app-two
  (equal (all-disjoint-from-allp xs (app ys zs))
         (and (all-disjoint-from-allp xs ys)
              (all-disjoint-from-allp xs zs)))
  :hints(("Goal" :induct (cdr-induction ys))))

(defthm all-disjoint-from-allp-of-app-one
  (equal (all-disjoint-from-allp (app xs ys) zs)
         (and (all-disjoint-from-allp xs zs)
              (all-disjoint-from-allp ys zs))))

(defthm all-disjoint-from-allp-of-rev-two
  (equal (all-disjoint-from-allp xs (rev ys))
         (all-disjoint-from-allp xs ys))
  :hints(("Goal" :induct (cdr-induction ys))))

(defthm all-disjoint-from-allp-of-rev-one
  (equal (all-disjoint-from-allp (rev xs) ys)
         (all-disjoint-from-allp xs ys)))


(defthm all-disjoint-from-allp-when-subsetp-of-other-one
  (implies (subsetp xs ys)
           (equal (all-disjoint-from-allp xs ys)
                  (none-consp xs)))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm all-disjoint-from-allp-when-subsetp-of-other-two
  (implies (subsetp xs ys)
           (equal (all-disjoint-from-allp ys xs)
                  (none-consp xs))))

(defthm disjoint-from-allp-when-memberp-of-all-disjoint-from-allp-one
  (implies (and (all-disjoint-from-allp xs ys)
                (memberp x xs))
           (equal (disjoint-from-allp x ys)
                  t))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm disjoint-from-allp-when-memberp-of-all-disjoint-from-allp-two
  (implies (and (all-disjoint-from-allp xs ys)
                (memberp y ys))
           (equal (disjoint-from-allp y xs)
                  t))
  :hints(("Goal" :induct (cdr-induction ys))))

(defthm disjointp-when-members-of-all-disjoint-from-allp
  (implies (and (all-disjoint-from-allp xs ys)
                (memberp x xs)
                (memberp y ys))
           (equal (disjointp x y)
                  t))
  :hints(("Goal" :induct (cdr-induction xs))))



;; If (all-disjoint-from-allp ys zs), then:
;;
;;   (subsetp xs ys) -> (all-disjoint-from-allp xs zs) and
;;                      (all-disjoint-from-allp zs xs)
;;
;;   (subsetp xs zs) -> (all-disjoint-from-allp ys xs) and
;;                      (all-disjoint-from-allp xs ys)

(defthm all-disjoint-from-allp-when-subsetp-of-all-disjoint-one
  (implies (and (all-disjoint-from-allp ys zs)
                (subsetp xs ys))
           (equal (all-disjoint-from-allp xs zs)
                  t))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm all-disjoint-from-allp-when-subsetp-of-all-disjoint-two
  (implies (and (all-disjoint-from-allp ys zs)
                (subsetp xs ys))
           (equal (all-disjoint-from-allp zs xs)
                  t)))

(defthm all-disjoint-from-allp-when-subsetp-of-all-disjoint-three
  (implies (and (all-disjoint-from-allp ys zs)
                (subsetp xs zs))
           (equal (all-disjoint-from-allp ys zs)
                  t))
  :hints(("Goal" :induct (cdr-induction ys))))

(defthm all-disjoint-from-allp-when-subsetp-of-all-disjoint-four
  (implies (and (all-disjoint-from-allp ys zs)
                (subsetp xs zs))
           (equal (all-disjoint-from-allp zs ys)
                  t)))








;; (mutually-disjointp xs)
;;
;; xs is interpreted as a chain.  We return true if every list in xs is
;; disjoint from every other list in xs.

(defund mutually-disjointp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (disjoint-from-allp (car xs) (cdr xs))
           (mutually-disjointp (cdr xs)))
    t))

(defthm mutually-disjointp-when-not-consp
  (implies (not (consp xs))
           (equal (mutually-disjointp xs)
                  t))
  :hints(("Goal" :in-theory (enable mutually-disjointp))))

(defthm mutually-disjointp-of-cons
  (equal (mutually-disjointp (cons x xs))
         (and (disjoint-from-allp x xs)
              (mutually-disjointp xs)))
  :hints(("Goal" :in-theory (enable mutually-disjointp))))

(defthm booleanp-of-mutually-disjointp
  (equal (booleanp (mutually-disjointp xs))
         t)
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm mutually-disjointp-of-cdr-when-mutually-disjointp
  (implies (mutually-disjointp xs)
           (equal (mutually-disjointp (cdr xs))
                  t))
  :hints(("Goal" :cases ((consp xs)))))

(defthm mutually-disjointp-of-list-fix
  (equal (mutually-disjointp (list-fix x))
         (mutually-disjointp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm mutually-disjointp-of-app
  (equal (mutually-disjointp (app x y))
         (and (mutually-disjointp x)
              (mutually-disjointp y)
              (all-disjoint-from-allp x y)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm mutually-disjointp-of-rev
  (equal (mutually-disjointp (rev x))
         (mutually-disjointp x))
  :hints(("Goal" :induct (cdr-induction x))))

;; I thought for some time that I might be able to generalize the below to
;; arbitrary subsets.  But I now realize that this won't be possible, because a
;; subset might have repeated members which will not be disjoint from their
;; copies.

(defthm mutually-disjointp-of-remove-all-when-mutually-disjointp
  (implies (mutually-disjointp x)
           (equal (mutually-disjointp (remove-all a x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjointp-when-both-membersp-of-mutually-disjointp
  (implies (and (mutually-disjointp xs)
                (memberp a xs)
                (memberp b xs))
           (equal (disjointp a b)
                  (if (equal a b)
                      (not (consp a))
                    t)))
  :hints(("Goal" :induct (cdr-induction xs))))









(defund disjoint-from-allp-badguy (x ys)
  (declare (xargs :guard t))
  (if (consp ys)
      (if (disjointp x (car ys))
          (disjoint-from-allp-badguy x (cdr ys))
        (car ys))
    nil))

(encapsulate
 ()
 (local (defthm disjoint-from-allp-badguy-when-not-consp
          (implies (not (consp ys))
                   (equal (disjoint-from-allp-badguy x ys)
                          nil))
          :hints(("Goal" :in-theory (enable disjoint-from-allp-badguy)))))

 (local (defthm disjoint-from-allp-badguy-of-cons
          (equal (disjoint-from-allp-badguy x (cons y ys))
                 (if (disjointp x y)
                     (disjoint-from-allp-badguy x ys)
                   y))
          :hints(("Goal" :in-theory (enable disjoint-from-allp-badguy)))))

 (defthmd disjoint-from-allp-badguy-property
   (implies (not (disjoint-from-allp x ys))
            (and (memberp (disjoint-from-allp-badguy x ys) ys)
                 (not (disjointp x (disjoint-from-allp-badguy x ys)))))
   :hints(("Goal" :induct (cdr-induction ys)))))

(defthm disjoint-from-allp-of-remove-all-when-memberp-of-mutually-disjointp
  (implies (and (mutually-disjointp xs)
                (memberp x xs))
           (equal (disjoint-from-allp x (remove-all x xs))
                  t))
  :hints(("Goal"
          :use ((:instance disjoint-from-allp-badguy-property
                           (x x)
                           (ys (remove-all x xs)))))))

(defthm member-of-nonep-of-remove-all-when-mutually-disjointp
  (implies (and (mutually-disjointp xs)
                (memberp x xs))
           (equal (member-of-nonep a (remove-all x xs))
                  (if (member-of-nonep a xs)
                      t
                    (memberp a x))))
  :hints(("Goal" :induct (cdr-induction xs))))


(defthm disjoint-from-allp-when-subsetp-of-remove-all-of-mutually-disjointp
  (implies (and (subsetp xs (remove-all y ys))
                (mutually-disjointp ys)
                (memberp y ys))
           (equal (disjoint-from-allp y xs)
                  t)))

;; YUCK.  This is so damn horrible.

(defthm disjoint-from-allp-when-subsetp-of-remove-all-of-mutually-disjointp-two
  (implies (and (mutually-disjointp ys)
                (memberp y ys)
                (subsetp xs (remove-all y ys)))
           (equal (disjoint-from-allp y xs)
                  t)))





(defthm lists-lookup-of-rev-when-mutually-disjointp
  (implies (mutually-disjointp xs)
           (equal (lists-lookup a (rev xs))
                  (lists-lookup a xs)))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm lists-lookup-when-memberp-in-lists-lookup-when-mutually-disjointp
  (implies (and (mutually-disjointp xs)
                (memberp a (lists-lookup b xs)))
           (equal (lists-lookup a xs)
                  (lists-lookup b xs)))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm lists-lookup-of-remove-all-from-mutually-disjointp
  (implies (and (mutually-disjointp xs)
                (memberp x xs))
           (equal (lists-lookup a (remove-all x xs))
                  (if (or (member-of-nonep a xs)
                          (memberp a x))
                      nil
                    (lists-lookup a xs))))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm lists-lookup-when-mutually-disjointp
  (implies (and (mutually-disjointp xs)
                (memberp x xs)
                (memberp a x)
                (memberp b x))
           (equal (lists-lookup a xs)
                  (lists-lookup b xs)))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm lists-lookup-of-car-of-lists-lookup
  (implies (and (mutually-disjointp xs)
                (not (member-of-nonep a xs)))
           (equal (lists-lookup (car (lists-lookup a xs)) xs)
                  (lists-lookup a xs)))
  :hints(("Goal" :use ((:instance lists-lookup-when-mutually-disjointp
                                  (x (lists-lookup a xs))
                                  (b (car (lists-lookup a xs))))))))

(defthm member-of-nonep-when-member-of-lists-lookup
  (implies (memberp a (lists-lookup b xs))
           (equal (member-of-nonep a xs)
                  nil))
  :hints(("Goal" :induct (cdr-induction xs))))

(defthm member-of-nonep-when-member-of-cdr-of-lists-lookup
  (implies (memberp a (cdr (lists-lookup b xs)))
           (equal (member-of-nonep a xs)
                  nil))
  :hints(("Goal"
          :in-theory (disable member-of-nonep-when-member-of-lists-lookup)
          :use ((:instance member-of-nonep-when-member-of-lists-lookup)))))

(defthm member-of-nonep-of-car-of-lists-lookup
  (equal (member-of-nonep (car (lists-lookup a xs)) xs)
         (and (member-of-nonep a xs)
              (member-of-nonep nil xs)))
  :hints(("Goal" :induct (cdr-induction xs))))

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defthm member-of-lists-lookup-when-members-of-mutually-disjointp
   (implies (and (mutually-disjointp xs)
                 (not (member-of-nonep a xs))
                 (not (member-of-nonep c xs)))
            (equal (memberp c (lists-lookup a xs))
                   (equal (lists-lookup a xs)
                          (lists-lookup c xs))))))




(deflist disjoint-from-nonep (e x)
  (disjointp e x)
  :negatedp t
  :elementp-of-nil t)

(defthm disjoint-from-nonep-when-not-consp-left
  (implies (not (consp e))
           (equal (disjoint-from-nonep e x)
                  (not (consp x))))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjoint-from-nonep-of-cons-left
  (implies (disjoint-from-nonep e x)
           (equal (disjoint-from-nonep (cons a e) x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjoint-from-nonep-of-list-fix-left
  (equal (disjoint-from-nonep (list-fix e) x)
         (disjoint-from-nonep e x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjoint-from-nonep-of-app-left-one
  (implies (disjoint-from-nonep e x)
           (equal (disjoint-from-nonep (app e a) x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjoint-from-nonep-of-app-left-two
  (implies (disjoint-from-nonep e x)
           (equal (disjoint-from-nonep (app a e) x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm disjoint-from-nonep-of-rev-left
  (equal (disjoint-from-nonep (rev e) x)
         (disjoint-from-nonep e x))
  :hints(("Goal" :induct (cdr-induction x))))

