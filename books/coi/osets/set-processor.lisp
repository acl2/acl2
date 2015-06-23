; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 Kookamara LLC
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

;; COI version, modified by Jared Davis, 2014-10, to include std/osets books
;; and only add the new functions and theorems that had been in COI.

(in-package "ACL2") ;bzo change this?

;bzo rename some theorems and functions in this book to have less generic names
;bzo all this stuff in duplicated in bozo.lisp in ray's project

(include-book "sets")

;therems about a generic set processor (especially the tricky "foo of insert" theorem).

;;
;; bzo start of stuff from jared - make this into a separate book?
;;

(defstub generic-pred (x) t)

(defstub process (x) t)

(defund process-set (set)
  (if (set::empty set)
      (set::emptyset)
    (let ((v (set::head set)))
      (if (generic-pred v)
          (set::insert (process v)
                  (process-set (set::tail set)))
        (process-set (set::tail set))))))

(defund filter-generic-pred (x)
  ;;  filter-generic-pred(x) = { x | (v \in x) ^ (generic-pred v) }
  (if (set::empty x)
      (set::emptyset)
    (let ((v (set::head x)))
      (if (generic-pred v)
          (set::insert v (filter-generic-pred (set::tail x)))
        (filter-generic-pred (set::tail x))))))

(defund process-all (x)
  ;; process-all(x) = { (process v) | v \in x }
  (if (set::empty x)
      (set::emptyset)
    (set::insert (process (set::head x))
            (process-all (set::tail x)))))

;; Now we can say that process-set is actually the following non-recursive
;; function, which just composes these two operations.

(defund my-process-set (x)
  (process-all (filter-generic-pred x)))

;; By breaking it up like this we can now reason about each part
;; separately and then talk about why process-all is hard to reason about.  To
;; begin, notice how well we can reason about filter-generic-pred, e.g., below.

(defthm setp-of-filter-generic-pred
  (set::setp (filter-generic-pred x))
  :hints(("Goal" :in-theory (enable filter-generic-pred))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (generic-pred a)
                   (equal (set::in a (filter-generic-pred x))
                          (set::in a x)))
          :hints(("Goal" :in-theory (enable filter-generic-pred)))))

 (local (defthm lemma2
          (implies (not (generic-pred a))
                   (not (set::in a (filter-generic-pred x))))
          :hints(("Goal" :in-theory (enable filter-generic-pred)))))

 (defthm in-filter-generic-pred
   (equal (set::in a (filter-generic-pred x))
          (and (generic-pred a)
               (set::in a x)))))

;; Unfortunately the process-all function is much more complicated.  We can
;; still easily say that it produces a set...

(defthm setp-of-process-all
  (set::setp (process-all x))
  :hints(("Goal" :in-theory (enable process-all))))

;; But what is the membership propery here?  It isn't as easy to say.  Really,
;; what we have is the following:
;;
;;   (set::in a (process-all x))
;;     =
;;   exists b in x such that (process b) = a.
;;
;; There are a few different ways we might introduce this.  One way would be to
;; just write a recursive function to try to see if such a b exists, e.g., as
;; below.

(defund has-process-inverse (a x)
  ;; (has-process-inverse a x) = exists b in x such that (process b) = a
  (if (set::empty x)
      nil
    (or (equal a (process (set::head x)))
       (has-process-inverse a (set::tail x)))))

;; Now we can say the following thing about membership in process-all.  It's
;; probably not very clear that we want to do this yet, but maybe since
;; has-process-inverse is a relatively simple function, there will be nice
;; properties about it that we can prove.

(defthm in-process-all
  (equal (set::in a (process-all x))
         (has-process-inverse a x))
  :hints(("Goal" :in-theory (enable process-all has-process-inverse))))

;; And now we have:

(defthm setp-of-my-process-set
  (set::setp (my-process-set x))
  :hints(("Goal" :in-theory (enable my-process-set))))

(defthm in-my-process-set
  (equal (set::in a (my-process-set x))
         (has-process-inverse a (filter-generic-pred x)))
  :hints(("Goal" :in-theory (enable my-process-set))))

;; Well, now lets just imagine that we wanted to prove the MBE equivalence
;; of process-set and my-process-set.  We can first note that process-set
;; creates a set.

(defthm setp-of-process-set
  (set::setp (process-set x))
  :hints(("Goal" :in-theory (enable process-set))))

;; Well then, all we need to do is prove the membership property for
;; process-set is the same as for in-process-all.  In other words, we
;; need to prove:
;;
;;   (set::in a (process-set x)) = (has-process-inverse a
;;                                                      (filter-generic-pred x))
;;
;; It took me awhile to prove this.  I haven't bothered to clean up the
;; lemmas I used, so this is reallly ugly. sorry.

(defthm subset-of-filter-each-when-subset
  (implies (set::subset x y)
           (set::subset (filter-generic-pred x) (filter-generic-pred y)))
  :hints(("Goal"
          ;; may not need to do this later
          :in-theory (enable set::subset))))

(defthm has-process-inverse-when-in
  (implies (set::in a x)
           (has-process-inverse (process a) x))
  :hints(("Goal" :in-theory (enable has-process-inverse))))

(defthm has-process-inverse-when-equal-to-process-member
  (implies (and (set::in b x)
                (equal (process b) a))
           (has-process-inverse a x))
  :hints(("Goal" :in-theory (enable has-process-inverse))))

(defthm has-process-inverse-when-has-process-inverse-of-subset
  (implies (and (set::subset x y)
                (has-process-inverse a x))
           (has-process-inverse a y))
  :hints(("Goal" :in-theory (enable has-process-inverse))))

(defthm has-process-inverse-when-has-process-inverse-of-subset-alt
  (implies (and (has-process-inverse a x)
                (set::subset x y))
           (has-process-inverse a y)))

(encapsulate
 ()
 (local (defthm terrible-lemma
          (implies (and (set::empty x)
                        (not (equal a (process b))))
                   (not (has-process-inverse a (set::insert b x))))
          :hints(("goal" :in-theory (enable has-process-inverse
                                            set::insert
                                            set::empty
                                            set::sfix
                                            set::head
                                            set::tail)))))

 (defthm badly-named-property-of-has-process-inverse
   (implies (and (not (has-process-inverse a x))
                 (not (equal a (process b))))
            (not (has-process-inverse a (set::insert b x))))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :expand ( )
            :in-theory (enable has-process-inverse
                               ;bzo had to add these enables
                               ;should we enable them?
                               set::WEAK-INSERT-INDUCTION-HELPER-1
                               set::WEAK-INSERT-INDUCTION-HELPER-2
                               set::WEAK-INSERT-INDUCTION-HELPER-3)))))

(encapsulate
 ()
 (local (defthm in-process-set-forward
          (implies (set::in a (process-set x))
                   (has-process-inverse a (filter-generic-pred x)))
          :hints(("Goal" :in-theory (enable process-set
                                            has-process-inverse
                                            filter-generic-pred)))))

 (local (defthm in-process-set-backwards
          (implies (not (set::in a (process-set x)))
                   (not (has-process-inverse a (filter-generic-pred x))))
          :hints(("Goal" :in-theory (enable process-set
                                            has-process-inverse
                                            filter-generic-pred)))))

 (defthm in-process-set
   (equal (set::in a (process-set x))
          (has-process-inverse a (filter-generic-pred x)))
   :hints(("Goal"
           :use ((:instance in-process-set-backwards)
                 (:instance in-process-set-forward))))))

;; And now the MBE equivalence is just by double containment...

(encapsulate
 ()

 (local (defthm lemma
          (set::subset (process-set x)
                       (my-process-set x))
          ;; shouldn't need this?
          :hints(("Goal" :in-theory (enable set::subset)))))

 (local (defthm lemma2
          (set::subset (my-process-set x)
                       (process-set x))
          ;; shouldn't need this?
          :hints(("Goal" :in-theory (enable set::subset)))))

 (defthm mbe-equivalence
   (equal (process-set x)
          (my-process-set x))
   :hints (("Goal" :in-theory (enable set::DOUBLE-CONTAINMENT-expensive
                                      )))))

;; Well now lets try to prove properties.  Your first goal is a really
;; simple consequence of the following lemma.

(encapsulate
 ()

 (local (defthm lemma
          (implies (not (generic-pred a))
                   (equal (filter-generic-pred (set::insert a x))
                          (filter-generic-pred x)))
          ;; won't need this hint later
          :hints(("Goal" :in-theory (enable ;subset
                                     set::DOUBLE-CONTAINMENT-expensive)))))

 (defthm goal-1
   (implies (and (set::setp x)
                 (not (generic-pred a)))
            (equal (process-set (set::insert a x))
                   (process-set x)))
   :hints(("Goal" :in-theory (enable my-process-set)))))

;; For the second goal, two lemmas are useful:

(encapsulate
 ()

 (local (defthm lemma
          (implies (generic-pred a)
                   (equal (filter-generic-pred (set::insert a x))
                          (set::insert a (filter-generic-pred x))))
          ;; won't need this hint later
          :hints(("Goal" :in-theory (enable ;subset
                                            set::DOUBLE-CONTAINMENT-EXPENSIVE)))))

 (local (defthm lemma-2
          (equal (set::insert (process a) (process-all x))
                 (process-all (set::insert a x)))
          :hints(("Goal" :in-theory (enable ;subset
                                            set::DOUBLE-CONTAINMENT-EXPENSIVE)))))

 (defthm goal-2
   (implies (and (set::setp x)
                 (generic-pred a))
            (equal (process-set (set::insert a x))
                   (set::insert (process a)
                                (process-set x))))
   :hints(("Goal" :in-theory (enable my-process-set)))))

(defthm goal-both
  (implies (set::setp x)
           (equal (process-set (set::insert a x))
                  (if (generic-pred a)
                      (set::insert (process a)
                                   (process-set x))
                    (process-set x))))
  :hints (("Goal" :in-theory (disable MBE-EQUIVALENCE))))

;;bzo add to sets?
;disabling, since showed up high in accumulated persistence
(defthmd insert-into-non-setp
  (implies (NOT (SET::SETP X))
           (equal (SET::INSERT A X)
                  (SET::INSERT A (set::emptyset)))))

(local (in-theory (enable insert-into-non-setp)))

(defthm tail-of-singleton
  (equal (SET::TAIL (SET::INSERT A NIL))
         nil)
  :hints (("Goal" :in-theory (enable SET::INSERT SET::TAIL SET::SFIX))))

;bzo uncomment thos...
(defthm goal-both-better
  (equal (process-set (set::insert a x))
         (if (generic-pred a)
             (set::insert (process a)
                          (process-set x))
           (process-set x)))
  :hints (("Goal" :use (:instance goal-both)
           :expand (PROCESS-ALL (SET::INSERT A NIL))
           :in-theory (e/d (SET::EMPTY
                            FILTER-GENERIC-PRED
                            MY-PROCESS-SET)(goal-both)))))
