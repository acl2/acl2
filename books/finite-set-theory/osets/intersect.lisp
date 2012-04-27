; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public Lic-
; ense along with this program; if not, write to the Free Soft- ware
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "SETS")
(include-book "membership")
(set-verify-guards-eagerness 2)



; Fast Intersect
;
; Again we are only interested in showing that fast-intersect creates sets and
; has the expected membership property.

(defun fast-intersectp (X Y)
  (declare (xargs :guard (and (setp X)
                              (setp Y))
                  :measure (fast-measure X Y)
                  :verify-guards nil))
  (cond ((endp X) nil)
        ((endp Y) nil)
        ((equal (car X) (car Y))
         t)
        ((mbe :logic (<< (car X) (car y))
              :exec (fast-lexorder (car X) (car Y)))
         (fast-intersectp (cdr X) Y))
        (t
         (fast-intersectp X (cdr Y)))))

(verify-guards fast-intersectp
  :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))


;; PATCH (0.91): David Rager noticed that as of v0.9, fast-intersect was not
;; tail recursive, and submitted an updated version.  The original
;; fast-intersect has been renamed to fast-intersect-old, and the new
;; fast-intersect replaces it.

(local
 (encapsulate
   ()

   (defun fast-intersect-old (X Y)
     (declare (xargs :measure (fast-measure X Y)
                     :guard (and (setp X) (setp Y))
                     :verify-guards nil))
     (cond ((endp X) nil)
           ((endp Y) nil)
           ((equal (car X) (car Y))
            (cons (car X) (fast-intersect-old (cdr X) (cdr Y))))
           ((mbe :logic (<< (car X) (car Y))
                 :exec (fast-lexorder (car X) (car Y)))
            (fast-intersect-old (cdr X) Y))
           (t
            (fast-intersect-old X (cdr Y)))))

   (verify-guards fast-intersect-old
     :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))

   (local (defthm l0
            (implies (and (consp (fast-intersect-old x y))
                          (or (atom x) (<< a (car x)))
                          (or (atom y) (<< a (car y)))
                          (setp x)
                          (setp y))
                     (<< a (car (fast-intersect-old x y))))
            :hints(("Goal" :in-theory (enable (:ruleset low-level-rules))))))

   (defthm setp-of-fast-intersect-old
     (implies (and (setp x)
                   (setp y))
              (setp (fast-intersect-old x y)))
     :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))

   (local (defthm l1
            (implies (and (member a x)
                          (member a y)
                          (setp x)
                          (setp y))
                     (member a (fast-intersect-old x y)))
            :hints(("Goal" :in-theory (enable (:ruleset low-level-rules))))))

   (local (defthm l2
            (implies (member a (fast-intersect-old x y))
                     (and (member a x)
                          (member a y)))
            :hints(("Goal" :in-theory (enable (:ruleset low-level-rules))))))

   (local (defthm member-of-fast-intersect-old
            (implies (and (setp x)
                          (setp y))
                     (iff (member a (fast-intersect-old x y))
                          (and (member a x)
                               (member a y))))))

   (defthm in-fast-intersect-old
     (implies (and (setp x)
                   (setp y))
              (equal (in a (fast-intersect-old x y))
                     (and (in a x)
                          (in a y))))
     :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))



   (local (defthm l4
            (equal (fast-intersectp X Y)
                   (consp (fast-intersect-old X Y)))
            :hints(("Goal" :in-theory (enable (:ruleset low-level-rules))))))

   (defthm fast-intersectp-correct-lemma
     (implies (and (setp X)
                   (setp Y))
              (equal (fast-intersectp X Y)
                     (not (empty (fast-intersect-old X Y)))))
     :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))))


(defun fast-intersect (X Y acc)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X)
                              (setp Y)
                              (true-listp acc))
                  :verify-guards nil))
  (cond ((endp X) (revappend acc nil))
        ((endp Y) (revappend acc nil))
        ((equal (car X) (car Y))
         (fast-intersect (cdr X) (cdr Y) (cons (car X) acc)))
        ((mbe :logic (<< (car X) (car Y))
              :exec (fast-lexorder (car X) (car Y)))
         (fast-intersect (cdr X) Y acc))
        (t
         (fast-intersect X (cdr Y) acc))))

(verify-guards fast-intersect
  :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))

(encapsulate
  ()
  (local (defthm lemma
           (implies (true-listp acc)
                    (equal (fast-intersect x y acc)
                           (revappend acc (fast-intersect-old x y))))))

  (local (defthm lemma2
           (equal (fast-intersect x y nil)
                  (fast-intersect-old x y))))

  (defthm fast-intersect-set
    (implies (and (force (setp X))
                  (force (setp Y)))
             (setp (fast-intersect X Y nil))))

  (defthm fast-intersect-membership
    (implies (and (setp X) (setp Y))
             (equal (in a (fast-intersect X Y nil))
                    (and (in a X) (in a Y)))))

  (defthm fast-intersectp-correct
    (implies (and (setp X) (setp Y))
             (equal (fast-intersectp X Y)
                    (not (empty (fast-intersect X Y nil))))))

  (in-theory (disable fast-intersect
                      fast-intersect-set
                      fast-intersect-membership
                      fast-intersectp
                      fast-intersectp-correct)))



(defsection intersect
  :parents (osets)
  :short "@(call intersect) constructs the intersection of <tt>X</tt> and
<tt>Y</tt>."

  :long "<p>The logical definition is very simple, and the essential
correctness property is given by <tt>intersect-in</tt>.</p>

<p>The execution uses a better, O(n) algorithm to intersect the sets by
exploiting the set order.</p>

<p>See also @(see intersectp), which doesn't construct a new set but just tells
you whether the sets have any overlap.  It's potentially faster if you don't
care about constructing the set, because it doesn't have to do any
consing.</p>"

  (defun intersect (X Y)
    (declare (xargs :guard (and (setp X) (setp Y))
                    :verify-guards nil))
    (mbe :logic (cond ((empty X) (sfix X))
                      ((in (head X) Y)
                       (insert (head X) (intersect (tail X) Y)))
                      (t (intersect (tail X) Y)))
         :exec (fast-intersect X Y nil)))

  (defthm intersect-set
    (setp (intersect X Y)))

  (defthm intersect-sfix-cancel-X
    (equal (intersect (sfix X) Y) (intersect X Y)))

  (defthm intersect-sfix-cancel-Y
    (equal (intersect X (sfix Y)) (intersect X Y)))

  (defthm intersect-empty-X
    (implies (empty X) (empty (intersect X Y))))

  (defthm intersect-empty-Y
    (implies (empty Y) (empty (intersect X Y))))

  (encapsulate ()

    (local (defthm intersect-in-Y
             (implies (not (in a Y))
                      (not (in a (intersect X Y))))))

    (local (defthm intersect-in-X
             (implies (not (in a X))
                      (not (in a (intersect X Y))))))

    (defthm intersect-in
      (equal (in a (intersect X Y))
             (and (in a Y) (in a X)))))

  (defthm intersect-symmetric
    (equal (intersect X Y) (intersect Y X))
    :rule-classes ((:rewrite :loop-stopper ((X Y)))))

  (defthm intersect-subset-X
    (subset (intersect X Y) X))

  (defthm intersect-subset-Y
    (subset (intersect X Y) Y))

  (defthm intersect-insert-X
    (implies (not (in a Y))
             (equal (intersect (insert a X) Y)
                    (intersect X Y))))

  (defthm intersect-insert-Y
    (implies (not (in a X))
             (equal (intersect X (insert a Y))
                    (intersect X Y))))


  (defthm intersect-with-subset-left
    (implies (subset X Y)
             (equal (intersect X Y)
                    (sfix X)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm intersect-with-subset-right
    (implies (subset X Y)
             (equal (intersect Y X)
                    (sfix X)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm intersect-self
    (equal (intersect X X) (sfix X)))

  (defthm intersect-associative
    (equal (intersect (intersect X Y) Z)
           (intersect X (intersect Y Z))))

  (defthm intersect-commutative
    (equal (intersect X (intersect Y Z))
           (intersect Y (intersect X Z)))
    :rule-classes ((:rewrite :loop-stopper ((X Y)))))

  (defthm intersect-outer-cancel
    (equal (intersect X (intersect X Z))
           (intersect X Z))))


(local (defthm fast-intersect-correct
         (implies (and (setp X)
                       (setp Y))
                  (equal (fast-intersect X Y nil)
                         (intersect X Y)))
         :hints(("Goal" :in-theory (enable fast-intersect-set
                                           fast-intersect-membership)))))

(verify-guards intersect)


(defsection intersectp
  :parents (osets)
  :short "@(call intersectp) checks whether <tt>X</tt> and <tt>Y</tt> have any
common members."

  :long "<p>Logically we just check whether the @(see intersect) of <tt>X</tt>
and <tt>Y</tt> is @(see empty).</p>

<p>In the execution, we use a faster function that checks for any common
members and doesn't build any new sets.</p>"

  (defun intersectp (X Y)
    (declare (xargs :guard (and (setp X) (setp Y))
                    :guard-hints(("Goal" :in-theory (enable fast-intersectp-correct)))))
    (mbe :logic (not (empty (intersect X Y)))
         :exec (fast-intersectp X Y))))
