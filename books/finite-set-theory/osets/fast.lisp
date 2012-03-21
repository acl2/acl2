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


; fast.lisp
;
; The MBE feature in ACL2 version 2.8 provides the opportunity to introduce
; functions which take advantage of the set order for good execution
; efficiency, while still using simple/nice functions for reasoning about.
;
; This file contains efficient versions of the union, intersect, and difference
; functions, and a few theorems about them.  The goal is to show that for each
; of these "fast" functions, when given two sets as inputs:
;
;   (1) produces a set, and
;   (2) has the correct membership properties
;
; These facts can then be used to make an equal-by-membership argument with the
; simple versions as required by MBE.
;
; Note that this file is very ugly.  There are many factors that contribute to
; this problem.  For one, these functions are written in terms of cons and
; therefore we have to consider many cases.  This also means we have lots of
; subgoals when we do inductions.  It is also challenging to develop a "good"
; rewrite theory when it comes to the cons function, which does not have very
; nice properties when related to sets.

(in-package "SETS")
(include-book "membership")
(set-verify-guards-eagerness 2)



; I've tried various approaches to exposing the set order.  My current strategy
; is to open all primitives, convert IN to MEMBER, and convert SUBSET to
; SUBSETP (list subset).  BOZO discuss the other, lifting approach.

(encapsulate
  ()
  (local (in-theory (enable (:ruleset primitive-rules)
                            (:ruleset order-rules))))

  (defthm setp-of-cons
    (equal (setp (cons a X))
           (and (setp X)
                (or (<< a (head X))
                    (empty X)))))

  (defthm in-to-member
    (implies (setp X)
             (equal (in a X)
                    (if (member a x)
                        t
                      nil))))

  (defthm not-member-when-smaller
    (implies (and (<< a (car x))
                  (setp x))
             (not (member a x))))

  (defthm subset-to-subsetp
    (implies (and (setp x)
                  (setp y))
             (equal (subset x y)
                    (subsetp x y))))

  (defthm lexorder-<<-equiv
    ;; This lets us optimize << into just lexorder when we've already
    ;; checked equality.
    (implies (not (equal a b))
             (equal (equal (<< a b) (lexorder a b))
                    t))
    :hints(("Goal" :in-theory (enable <<)))))

(def-ruleset low-level-rules
  '(setp-of-cons
    in-to-member
    not-member-when-smaller
    subset-to-subsetp
    lexorder-<<-equiv
    (:ruleset primitive-rules)
    (:ruleset order-rules)))

(in-theory (disable (:ruleset low-level-rules)))



; These fast versions recur on one or both of their arguments, but not always
; the same argument.  Hence, we need to introduce a more flexible measure to
; prove that they terminate.  Fortunately, this is still relatively simple:

(defun fast-measure (X Y)
  (+ (acl2-count X) (acl2-count Y)))



; Fast Union
;
; We want to show that fast union always produces a set, and has the expected
; membership property.


; PATCH (0.91): David Rager noticed that as of v0.9, fast-union was not tail
; recursive, and submitted an updated version.  The original fast-union has
; been renamed to fast-union-old, and the new fast-union replaces it.

(local
 (encapsulate ()

   (defun fast-union-old (X Y)
     (declare (xargs :measure (fast-measure X Y)
                     :guard (and (setp X) (setp Y))
                     :verify-guards nil))
     (cond ((endp X) Y)
           ((endp Y) X)
           ((equal (car X) (car Y))
            (cons (car X) (fast-union-old (cdr X) (cdr Y))))
           ((fast-<< (car X) (car Y))
            (cons (car X) (fast-union-old (cdr X) Y)))
           (t
            (cons (car Y) (fast-union-old X (cdr Y))))))

   (defthm fast-union-old-set
     (implies (and (setp X) (setp Y))
              (setp (fast-union-old X Y)))
     :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))

   (defthm member-of-fast-union-old
     (iff (member a (fast-union-old x y))
          (or (member a x)
              (member a y))))

   (defthm fast-union-old-membership
     (implies (and (setp X) (setp Y))
              (equal (in a (fast-union-old X Y))
                     (or (in a X) (in a Y))))
     :hints(("Goal"
             :do-not '(generalize fertilize)
             :in-theory (enable (:ruleset low-level-rules)))))

   (verify-guards fast-union-old
     :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))))


(defun fast-union (x y acc)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp x)
                              (setp y)
                              (true-listp acc))
                  :verify-guards nil))
  (cond ((endp x) (revappend acc y))
        ((endp y) (revappend acc x))
        ((equal (car x) (car y))
         (fast-union (cdr x) (cdr y) (cons (car x) acc)))
        ((mbe :logic (<< (car x) (car y))
              :exec (fast-lexorder (car x) (car y)))
         (fast-union (cdr x) y (cons (car x) acc)))
        (t
         (fast-union x (cdr y) (cons (car y) acc)))))

(verify-guards fast-union
  :hints(("Goal"
          :do-not '(generalize fertilize)
          :in-theory (enable (:ruleset low-level-rules)))))

(encapsulate
  ()
  (local (defthm lemma
           (equal (fast-union x y acc)
                  (revappend acc (fast-union-old x y)))
           :hints(("Goal" :in-theory (enable (:ruleset low-level-rules))))))

  (local (defthm lemma2
           (equal (fast-union x y nil)
                  (fast-union-old x y))))

  (defthm fast-union-set
    (implies (and (setp X) (setp Y))
             (setp (fast-union X Y nil))))

  (defthm fast-union-membership
    (implies (and (setp X) (setp Y))
             (equal (in a (fast-union X Y nil))
                    (or (in a X) (in a Y)))))

  (in-theory (disable fast-union
                      fast-union-set
                      fast-union-membership)))




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
    (implies (and (setp X) (setp Y))
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




; Fast Difference
;
; As before, we want to show that difference always creates a set and that the
; produced set has the expected membership properties.  Also as before, these
; proofs are ugly.

; PATCH (0.91): David Rager noticed that as of v0.9, fast-difference was not
; tail recursive, and submitted an updated version.  The original
; fast-difference has been renamed to fast-difference-old, and the new
; fast-difference replaces it.

(defun fast-difference-old (X Y)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X) (setp Y))
                  :verify-guards nil))
  (cond ((endp X) nil)
        ((endp Y) X)
        ((equal (car X) (car Y))
         (fast-difference-old (cdr X) (cdr Y)))
        ((mbe :logic (<< (car X) (car Y))
              :exec (fast-lexorder (car X) (car Y)))
         (cons (car X) (fast-difference-old (cdr X) Y)))
        (t
         (fast-difference-old X (cdr Y)))))

(verify-guards fast-difference-old
  :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))

(local
 (encapsulate ()

   (local (defthm l0
            (implies (and (consp (fast-difference-old x y))
                          (or (atom x) (<< a (car x)))
                          (setp x))
                     (<< a (car (fast-difference-old x y))))
            :hints(("Goal" :in-theory (enable (:ruleset low-level-rules))))))

   (defthm fast-difference-old-set
     (implies (and (setp X) (setp Y))
              (setp (fast-difference-old X Y)))
     :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))

   (local (defthm l1
            (implies (and (member a x)
                          (not (member a y))
                          (setp x)
                          (setp y))
                     (member a (fast-difference-old x y)))
            :hints(("Goal" :in-theory (enable (:ruleset low-level-rules))))))

   (local (defthm l2
            (implies (and (member a (fast-difference-old x y))
                          (setp x)
                          (setp y))
                     (and (member a x)
                          (not (member a y))))
            :hints(("Goal" :in-theory (enable (:ruleset low-level-rules))))))

   (local (defthm member-of-fast-difference-old
            (implies (and (setp x)
                          (setp y))
                     (iff (member a (fast-difference-old x y))
                          (and (member a x)
                               (not (member a y)))))))

   (defthm fast-difference-old-membership
     (implies (and (setp X) (setp Y))
              (equal (in a (fast-difference-old X Y))
                     (and (in a X)
                          (not (in a Y)))))
     :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))))


(defun fast-difference (X Y acc)
  (declare (xargs :measure (fast-measure X Y)
                  :guard (and (setp X)
                              (setp Y)
                              (true-listp acc))
                  :verify-guards nil))
  (cond ((endp X) (revappend acc nil))
        ((endp Y) (revappend acc X))
        ((equal (car X) (car Y))
         (fast-difference (cdr X) (cdr Y) acc))
        ((mbe :logic (<< (car X) (car Y))
              :exec (fast-lexorder (car X) (car Y)))
         (fast-difference (cdr X) Y (cons (car X) acc)))
        (t
         (fast-difference X (cdr Y) acc))))

(verify-guards fast-difference
  :hints(("Goal" :in-theory (enable (:ruleset low-level-rules)))))

(encapsulate
  ()
  (local (defthm lemma
           (implies (true-listp acc)
                    (equal (fast-difference x y acc)
                           (revappend acc (fast-difference-old x y))))))

  (local (defthm lemma2
           (equal (fast-difference x y nil)
                  (fast-difference-old x y))))

  (defthm fast-difference-set
    (implies (and (setp X) (setp Y))
             (setp (fast-difference X Y nil))))

  (defthm fast-difference-membership
    (implies (and (setp X) (setp Y))
             (equal (in a (fast-difference X Y nil))
                    (and (in a X)
                         (not (in a Y))))))

  (in-theory (disable fast-difference
                      fast-difference-set
                      fast-difference-membership)))



