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
(include-book "delete")
(set-verify-guards-eagerness 2)

(defsection cardinality
  :parents (osets)
  :short "@(call cardinality) computes the number of elements in @('X')."

  :long "<p>This is like @(see length), but respects the non-set convention and
always returns 0 for ill-formed sets.</p>"

  (defun cardinality (X)
    (declare (xargs :guard (setp X)
                    :verify-guards nil))
    (mbe :logic (if (empty X)
                    0
                  (1+ (cardinality (tail X))))
         :exec  (length (the list X))))

  (verify-guards cardinality
    ;; Normally we would never want to enable the primitives theory.  However,
    ;; here we need to show that cardinality is equal to length, and for this
    ;; we need to be able to reason about tail and empty.  Think of this as a
    ;; tiny extension of "fast.lisp"
    :hints(("Goal" :in-theory (enable (:ruleset primitive-rules)))))

  (defthm cardinality-type
    (and (integerp (cardinality X))
         (<= 0 (cardinality X)))
    :rule-classes :type-prescription)

  (defthm cardinality-zero-empty
    (equal (equal (cardinality x) 0)
           (empty x)))

  (defthm cardinality-sfix-cancel
    (equal (cardinality (sfix X)) (cardinality X)))

  (encapsulate ()

    (local (defthm cardinality-insert-empty
             (implies (empty X)
                      (equal (cardinality (insert a X)) 1))
             :hints(("Goal" :use (:instance cardinality (x (insert a nil)))))))

    (defthm insert-cardinality
      (equal (cardinality (insert a X))
             (if (in a X)
                 (cardinality X)
               (1+ (cardinality X))))))

  (defthm delete-cardinality
    (equal (cardinality (delete a X))
           (if (in a X)
               (1- (cardinality X))
             (cardinality X))))

; Now that we have the delete function, we can prove an interesting
; theorem, namely that if (subset X Y) and |X| = |Y|, then X = Y.  In
; order to do this, we need to induct by deleting elements from both
; X and Y.  This is a little ugly, but along the way we will show the
; nice theorem, subset-cardinality.

  (local (defun double-delete-induction (X Y)
           (declare (xargs :guard (and (setp X) (setp Y))))
           (if (or (empty X) (empty Y))
               (list X Y)
             (double-delete-induction (delete (head X) X)
                                      (delete (head X) Y)))))

  (local (defthmd subset-double-delete
           (implies (subset X Y)
                    (subset (delete a X) (delete a Y)))
           :hints(("Goal" :in-theory (disable delete-nonmember-cancel
                                              in-tail-or-head)))))

  (encapsulate
    ()
    (local (defthm subset-cardinality-lemma
             (implies (and (not (or (empty x) (empty y)))
                           (implies (subset (delete (head x) x)
                                            (delete (head x) y))
                                    (<= (cardinality (delete (head x) x))
                                        (cardinality (delete (head x) y)))))
                      (implies (subset x y)
                               (<= (cardinality x) (cardinality y))))
             :hints(("goal" :use ((:instance subset-double-delete
                                             (a (head x))
                                             (x x)
                                             (y y)))))))

    (defthm subset-cardinality
      (implies (subset X Y)
               (<= (cardinality X) (cardinality Y)))
      :hints(("Goal" :induct (double-delete-induction X Y)))
      :rule-classes (:rewrite :linear)))

  (defthmd equal-cardinality-subset-is-equality
    (implies (and (setp X)
                  (setp Y)
                  (subset X Y)
                  (equal (cardinality X) (cardinality Y)))
             (equal (equal X Y) t))
    :hints(("Goal" :induct (double-delete-induction X Y))
           ("Subgoal *1/2"
            :use ((:instance subset-double-delete
                             (a (head X))
                             (X X)
                             (Y Y))
                  (:instance (:theorem
                              (implies (equal X Y)
                                       (equal (insert a X) (insert a Y))))
                             (a (head X))
                             (X (tail X))
                             (Y (delete (head X) Y)))))))

  (defthm proper-subset-cardinality
    (implies (and (subset X Y)
                  (not (subset Y X)))
             (< (cardinality X) (cardinality Y)))
    :rule-classes (:rewrite :linear)
    :hints(("Goal"
            :in-theory (disable pick-a-point-subset-strategy)
            :use ((:instance equal-cardinality-subset-is-equality
                             (X (sfix x))
                             (Y (sfix y))))))))


