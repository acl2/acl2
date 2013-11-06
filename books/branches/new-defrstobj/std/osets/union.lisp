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
    (implies (and (force (setp X))
                  (force (setp Y)))
             (setp (fast-union X Y nil))))

  (defthm fast-union-membership
    (implies (and (setp X) (setp Y))
             (equal (in a (fast-union X Y nil))
                    (or (in a X) (in a Y)))))

  (in-theory (disable fast-union
                      fast-union-set
                      fast-union-membership)))




(defsection union
  :parents (osets)
  :short "@(call union) constructs the union of @('X') and @('Y')."

  :long "<p>The logical definition is very simple, and the essential
correctness property is given by @('union-in').</p>

<p>The execution uses a better, O(n) algorithm to merge the sets by exploiting
the set order.</p>"

  (defun union (X Y)
    (declare (xargs :guard (and (setp X) (setp Y))
                    :verify-guards nil))
    (mbe :logic (if (empty X)
                    (sfix Y)
                  (insert (head X) (union (tail X) Y)))
         :exec  (fast-union X Y nil)))

  (defthm union-set
    (setp (union X Y)))

  (defthm union-sfix-cancel-X
    (equal (union (sfix X) Y) (union X Y)))

  (defthm union-sfix-cancel-Y
    (equal (union X (sfix Y)) (union X Y)))

  (defthm union-empty-X
    (implies (empty X)
             (equal (union X Y) (sfix Y))))

  (defthm union-empty-Y
    (implies (empty Y)
             (equal (union X Y) (sfix X))))

  (defthm union-empty
    (equal (empty (union X Y))
           (and (empty X) (empty Y))))

  (defthm union-in
    (equal (in a (union X Y))
           (or (in a X) (in a Y))))

  (verify-guards union
    :hints(("Goal" :in-theory (enable fast-union-set
                                      fast-union-membership))))


  (defthm union-symmetric
    (equal (union X Y) (union Y X))
    :rule-classes ((:rewrite :loop-stopper ((X Y)))))

  (defthm union-subset-X
    (subset X (union X Y)))

  (defthm union-subset-Y
    (subset Y (union X Y)))

  (defthm union-insert-X
    (equal (union (insert a X) Y)
           (insert a (union X Y))))

  (defthm union-insert-Y
    (equal (union X (insert a Y))
           (insert a (union X Y))))

  (defthm union-with-subset-left
    (implies (subset X Y)
             (equal (union X Y)
                    (sfix Y)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm union-with-subset-right
    (implies (subset X Y)
             (equal (union Y X)
                    (sfix Y)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm union-self
    (equal (union X X) (sfix X)))

  (defthm union-associative
    (equal (union (union X Y) Z)
           (union X (union Y Z))))

  (defthm union-commutative
    (equal (union X (union Y Z))
           (union Y (union X Z)))
    :rule-classes ((:rewrite :loop-stopper ((X Y)))))

  (defthm union-outer-cancel
    (equal (union X (union X Z))
           (union X Z))))