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


(defsection delete
  :parents (osets)
  :short "@(call delete) removes the element @('a') from the set @('X')."

  :long "<p>If @('a') is not a member of @('X'), then the result is just @('X')
itself.</p>

<p>Efficiency note.  Delete is @('O(n)').  It is very inefficient to call it
repeatedly.  Instead, consider removing multiple elements with @(see
difference) or @(see intersect).</p>

<p>The theorem @('delete-in') is the essential correctness property for
@('delete').</p>"

  (defun delete (a X)
    (declare (xargs :guard (setp X)
                    :verify-guards nil))
    (mbe :logic
         (cond ((empty X) nil)
               ((equal a (head X)) (tail X))
               (t (insert (head X) (delete a (tail X)))))
         :exec
         (cond ((endp X) nil)
               ((equal a (car X)) (cdr X))
               (t (insert (car X) (delete a (cdr X)))))))

  (defthm delete-set
    (setp (delete a X)))

  (verify-guards delete
    :hints(("Goal" :in-theory (enable (:ruleset primitive-rules)))))

  (defthm delete-preserves-empty
    (implies (empty X)
             (empty (delete a X))))

  (defthm delete-in
    (equal (in a (delete b X))
           (and (in a X)
                (not (equal a b)))))

  (defthm delete-sfix-cancel
    (equal (delete a (sfix X))
           (delete a X)))

  (defthm delete-nonmember-cancel
    (implies (not (in a X))
             (equal (delete a X) (sfix X))))

  (defthm delete-delete
    (equal (delete a (delete b X))
           (delete b (delete a X)))
    :rule-classes ((:rewrite :loop-stopper ((a b)))))

  (defthm repeated-delete
    (equal (delete a (delete a X))
           (delete a X)))

  (defthm delete-insert-cancel
    (equal (delete a (insert a X))
           (delete a X)))

  (defthm insert-delete-cancel
    (equal (insert a (delete a X))
           (insert a X)))

  (defthm subset-delete
    (subset (delete a X) X)))