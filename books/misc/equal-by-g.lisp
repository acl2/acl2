; equal-by-g.lisp -- theorem for pick-a-point proofs of record equality
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "records")
(local (include-book "equal-by-g-help"))

; This book introduces a generic theorem that can be functionally instantiated
; to carry out pick-a-point proofs that records are equal.  The constraint is
; given by the following encapsulate.

(encapsulate
  (((equal-by-g-hyp) => *)
   ((equal-by-g-lhs) => *)
   ((equal-by-g-rhs) => *))

  (local (defun equal-by-g-hyp () nil))
  (local (defun equal-by-g-lhs () nil))
  (local (defun equal-by-g-rhs () nil))

  (defthm equal-by-g-constraint
    (implies (equal-by-g-hyp)
             (equal (g arbitrary-key (equal-by-g-lhs))
                    (g arbitrary-key (equal-by-g-rhs))))))

(defthm equal-by-g
  (implies (equal-by-g-hyp)
           (equal (equal-by-g-lhs)
                  (equal-by-g-rhs)))
  :hints(("Goal"
          :in-theory (disable g-worseguy-finds-counterexample
                              g-worseguy)
          :use ((:instance g-worseguy-finds-counterexample
                           (x (equal-by-g-lhs))
                           (y (equal-by-g-rhs)))))))
