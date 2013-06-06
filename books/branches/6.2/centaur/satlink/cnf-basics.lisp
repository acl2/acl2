; SATLINK - Link from ACL2 to SAT Solvers
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

; cnf-basics.lisp -- Basic theorems about variables, literals, clauses,
; evaluation, etc.  We generally expect to locally include this any time we
; actually want to reason about our CNF representation.

(in-package "SATLINK")
(include-book "cnf")
(include-book "centaur/misc/equal-sets" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (enable eval-clause eval-formula)))

(local (defthm equal-1-when-bitp
         (implies (bitp x)
                  (equal (equal x 1)
                         (not (equal x 0))))))

(defsection cnf-basics
  :extension eval-formula

  (defcong var-equiv equal (eval-var x env) 1
    :hints(("Goal" :in-theory (enable eval-var))))

  (defcong bits-equiv equal (eval-var x env) 2
    :hints(("Goal" :in-theory (enable eval-var))))



  (defcong lit-equiv equal (eval-lit x env) 1
    :hints(("Goal" :in-theory (enable eval-lit))))

  (defcong bits-equiv equal (eval-lit x env) 2
    :hints(("Goal" :in-theory (enable eval-lit))))



  (defthm eval-lit-of-make-lit
    (equal (eval-lit (make-lit var neg) env)
           (b-xor neg (eval-var var env)))
    :hints(("Goal" :in-theory (enable eval-lit))))

  (defthm eval-lit-of-lit-negate
    (equal (eval-lit (lit-negate lit) env)
           (b-not (eval-lit lit env)))
    :hints(("Goal" :in-theory (enable eval-lit))))


  (defthm eval-clause-when-atom
    (implies (atom clause)
             (equal (eval-clause clause env)
                    0)))

  (defthm eval-clause-of-cons
    (equal (eval-clause (cons lit clause) env)
           (b-ior (eval-lit lit env)
                  (eval-clause clause env))))

  (defthm eval-clause-when-some-true-literal
    (implies (and (member lit clause)
                  (equal (eval-lit lit env) 1))
             (equal (eval-clause clause env)
                    1)))

  (local (defthm l0
           (implies (and (subsetp c1 c2)
                         (equal (eval-clause c2 env) 0))
                    (equal (eval-clause c1 env) 0))
           :hints(("Goal" :induct (len c1)))))

  (defcong set-equiv equal (eval-clause clause env) 1
    :hints(("Goal" :in-theory (enable set-equiv))))

  (defcong bits-equiv equal (eval-clause clause env) 2)



  (defthm eval-formula-when-atom
    (implies (atom formula)
             (equal (eval-formula formula env)
                    1)))

  (defthm eval-formula-of-cons
    (equal (eval-formula (cons clause formula) env)
           (b-and (eval-clause clause env)
                  (eval-formula formula env))))

  (defthm eval-formula-when-some-false-clause
    (implies (and (member clause formula)
                  (equal (eval-clause clause env) 0))
             (equal (eval-formula formula env)
                    0)))

  (local (defthm l1
           (implies (and (subsetp f1 f2)
                         (equal (eval-formula f2 env) 1))
                    (equal (eval-formula f1 env) 1))
           :hints(("Goal" :induct (len f1)))))

  (defcong set-equiv equal (eval-formula formula env) 1
    :hints(("Goal" :in-theory (enable set-equiv))))

  (defcong bits-equiv equal (eval-formula formula env) 2))



(defsection max-index-clause-basics
  :extension max-index-clause

  (local (in-theory (enable max-index-clause)))

  (defthm max-index-clause-when-atom
    (implies (atom clause)
             (equal (max-index-clause clause)
                    0)))

  (defthm max-index-clause-of-cons
    (equal (max-index-clause (cons lit clause))
           (max (var->index (lit->var lit))
                (max-index-clause clause))))

  (defthm index-of-literals-is-bounded-by-max-index-clause
    (implies (member lit clause)
             (<= (var->index (lit->var lit)) (max-index-clause clause)))
    :rule-classes ((:rewrite) (:linear)))

  (local (defthm l0
           (implies (subsetp-equal c1 c2)
                    (<= (max-index-clause c1)
                        (max-index-clause c2)))
           :rule-classes :linear
           :hints(("Goal" :induct (len c1)))))

  (defcong set-equiv equal (max-index-clause x) 1
    :hints(("Goal" :in-theory (enable set-equiv)))))



(defsection max-index-formula-basics
  :extension max-index-formula

  (local (in-theory (enable max-index-formula)))

  (defthm max-index-formula-when-atom
    (implies (atom formula)
             (equal (max-index-formula formula)
                    0)))

  (defthm max-index-formula-of-cons
    (equal (max-index-formula (cons clause formula))
           (max (max-index-clause clause)
                (max-index-formula formula))))

  (defthm max-index-clause-is-bounded-by-max-index-formula
    (implies (member clause formula)
             (<= (max-index-clause clause) (max-index-formula formula)))
    :rule-classes ((:rewrite) (:linear)))

  (local (defthm l0
           (implies (subsetp-equal f1 f2)
                    (<= (max-index-formula f1)
                        (max-index-formula f2)))
           :rule-classes :linear
           :hints(("Goal" :induct (len f1)))))

  (defcong set-equiv equal (max-index-formula x) 1
    :hints(("Goal" :in-theory (enable set-equiv)))))



(defsection clause-indices-basics
  :extension clause-indices

  (local (in-theory (enable clause-indices)))

  (local (defthm l0
           (implies (member-equal a f1)
                    (member-equal (var->index (lit->var a)) (clause-indices f1)))))

  (local (defthm l1
           (implies (subsetp-equal f1 f2)
                    (subsetp-equal (clause-indices f1)
                                   (clause-indices f2)))))

  (local (defthm clause-indices-of-list-fix
           (equal (clause-indices (list-fix x))
                  (clause-indices x))))

  (local (defun my-ind (x y)
           (if (or (atom x)
                   (atom y))
               nil
             (my-ind (cdr x) (cdr y)))))

  (defthm nat-listp-of-clause-indices
    (nat-listp (clause-indices x)))

  (defcong list-equiv equal (clause-indices x) 1
    :hints(("Goal" :induct (my-ind x acl2::x-equiv))))

  (defcong set-equiv set-equiv (clause-indices x) 1
    :hints(("Goal" :in-theory (enable set-equiv)))))



(defsection formula-indices-basics
  :extension formula-indices

  (local (in-theory (enable formula-indices)))

  (local (defun my-ind (x y)
           (if (or (atom x)
                   (atom y))
               nil
             (my-ind (cdr x) (cdr y)))))

  (defthm nat-listp-of-formula-indices
    (nat-listp (formula-indices x)))

  (defcong list-equiv equal (formula-indices x) 1
    :hints(("Goal" :induct (my-ind x acl2::x-equiv))))

  (local (defthm l0
           (implies (member-equal clause formula)
                    (subsetp-equal (clause-indices clause)
                                   (formula-indices formula)))))

  (local (defthm l1
           (implies (subsetp-equal f1 f2)
                    (subsetp-equal (formula-indices f1)
                                   (formula-indices f2)))))

  (defcong set-equiv set-equiv (formula-indices x) 1
    :hints(("Goal" :in-theory (enable set-equiv)))))

