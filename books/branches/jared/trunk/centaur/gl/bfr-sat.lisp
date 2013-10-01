; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "bfr")

(encapsulate
  (((bfr-sat *) => (mv * * *)))

  (local (defun bfr-sat (prop)
           (declare (xargs :guard t))
           (mv nil nil prop)))

  (defthm bfr-sat-nvals
    (equal (len (bfr-sat prop)) 3))

  (defthm bfr-sat-true-listp
    (true-listp (bfr-sat prop)))

  (defthm bfr-sat-unsat
    (mv-let (sat succeeded ctrex)
      (bfr-sat prop)
      (declare (ignore ctrex))
      (implies (and succeeded (not sat))
               (not (bfr-eval prop env))))))

(defun bfr-sat-bdd (prop)
  (declare (xargs :guard t))
  (if (bfr-mode)
      (mv nil nil nil) ;; AIG-mode, fail.
    (let ((sat? (acl2::eval-bdd prop (acl2::bdd-sat-dfs prop))))
      (mv sat? t prop))))

(defthm bfr-sat-bdd-unsat
  (mv-let (sat succeeded ctrex)
    (bfr-sat-bdd prop)
    (declare (ignore ctrex))
    (implies (and succeeded (not sat))
             (not (bfr-eval prop env))))
  :hints(("Goal" :in-theory (e/d (bfr-eval)
                                 (acl2::eval-bdd-ubdd-fix))
          :use ((:instance acl2::eval-bdd-ubdd-fix
                           (x prop))))))


(acl2::defattach
 (bfr-sat bfr-sat-bdd
          :hints (("goal" :in-theory '(bfr-sat-bdd-unsat)))))

(in-theory (disable bfr-sat-bdd-unsat bfr-sat-unsat))



;; In the AIG case, the counterexample returned is either an alist giving a
;; single satisfying assignment or a BDD giving the full set of satisfying
;; assignments.
(defstub bfr-counterex-mode () t)
(defun bfr-counterex-alist ()
  (declare (Xargs :guard t))
  t)
(defun bfr-counterex-bdd ()
  (declare (xargs :guard t))
  nil)

(acl2::defattach bfr-counterex-mode bfr-counterex-bdd)


;; Given a non-NIL BDD, generates a satisfying assignment (a list of Booleans
;; corresponding to the decision levels.)  The particular satisfying assignment
;; chosen is determined by the sequence of bits in the LST argument.
(defun to-satisfying-assign (lst bdd)
  (declare (xargs :hints (("goal" :in-theory (enable acl2-count)))))
  (cond ((atom bdd) lst)
        ((eq (cdr bdd) nil) (cons t (to-satisfying-assign  lst (car bdd))))
        ((eq (car bdd) nil) (cons nil (to-satisfying-assign  lst (cdr bdd))))
        (t (cons (car lst) (to-satisfying-assign
                            (cdr lst)
                            (if (car lst) (car bdd) (cdr bdd)))))))

(defthm to-satisfying-assign-correct
  (implies (and bdd (acl2::ubddp bdd))
           (acl2::eval-bdd bdd (to-satisfying-assign lst bdd)))
  :hints(("Goal" :in-theory (enable acl2::eval-bdd acl2::ubddp))))

(defun bfr-ctrex-to-satisfying-assign (assign ctrex)
  (if (eq (bfr-counterex-mode) t) ;; alist
      ctrex
    (to-satisfying-assign assign ctrex)))





(defund bfr-known-value (x)
  (declare (xargs :guard t))
  (bfr-case :bdd (and x t)
            :aig (acl2::aig-eval x nil)))


(defsection bfr-constcheck
  ;; Bfr-constcheck: use SAT (or examine the BDD) to determine whether x is
  ;; constant, and if so return that constant.
  (defund bfr-constcheck (x)
    (declare (xargs :guard t))
    (if (bfr-known-value x)
        (b* (((mv sat ok &) (bfr-sat (bfr-not x))))
          (if (or sat (not ok))
              x
            t))
      (b* (((mv sat ok &) (bfr-sat x)))
        (if (or sat (not ok))
            x
          nil))))

  (local (in-theory (enable bfr-constcheck)))

  (defthm bfr-eval-of-bfr-constcheck
    (equal (bfr-eval (bfr-constcheck x) env)
           (bfr-eval x env))
    :hints (("goal" :use ((:instance bfr-sat-unsat
                           (prop x))
                          (:instance bfr-sat-unsat
                           (prop (bfr-not x)))))))

  (defthm pbfr-depends-on-of-bfr-constcheck
    (implies (not (pbfr-depends-on k p x))
             (not (pbfr-depends-on k p (bfr-constcheck x))))))

(defsection bfr-constcheck-pathcond
  ;; Bfr-constcheck: use SAT (or examine the BDD) to determine whether x is
  ;; constant, and if so return that constant.
  (defund bfr-constcheck-pathcond (x pathcond)
    (declare (xargs :guard t))
    (b* (((mv sat ok &) (bfr-sat (bfr-and pathcond x)))
         ((unless (or sat (not ok)))
          nil)
         ((mv sat ok &) (bfr-sat (bfr-and pathcond (bfr-not x))))
         ((unless (or sat (not ok)))
          t))
      x))

  (local (in-theory (enable bfr-constcheck-pathcond)))

  (defthm bfr-eval-of-bfr-constcheck-pathcond
    (implies (bfr-eval pathcond env)
             (equal (bfr-eval (bfr-constcheck-pathcond x pathcond) env)
                    (bfr-eval x env)))
    :hints (("goal" :use ((:instance bfr-sat-unsat
                           (prop (bfr-and pathcond x)))
                          (:instance bfr-sat-unsat
                           (prop (bfr-and pathcond (bfr-not x))))))))

  (defthm pbfr-depends-on-of-bfr-constcheck-pathcond
    (implies (not (pbfr-depends-on k p x))
             (not (pbfr-depends-on k p (bfr-constcheck-pathcond x pathcond))))))


(defsection bfr-check-true
  ;; Bfr-constcheck: use SAT (or examine the BDD) to determine whether x is
  ;; constant, and if so return that constant.
  (defund bfr-check-true (x)
    (declare (xargs :guard t))
    (if (bfr-known-value x)
        (b* (((mv sat ok &) (bfr-sat (bfr-not x))))
          (if (or sat (not ok))
              x
            t))
      x))

  (local (in-theory (enable bfr-check-true)))

  (defthm bfr-eval-of-bfr-check-true
    (equal (bfr-eval (bfr-check-true x) env)
           (bfr-eval x env))
    :hints (("goal" :use ((:instance bfr-sat-unsat
                           (prop x))
                          (:instance bfr-sat-unsat
                           (prop (bfr-not x)))))))

  (defthm pbfr-depends-on-of-bfr-check-true
    (implies (not (pbfr-depends-on k p x))
             (not (pbfr-depends-on k p (bfr-check-true x))))))

(defsection bfr-check-false
  ;; Bfr-constcheck: use SAT (or examine the BDD) to determine whether x is
  ;; constant, and if so return that constant.
  (defund bfr-check-false (x)
    (declare (xargs :guard t))
    (if (bfr-known-value x)
        x
      (b* (((mv sat ok &) (bfr-sat x)))
        (if (or sat (not ok))
            x
          nil))))

  (local (in-theory (enable bfr-check-false)))

  (defthm bfr-eval-of-bfr-check-false
    (equal (bfr-eval (bfr-check-false x) env)
           (bfr-eval x env))
    :hints (("goal" :use ((:instance bfr-sat-unsat
                           (prop x))
                          (:instance bfr-sat-unsat
                           (prop (bfr-not x)))))))

  (defthm pbfr-depends-on-of-bfr-check-false
    (implies (not (pbfr-depends-on k p x))
             (not (pbfr-depends-on k p (bfr-check-false x))))))

