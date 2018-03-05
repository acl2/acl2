; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "bfr")
(include-book "centaur/misc/hons-extra" :dir :system)
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

(defthmd bfr-sat-bdd-unsat
  (mv-let (sat succeeded ctrex)
    (bfr-sat-bdd prop)
    (declare (ignore ctrex))
    (implies (and succeeded (not sat))
             (not (bfr-eval prop env))))
  :hints(("Goal" :in-theory (e/d (bfr-eval)
                                 (acl2::eval-bdd-ubdd-fix))
          :use ((:instance acl2::eval-bdd-ubdd-fix
                           (x prop))))))


(acl2::defattach (bfr-sat bfr-sat-bdd)
  :hints (("goal" :in-theory '(bfr-sat-bdd-unsat))
          (and stable-under-simplificationp
               '(:in-theory (enable bfr-sat-bdd)))))

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
  (declare (xargs :hints (("goal" :in-theory (enable acl2-count)))
                  :guard (true-listp lst)))
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
  (declare (xargs :guard (true-listp assign)))
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
  ;; Returns (mv path-condition-satisfiable x'), where x' is equivalent to x
  ;; under the path condition.
  (defund bfr-constcheck (x pathcond)
    (declare (xargs :guard t))
    (if (eq pathcond t)
        (mv t ;; path condition sat
            (if (bfr-known-value x)
                (b* (((mv sat ok &) (bfr-sat (bfr-not x))))
                  (if (or sat (not ok))
                      x
                    t))
              (b* (((mv sat ok &) (bfr-sat x)))
                (if (or sat (not ok))
                    x
                  nil))))
      (b* (((mv sat ok ctrex) (bfr-sat pathcond))
           ((unless ok) (mv t x)) ;; failed -- conservative result
           ((unless sat) (mv nil nil)) ;; path condition unsat!
           (env (bfr-ctrex-to-satisfying-assign nil ctrex))
           ((acl2::with-fast env))
           (known-val (bfr-eval x env))
           ((mv sat ok &) (bfr-sat (bfr-and pathcond
                                            (if known-val
                                                ;; know x can be true, see if
                                                ;; it can be false under pathcond
                                                (bfr-not x)
                                              ;; know x can be false...
                                              x))))
           ((unless (or sat (not ok)))
            (mv t known-val)))
        (mv t x))))

  (local (in-theory (enable bfr-constcheck)))

  (defthmd bfr-constcheck-pathcond-unsat
    (b* (((mv ?pc-sat ?xx) (bfr-constcheck x pathcond)))
      (implies (not pc-sat)
               (not (bfr-eval pathcond env))))
    :hints(("Goal" :in-theory (enable bfr-sat-unsat))))

  (defthm bfr-eval-of-bfr-constcheck
    (b* (((mv ?pc-sat ?xx) (bfr-constcheck x pathcond)))
      (implies (bfr-eval pathcond env)
               (and pc-sat
                    (equal (bfr-eval xx env)
                           (bfr-eval x env)))))
    :hints (("goal" :use ((:instance bfr-sat-unsat
                           (prop (bfr-and pathcond x)))
                          (:instance bfr-sat-unsat
                           (prop (bfr-and pathcond (bfr-not x))))
                          (:instance bfr-sat-unsat
                           (prop x))
                          (:instance bfr-sat-unsat
                           (prop (bfr-not x)))
                          (:instance bfr-sat-unsat
                           (prop pathcond))))))

  (defthm pbfr-depends-on-of-bfr-constcheck
    (b* (((mv ?pc-sat ?xx) (bfr-constcheck x pathcond)))
      (implies (not (pbfr-depends-on k p x))
               (not (pbfr-depends-on k p xx))))))

(defsection bfr-check-true
  ;; Bfr-constcheck: use SAT (or examine the BDD) to determine whether x is
  ;; constant, and if so return that constant.
  (defund bfr-check-true (x pathcond)
    (declare (xargs :guard t))
    (if (eq pathcond t)
        (if (bfr-known-value x)
            (b* (((mv sat ok &) (bfr-sat (bfr-not x))))
              (if (or sat (not ok))
                  x
                t))
          x)
      (b* (((mv sat ok &) (bfr-sat (bfr-and pathcond (bfr-not x)))))
        (if (or sat (not ok))
            x
          t))))

  (local (in-theory (enable bfr-check-true)))

  (defthm bfr-eval-of-bfr-check-true
    (implies (bfr-eval pathcond env)
             (equal (bfr-eval (bfr-check-true x pathcond) env)
                    (bfr-eval x env)))
    :hints (("goal" :use ((:instance bfr-sat-unsat
                           (prop (bfr-not x)))
                          (:instance bfr-sat-unsat
                           (prop (bfr-and pathcond (bfr-not x))))))))

  (defthm pbfr-depends-on-of-bfr-check-true
    (implies (not (pbfr-depends-on k p x))
             (not (pbfr-depends-on k p (bfr-check-true x pathcond))))))

(defsection bfr-check-false
  ;; Bfr-constcheck: use SAT (or examine the BDD) to determine whether x is
  ;; constant, and if so return that constant.
  (defund bfr-check-false (x pathcond)
    (declare (xargs :guard t))
    (if (eq pathcond t)
        (if (bfr-known-value x)
            x
          (b* (((mv sat ok &) (bfr-sat x)))
            (if (or sat (not ok))
                x
              nil)))
      (b* (((mv sat ok &) (bfr-sat (bfr-and pathcond x))))
        (if (or sat (not ok))
            x
          nil))))

  (local (in-theory (enable bfr-check-false)))

  (defthm bfr-eval-of-bfr-check-false
    (implies (bfr-eval pathcond env)
             (equal (bfr-eval (bfr-check-false x pathcond) env)
                    (bfr-eval x env)))
    :hints (("goal" :use ((:instance bfr-sat-unsat
                           (prop x))
                          (:instance bfr-sat-unsat
                           (prop (bfr-and pathcond x)))))))

  (defthm pbfr-depends-on-of-bfr-check-false
    (implies (not (pbfr-depends-on k p x))
             (not (pbfr-depends-on k p (bfr-check-false x pathcond))))))

(defsection bfr-force-check
  ;; Returns (mv pathcond-sat x'), where x' is equivalent to x under the
  ;; pathcond.  But we only check the pathcond if direction is :both -- in the
  ;; other cases we assume it's satisfiable.
  (defund bfr-force-check (x pathcond direction)
    (declare (xargs :guard t))
    (case direction
      ((t) (mv t (bfr-check-true x pathcond)))
      ((nil) (mv t (bfr-check-false x pathcond)))
      (otherwise (bfr-constcheck x pathcond))))


  (local (in-theory (enable bfr-force-check)))

  (defthm bfr-eval-of-bfr-force-check
    (b* (((mv ?pc-sat ?xx) (bfr-force-check x pathcond dir)))
      (implies (bfr-eval pathcond env)
               (and pc-sat
                    (equal (bfr-eval xx env)
                           (bfr-eval x env)))))
    :hints (("goal" :use ((:instance bfr-sat-unsat
                           (prop x))
                          (:instance bfr-sat-unsat
                           (prop (bfr-and pathcond x)))))))

  (defthm pbfr-depends-on-of-bfr-force-check
    (b* (((mv ?pc-sat ?xx) (bfr-force-check x pathcond dir)))
      (implies (not (pbfr-depends-on k p x))
               (not (pbfr-depends-on k p xx))))))




;; Exactly the same constraint as bfr-sat, but can be attached to a different function if desired.
(encapsulate
  (((bfr-vacuity-check *) => (mv * * *)))

  (local (defun bfr-vacuity-check (prop)
           (declare (xargs :guard t))
           (mv nil nil prop)))

  (defthm bfr-vacuity-check-nvals
    (equal (len (bfr-vacuity-check prop)) 3))

  (defthm bfr-vacuity-check-true-listp
    (true-listp (bfr-vacuity-check prop)))

  (defthm bfr-vacuity-check-unsat
    (mv-let (sat succeeded ctrex)
      (bfr-vacuity-check prop)
      (declare (ignore ctrex))
      (implies (and succeeded (not sat))
               (not (bfr-eval prop env))))))

(defattach (bfr-vacuity-check
            bfr-sat)
  :hints (("goal" :use bfr-sat-unsat)))

(in-theory (disable bfr-vacuity-check-unsat
                    bfr-sat-unsat))
