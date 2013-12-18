; Centaur BED Library
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

(in-package "BED")
(include-book "ops")

(define bed-env-lookup ((var atom) env)
  (b* (((when (or (eq var t)
                  (eq var nil)))
        ;; Goofy restriction to agree with aig-eval
        var)
       (look (hons-get var env))
       ((unless look)
        ;; Goofy default value agrees with aig-env-lookup
        t))
    (cdr look))
  ///
  (defthm bed-env-lookup-of-nil
    (equal (bed-env-lookup nil env)
           nil))
  (defthm bed-env-lookup-of-t
    (equal (bed-env-lookup t env)
           t)))

(define bed-eval ((x   "BED to evaluate")
                  (env "Fast alist mapping variables to Booleans (t/nil)"))
  :returns (bit bitp)
  :parents (bed)
  :short "Semantics of BEDs."
  :verify-guards nil
  (b* (((when (atom x))
        (if x 1 0))
       ((cons a b) x)

       ((when (atom a))
        ;; Variable node -- lazily evaluate whichever branch we need.
        (if (bed-env-lookup a env)
            (bed-eval (car$ b) env)
          (bed-eval (cdr$ b) env)))

       ;; Operator node, we'll evaluate both branches
       (op    (bed-op-fix b))
       (left  (bed-eval (car$ a) env))
       (right (bed-eval (cdr$ a) env)))
    (bed-op-eval op left right))
  ///
  (verify-guards bed-eval)
  (memoize 'bed-eval :condition '(consp x))

  (defthm bed-eval-when-atom
    (implies (atom x)
             (equal (bed-eval x env)
                    (if x 1 0))))

  (defthm bed-eval-of-var
    (implies (and (consp x)
                  (atom (car x)))
             (equal (bed-eval x env)
                    (if (bed-env-lookup (car x) env)
                        (bed-eval (car (cdr x)) env)
                      (bed-eval (cdr (cdr x)) env)))))

  (defthm bed-eval-when-known-op
    (implies (and (equal (bed-op-fix op) fixed-op)
                  (consp leftright))
             (equal (bed-eval (cons leftright op) env)
                    (bed-op-eval fixed-op
                                 (bed-eval (car leftright) env)
                                 (bed-eval (cdr leftright) env))))))
