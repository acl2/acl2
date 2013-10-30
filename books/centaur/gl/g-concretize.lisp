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
(include-book "bfr-sat")
(include-book "gl-mbe")
(include-book "g-primitives-help")
(include-book "g-if")
(include-book "eval-g-base")
(include-book "ctrex-utils")
(local (include-book "hyp-fix"))
(local (include-book "eval-g-base-help"))

(include-book "g-equal")

(mutual-recursion
 (defun eval-g-base-or-err (x env)
   (declare (xargs :guard (consp env)
                   :measure (acl2-count x)
                   :verify-guards nil
                   :hints (("goal" :in-theory '(measure-for-geval atom)))))
   (if (atom x)
       (mv t x)
     (pattern-match x
       ((g-concrete obj) (mv t obj))
       ((g-boolean bool) (mv t (bfr-eval bool (car env))))
       ((g-number num)
        (b* (((mv real-num
                  real-denom
                  imag-num
                  imag-denom)
              (break-g-number num)))
          (flet ((uval (n env)
                       (bfr-list->u n (car env)))
                 (sval (n env)
                       (bfr-list->s n (car env))))
            (mv t (components-to-number (sval real-num env)
                                        (uval real-denom env)
                                        (sval imag-num env)
                                        (uval imag-denom env))))))
       ((g-ite test then else)
        (b* (((mv ok test) (eval-g-base-or-err test env))
             ((unless ok) (mv nil nil)))
          (if test
              (eval-g-base-or-err then env)
            (eval-g-base-or-err else env))))

       ((g-apply fn args)
        (b* (((when (eq fn 'quote)) (mv nil nil))
             ((mv ok args) (eval-g-base-or-err-list args env))
             ((unless ok) (mv nil nil))
             (args (acl2::list-fix args)))
          (eval-g-base-apply fn args)))

       ((g-var name) (mv t (cdr (hons-get name (cdr env)))))

       (& (b* (((mv ok car) (eval-g-base-or-err (car x) env))
               ((unless ok) (mv nil nil))
               ((mv ok cdr) (eval-g-base-or-err (cdr x) env))
               ((unless ok) (mv nil nil)))
            (mv t (cons car cdr)))))))

 (defun eval-g-base-or-err-list (x env)
   (declare (xargs :guard (consp env)
                   :measure (acl2-count x)))
   (if (atom x)
       (mv t nil)
     (b* (((mv ok car) (eval-g-base-or-err (car x) env))
          ((unless ok) (mv nil nil))
          ((mv ok cdr) (eval-g-base-or-err-list (cdr x) env))
          ((unless ok) (mv nil nil)))
       (mv t (cons car cdr))))))

(verify-guards eval-g-base-or-err)

(defthm-gobj-flag
  (defthm eval-g-base-or-err-correct
    (b* (((mv ok res) (eval-g-base-or-err x env)))
      (implies ok
               (equal res (eval-g-base x env))))
    :hints ('(:expand ((:with eval-g-base (eval-g-base x env)))
              :in-theory (e/d (eval-g-base-apply-agrees-with-eval-g-base-ev)
                              (eval-g-base-apply
                                  eval-g-base-alt-def))))
    :flag gobj)
  (defthm eval-g-base-or-err-list-correct
    (b* (((mv ok res) (eval-g-base-or-err-list x env)))
      (implies ok
               (equal res (eval-g-base-list x env))))
    :hints ('(:expand ((eval-g-base-list x env))))
    :flag list))

(in-theory (disable eval-g-base-or-err))

(def-g-fn gl-concretize$inline
  `(b* (((unless (bfr-mode))
         ;; identity in bdd mode
         (gret x))
        (hyp-bfr (bfr-hyp->bfr hyp))
        ((mv hyp-sat hyp-succ assign) (bfr-sat hyp-bfr))
        ((unless (and hyp-succ hyp-sat))
         (cw "Note: Failed to find satisfying assignment for path cond~%")
         (gret x))
        ((with-fast assign))
        ((mv ok xconc) (eval-g-base-or-err x (cons assign nil)))
        ((unless ok)
         (cw "Note: Failed to concretize ~x0~%" (gobj-abstract-top x))
         (gret x))
        ;; (- (cw "Note: concretize try: ~x0~%" xconc))
        (xconc (g-concrete-quote xconc))
        ((gret eq) (glc equal x xconc))
        ((mv eq-nonnil eq-unknown & hyp) (gtests eq hyp))
        (prop (bfr-and (bfr-hyp->bfr hyp)
                       (bfr-or eq-unknown
                               (bfr-not eq-nonnil))))
        ((mv false-sat false-succ ?false-ctrex)
         (bfr-sat prop))
        ((when (and false-succ (not false-sat)))
         (gret xconc)))
     (cw "Note: Failed to concretize ~x0~%" (gobj-abstract-top x))
     (gret x)))

(verify-g-guards gl-concretize$inline)


(def-gobj-dependency-thm gl-concretize$inline
  :hints `(("goal"
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))


(local
 (defun instantiate-bfr-sat-hint (clause env)
   (if (atom clause)
       nil
     (let ((lit (car clause)))
       (case-match lit
         (('mv-nth ''0 ('bfr-sat term))
          (cons `(:instance bfr-sat-unsat
                            (prop ,term)
                            (env ,env))
                (instantiate-bfr-sat-hint (cdr clause) env)))
         (& (instantiate-bfr-sat-hint (cdr clause) env)))))))

(def-g-correct-thm gl-concretize$inline eval-g-base
  :hints `(("goal" :do-not-induct t
            :expand (,gcall)
            :in-theory (disable bfr-sat-unsat))
           (and stable-under-simplificationp
                (let ((insts (instantiate-bfr-sat-hint clause '(car env))))
                  (if insts
                      `(:use ,insts)
                    (cw "clause: ~x0~%" clause))))))
