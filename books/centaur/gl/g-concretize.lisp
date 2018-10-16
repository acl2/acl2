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
(include-book "bfr-sat")
(include-book "gl-mbe")
(include-book "g-primitives-help")
(include-book "g-if")
(include-book "eval-g-base")
(include-book "ctrex-utils")
(include-book "g-equal")
(local (include-book "hyp-fix"))
(local (include-book "eval-g-base-help"))



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
       ((g-integer bits)
        (mv t (bfr-list->s (list-fix bits) (car env))))
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
                               eval-g-base-alt-def
                               general-concretep-def
                               general-concrete-obj-when-atom))))
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
        ((acl2::with-fast assign))
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
