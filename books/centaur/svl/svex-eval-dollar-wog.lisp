; Copyright (C) 2022 Intel Corporation
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
; Original author: Mertcan Temel <mert.temel@intel.com>


;; Alternative definitions for SVEX-EVAL WITHOUT ANY GUARDS down to 4vec functions

(in-package "SVL")

(include-book "centaur/sv/svex/eval" :dir :system)
(include-book "centaur/sv/svex/eval-dollar" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "projects/rp-rewriter/top" :dir :system)
(include-book "macros")
(include-book "svex-eval-wog")


(local
 (in-theory (enable hons-get)))

(define 4veclist-fix-wog (lst)
  (if (atom lst)
      nil
    (cons (4vec-fix-wog (car lst))
          (4veclist-fix-wog (cdr lst))))
  ///
  (def-rp-rule 4veclist-fix-wog-is-4veclist-fix
    (equal (4veclist-fix-wog x)
           (sv::4veclist-fix x))))

(defmacro svex-apply$-cases-wog (fn args)
  `(case ,fn
     ,@(take (len sv::*svex-op-table*) (svex-apply-cases-fn-wog args sv::*svex-op-table*))
     (otherwise
      (b* ((res (apply$ ,fn (4veclist-fix-wog ,args))))
        (if (4vec-p res)
            res
          (sv::4vec-x))))))

(define svex-apply$-wog (fn (args true-listp))
  :returns
  (sv::result 4vec-p
              "result of applying the function.")
  (let* ((fn (fnsym-fix fn)))
    (svex-apply$-cases-wog fn args)))

(def-rp-rule :disabled-for-acl2 t
  svex-apply$-is-svex-apply$-wog
  (equal (sv::svex-apply$ fn args)
         (svex-apply$-wog fn args))
  :hints (("goal"
           :expand ((:free (index)
                           (nth index (sv::4veclist-fix args)))
                    (:free (index)
                           (nth index (sv::4veclist-fix (cdr args)))))
           :in-theory (e/d (svex-apply$-wog
                            sv::4veclist-fix
                            nth
                            4veclist-nth-safe
                            sv::svex-apply$)
                           (sv::4vec-fix-under-4vec-equiv
                            (:definition ifix)
                            (:rewrite sv::4vec-fix-of-4vec)
                            (:definition integer-listp)
                            (:rewrite sv::4vec-p-of-nth-when-4veclist-p)
                            (:type-prescription integer-listp)
                            (:rewrite sv::nth-of-4veclist-fix))))))

(acl2::defines
  svex-eval$-wog
  :flag svex-eval$-wog-flag
  :flag-defthm-macro defthm-svex-eval$-wog
  :verify-guards nil
  :flag-local nil

  (define svex-eval$-wog (x env)
    :measure (cons-count x)
    :hints (("Goal"
             :in-theory (e/d (rp::measure-lemmas
                              svex-kind-wog
                              svex-kind) ())))
    :flag expr
    :returns (val 4vec-p "Value of @('x') under this environment."
                  :hyp (and (sv::svex-env-p env)
                            (sv::svex-p x))
                  :hints ((and stable-under-simplificationp
                               '(:expand ((4vec-p x))))))
    (let* ((x.kind (svex-kind-wog x)))
      (case
        x.kind
        (:quote x)
        (:var (svex-env-fastlookup-wog x env))
        (otherwise
         (b* ((x.fn (car x))
              (x.args (cdr x)))
           (svex-apply$-wog x.fn (svexlist-eval$-wog x.args env)))))))

  (define svexlist-eval$-wog (args env)
    :returns (vals sv::4veclist-p "Values of the expressions in @('x') under
    this environment."
                   :hyp (and (sv::svex-env-p env)
                             (sv::svexlist-p args)))
    :measure (cons-count args)
    :flag list
    (if (atom args)
        nil
      (cons (svex-eval$-wog (car args) env)
            (svexlist-eval$-wog (cdr args) env)))
    ///
    (acl2::more-returns
     (vals true-listp)))

  :prepwork
  ((local
    (defthm returns-lemma
      (implies (and
                (equal (svex-kind-wog x) :quote)
                (svex-p x))
               (4vec-p x))
      :hints (("goal"
               :in-theory (e/d (svex-kind-wog svex-p 4vec-p) ())))))
   )
  ///

  (local
   (in-theory (enable SVEX-KIND-WOG)))

  (local (defthm consp-of-svexlist-eval$
           (equal (consp (svexlist-eval$-wog x env))
                  (consp x))
           :hints (("goal" :expand ((svexlist-eval$-wog x env))))))

  (local (defthm upper-lower-of-3vec-fix
           (implies (and (sv::3vec-p x)
                         (not (equal (sv::4vec->lower x) 0)))
                    (not (equal (sv::4vec->upper x) 0)))
           :hints(("Goal" :in-theory (enable sv::3vec-p)))))

  (local (defthm 4vec-?-cases
           (and (implies (equal (sv::4vec->upper (sv::3vec-fix test)) 0)
                         (equal (sv::4vec-? test then else)
                                (4vec-fix else)))
                (implies (not (equal (sv::4vec->lower (sv::3vec-fix test)) 0))
                         (equal (sv::4vec-? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable sv::4vec-? sv::3vec-?)))))

  (local (defthm 4vec-bit?-cases
           (and (implies (equal test 0)
                         (equal (sv::4vec-bit? test then else)
                                (4vec-fix else)))
                (implies (equal test -1)
                         (equal (sv::4vec-bit? test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable sv::4vec-bit? sv::3vec-bit?)))))

  (local (defthm 4vec-?*-cases
           (and (implies (equal (sv::4vec->upper (sv::3vec-fix test)) 0)
                         (equal (4vec-?* test then else)
                                (4vec-fix else)))
                (implies (not (equal (sv::4vec->lower (sv::3vec-fix test)) 0))
                         (equal (4vec-?* test then else)
                                (4vec-fix then))))
           :hints(("Goal" :in-theory (enable 4vec-?* sv::3vec-?*)))))

  (local (defthm 4vec-bitand-case
           (implies (equal test 0)
                    (equal (4vec-bitand test x)
                           0))
           :hints(("Goal" :in-theory (enable 4vec-bitand 3vec-bitand)))))

  (local (defthm 4vec-bitor-case
           (implies (equal test -1)
                    (equal (4vec-bitor test x)
                           -1))
           :hints(("Goal" :in-theory (enable 4vec-bitor sv::3vec-bitor)))))

  (verify-guards svex-eval$-wog
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (svex-apply$-wog len nth SVEX-KIND)
                                   (svex-eval$-wog))
                              :expand ((svexlist-eval$-wog (svex-call->args x) env)
                                       (svexlist-eval$-wog (cdr (svex-call->args x)) env)
                                       (svexlist-eval$-wog (cddr (svex-call->args x)) env))))))

  #|(memoize 'svex-eval$ :condition '(eq (svex-kind x) :call))||#)

(defthm-svex-eval$-wog
  (defthmd svex-eval$-wog-is-svex-eval$
    (implies (and (svex-p x)
                  (svex-env-p env))
             (equal (svex-eval$-wog x env)
                    (sv::svex-eval$ x env)))
    :flag expr)
  (defthmd svexlist-eval$-wog-is-svexlist-eval$
    (implies (and (sv::svexlist-p args)
                  (svex-env-p env))
             (equal (svexlist-eval$-wog args env)
                    (sv::svexlist-eval$ args env)))
    :flag list)
  :hints (("goal"
           :in-theory (e/d (svex-call->fn
                            svex-kind-wog
                            svex-kind
                            SVEX-APPLY$-IS-SVEX-APPLY$-WOG
                            svex-eval$-wog
                            svex-env-lookup-is-svex-env-fastlookup-wog
                            svexlist-eval$-wog
                            svex-p
                            sv::svar-p
                            sv::svex-eval$
                            svex-var->name
                            sv::svex-quote->val
                            svex-call->args) ()))))

(def-rp-rule :disabled-for-acl2 t
  svex-eval$-is-svex-eval$-wog
  (implies (and (force (svex-p x))
                (force (svex-env-p env)))
           (equal (sv::svex-eval$ x env)
                  (svex-eval$-wog x env)))
  :hints (("Goal"
           :in-theory (e/d (svex-eval$-wog-is-svex-eval$) ()))))

(def-rp-rule :disabled-for-acl2 t
  svexlist-eval$-is-svexlist-eval$-wog
  (implies (and (force (svexlist-p x))
                (force (svex-env-p env)))
           (equal (sv::svexlist-eval$ x env)
                  (svexlist-eval$-wog x env)))
  :hints (("Goal"
           :in-theory (e/d (svexlist-eval$-wog-is-svexlist-eval$) ()))))

(define svexlist-list-eval$-wog (x env)
  :returns (res 4vec-list-listp
                :hyp (and (sv::svex-env-p env)
                          (svex-list-listp x)))
  (if (atom x)
      nil
    (cons (svexlist-eval$-wog (car x) env)
          (svexlist-list-eval$-wog (cdr x) env))))
