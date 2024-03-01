; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
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

(in-package "SV")

(include-book "rewrite")
(include-book "env-ops")
(local (include-book "clause-processors/find-subterms" :dir :system))



(defun-sk svex-envs-agree-on-masks (masks env1 env2)
  (forall var
          (let ((mask (svex-mask-lookup (svex-var var) masks)))
            (equal (4vec-mask mask
                              (svex-env-lookup var env1))
                   (4vec-mask mask
                              (svex-env-lookup var env2)))))
  :rewrite :direct)

(in-theory (disable svex-envs-agree-on-masks))

(defthm svex-envs-agree-on-masks-implies-var
  (implies (and (svex-envs-agree-on-masks masks env1 env2)
                (svex-case x :var))
           (let* ((mask (svex-mask-lookup x masks))
                  (name (svex-var->name x)))
             (equal (4vec-mask mask (svex-env-lookup name env1))
                    (4vec-mask mask (svex-env-lookup name env2)))))
  :hints (("goal" :use ((:instance svex-envs-agree-on-masks-necc
                         (var (svex-var->name x))))
           :in-theory (disable svex-envs-agree-on-masks-necc))))


(local (defthm svex-argmasks-okp-apply
         (implies (and (svex-case x :call)
                       (equal (4veclist-mask argmasks (svexlist-eval (svex-call->args x) env))
                              (4veclist-mask argmasks vals))
                       (svex-argmasks-okp x mask argmasks))
                  (equal (equal (4vec-mask mask (svex-apply (svex-call->fn x)
                                                            (svexlist-eval (svex-call->args x) env)))
                                (4vec-mask mask (svex-apply (svex-call->fn x)
                                                            vals)))
                         t))
         :hints (("goal" :use ((:instance svex-argmasks-okp-necc))
                  :expand ((svex-eval x env))
                  :in-theory (disable svex-argmasks-okp-necc)))))

(local (in-theory (enable svex-mask-alist-complete-necc)))

(defthm-svex-eval-flag svex-envs-agree-on-masks-implies-eval-when-svex-mask-alist-complete
  (defthm svex-envs-agree-on-masks-implies-svex-eval-when-svex-mask-alist-complete
    (implies (And (svex-envs-agree-on-masks masks env1 env2)
                  (svex-mask-alist-complete masks))
             (let ((mask (svex-mask-lookup x masks)))
               (equal (4vec-mask mask (svex-eval x env1))
                      (4vec-mask mask (svex-eval x env2)))))
    :hints ('(:expand ((:free (env) (svex-eval x env)))))
    :flag expr)
  (defthm svex-envs-agree-on-masks-implies-svexlist-eval-when-svex-mask-alist-complete
    (implies (And (svex-envs-agree-on-masks masks env1 env2)
                  (svex-mask-alist-complete masks))
             (let ((mask (svex-argmasks-lookup x masks)))
               (equal (4veclist-mask mask (svexlist-eval x env1))
                      (4veclist-mask mask (svexlist-eval x env2)))))
    :hints ('(:expand ((:free (env) (svexlist-eval x env))
                       (svex-argmasks-lookup x masks)
                       (:free (a b c d) (4veclist-mask (cons a b) (cons c d))))))
    :flag list))



(defcong svex-envs-similar iff (svex-envs-agree-on-masks masks env1 env2) 2
  :hints ((and stable-under-simplificationp
               (let ((lit (assoc 'svex-envs-agree-on-masks clause)))
                 `(:computed-hint-replacement
                   ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                      (and var
                           `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var)))))))
                   :expand (,lit))))))

(defcong svex-envs-similar iff (svex-envs-agree-on-masks masks env1 env2) 3
  :hints ((and stable-under-simplificationp
               (let ((lit (assoc 'svex-envs-agree-on-masks clause)))
                 `(:computed-hint-replacement
                   ((let ((var (acl2::find-call-lst 'svex-envs-agree-on-masks-witness clause)))
                      (and var
                           `(:clause-processor (acl2::generalize-with-alist-cp clause '((,var . var)))))))
                   :expand (,lit))))))

(defthm svex-envs-agree-on-masks-refl
  (svex-envs-agree-on-masks masks x x)
  :hints(("Goal" :in-theory (enable svex-envs-agree-on-masks))))
