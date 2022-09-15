; SV - Symbolic Vector Hardware Analysis Framework
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "compose-theory-base")
(include-book "fixpoint-eval")
(local (include-book "alist-thms"))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (in-theory (disable hons-dups-p)))


(encapsulate nil
  (local (defthm svex-alist-eval-when-equiv-compose
           (implies (svex-alist-eval-equiv x (svex-alist-compose y z))
                    (svex-envs-equivalent (svex-alist-eval x env)
                                          (svex-alist-eval y (append (svex-alist-eval z env) env))))))
  
  (defthmd eval-when-netevalcomp-p
    (implies (netevalcomp-p comp network)
             (svex-envs-equivalent (svex-alist-eval comp env)
                                   (neteval-ordering-eval
                                    (netevalcomp-p-witness comp network)
                                    network
                                    (append (svarlist-x-env (svex-alist-keys network)) env))))
    :hints (("goal" :expand ((netevalcomp-p comp network))))))



(defsection neteval-ordering-eval-<<=-fixpoint
  

  (local (in-theory (disable bitops::logbitp-when-bit
                             bitops::logior-<-0-linear-2
                             bitops::lognot-natp
                             bitops::logbitp-nonzero-of-bit
                             bitops::logbitp-when-bitmaskp)))
  
  (local (defthm extract-similar-to-nil-implies-lookup
           (implies (and (svex-envs-similar (svex-env-extract keys env) nil)
                         (member-equal (svar-fix v) (svarlist-fix keys)))
                    (equal (svex-env-lookup v env) (4vec-x)))
           :hints (("goal" :use ((:instance svex-env-lookup-of-svex-env-extract
                                  (vars keys)))
                    :in-theory (disable svex-env-lookup-of-svex-env-extract)))))

  (local (defthm append-neteval-ordering-eval-env-is-append-extract
           (implies (svex-envs-similar (svex-env-extract (svex-alist-keys network) env) nil)
                    (svex-envs-similar (append (neteval-ordering-eval x network env) env)
                                       (append (svex-env-extract (svex-alist-keys network)
                                                                 (neteval-ordering-eval x network env))
                                               env)))
           :hints(("goal" :in-theory (e/d (lookup-signal-not-in-network-of-neteval-ordering-eval)
                                          (SVEX-ENV-LOOKUP-OF-NETEVAL-ORDERING-EVAL)))
                  (and stable-under-simplificationp
                       `(:expand (,(car (last clause)))))
                  (and stable-under-simplificationp
                       '(:in-theory (enable SVEX-ENV-LOOKUP-OF-NETEVAL-ORDERING-EVAL))))))

  (local (defthm eval-lookup-of-extract
           (equal (svex-eval (svex-lookup signal network)
                             (append (svex-env-extract (svex-alist-keys network) env1) env2))
                  (svex-env-lookup signal (svex-alist-eval-fixpoint-step network env1 env2)))
           :hints(("Goal" :in-theory (enable svex-alist-eval-fixpoint-step)))))

  (local (defthm 4vec-rsh-when-zp
           (implies (zip offset)
                    (equal (4vec-rsh (2vec offset) x)
                           (4vec-fix x)))
           :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core)))))
  
  (local (defthm 4vec-<<=-of-4vec-rsh
           (implies (4vec-<<= x y)
                    (4vec-<<= (4vec-rsh n x) (4vec-rsh n y)))
           :hints(("Goal" :in-theory (enable 4vec-<<= 4vec-rsh 4vec-shift-core))
                  (bitops::logbitp-reasoning
                   :simp-hint (:in-theory (enable* logbitp-case-splits))
                   :add-hints (:in-theory (enable* logbitp-case-splits))))))

  (local (defthm 4vec-<<=-of-4vec-concat
           (implies (and (2vec-p w)
                         (natp (2vec->val w))
                         (4vec-<<= x z)
                         (4vec-<<= y (4vec-rsh w z)))
                    (4vec-<<= (4vec-concat w x y) z))
           :hints(("Goal" :in-theory (enable 4vec-<<= 4vec-rsh 4vec-shift-core 4vec-concat))
                  (bitops::logbitp-reasoning
                   :simp-hint (:in-theory (enable* logbitp-case-splits))
                   :add-hints (:in-theory (enable* logbitp-case-splits))))))

  (local (defthm svex-env-extract-nil-under-svex-envs-similar
           (svex-envs-similar (svex-env-extract keys nil) nil)
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))

  (local (defthm svex-env-extract-cons-non-member
           (implies (not (member-equal v (svarlist-fix vars)))
                    (equal (svex-env-extract vars (cons (cons v expr) rest))
                           (svex-env-extract vars rest)))
           :hints(("Goal" :in-theory (enable svex-env-extract
                                             svex-env-lookup-of-cons)))))


  (local (Defthm svex-env-<<=-extract-cons-lemma
           (implies (and (4vec-<<= val (svex-env-lookup key fixpoint))
                         (svex-env-<<= (svex-env-extract keys rest) fixpoint))
                    (svex-env-<<= (svex-env-extract keys (cons (cons key val) rest)) fixpoint))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause)))
                          :in-theory (enable svex-env-lookup-of-cons-split)
                          :use ((:instance svex-env-<<=-necc
                                 (x (svex-env-extract keys rest)) (y fixpoint)
                                 (var (svex-env-<<=-witness . ,(cdar (last clause)))))))))))
  
  (defthm-neteval-ordering-compile-flag neteval-ordering-eval-<<=-fixpoint
    (defthm neteval-ordering-eval-<<=-fixpoint
      (implies (and (svex-alist-width network)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    ;; env binds all keys of network to X
                    (svex-envs-similar (svex-env-extract (svex-alist-keys network) env) nil))
               (svex-env-<<= (svex-env-extract (svex-alist-keys network) (neteval-ordering-eval x network env))
                             (svex-alist-eval-least-fixpoint network env)))
      :hints ('(:expand ((neteval-ordering-eval x network env))))
      :flag neteval-ordering-compile)
    (defthm neteval-sigordering-eval-<<=-fixpoint
      (implies (and (svex-alist-width network)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    ;; env binds all keys of network to X
                    (svex-envs-similar (svex-env-extract (svex-alist-keys network) env) nil)
                    (svex-lookup signal network))
               (4vec-<<= (neteval-sigordering-eval x signal offset network env)
                         (4vec-rsh (2vec (nfix offset)) (svex-env-lookup signal (svex-alist-eval-least-fixpoint network env)))))
      :hints ('(:expand ((neteval-sigordering-eval x signal offset network env))))
      :flag neteval-sigordering-compile)
    (defthm neteval-ordering-or-nul-eval-<<=-fixpoint
      (implies (and (svex-alist-width network)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    ;; env binds all keys of network to X
                    (svex-envs-similar (svex-env-extract (svex-alist-keys network) env) nil)
                    (svex-lookup signal network))
               (4vec-<<= (neteval-ordering-or-null-eval x signal network env)
                         (svex-env-lookup signal (svex-alist-eval-least-fixpoint network env))))
      :hints ('(:expand (neteval-ordering-or-null-eval x signal network env))
              (and stable-under-simplificationp
                   '(:use ((:instance svex-alist-eval-fixpoint-step-monotonic
                            (x network)
                            (env1 (svex-env-extract (svex-alist-keys network)
                                                    (neteval-ordering-eval (neteval-ordering-or-null-ordering->ord x) network env)))
                            (env2 (svex-alist-eval-least-fixpoint network env))
                            (in-env env)))
                     :in-theory (disable svex-alist-eval-fixpoint-step-monotonic))))
      :flag neteval-ordering-or-null-compile))

  (local (defthm svex-alist-keys-when-equiv-compose
           (implies (svex-alist-eval-equiv x (svex-alist-compose y z))
                    (set-equiv (svex-alist-keys x)
                               (svex-alist-keys y)))))
  
  (local (defthm alist-keys-of-netevalcomp-p-witness-when-netevalcomp-p
           (implies (netevalcomp-p comp network)
                    (set-equiv (alist-keys (neteval-ordering-fix (netevalcomp-p-witness comp network)))
                               (svex-alist-keys comp)))
           :hints(("Goal" :in-theory (enable netevalcomp-p)))))

  (local (defun induct-down-neteval-ordering (x)
           (declare (xargs :measure (neteval-ordering-count x)))
           (if (atom (neteval-ordering-fix x))
               x
             (induct-down-neteval-ordering (cdr (neteval-ordering-fix x))))))
  
  (local (defthm alist-keys-of-neteval-ordering-eval
           (equal (alist-keys (neteval-ordering-eval x network env))
                  (alist-keys (neteval-ordering-fix x)))
           :hints (("goal" :induct (induct-down-neteval-ordering x)
                    :in-theory (enable alist-keys)
                    :expand ((neteval-ordering-eval x network env))))))


  (local (defthm svex-envs-similar-append-extract-svarlist-x-env
           (svex-envs-similar (append (svex-env-extract keys env1) (svarlist-x-env keys) env2)
                              (append (svex-env-extract keys env1) env2))
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))
  
  (local (defthm svex-alist-eval-fixpoint-step-of-append-svarlist-x-env
           (equal (svex-alist-eval-fixpoint-step x env (append (svarlist-x-env (svex-alist-keys x)) in-env))
                  (svex-alist-eval-fixpoint-step x env in-env))
           :hints(("Goal" :in-theory (enable svex-alist-eval-fixpoint-step)))))

  (local (defthm svex-alist-eval-fixpoint-iterate-of-append-svarlist-x-env
           (equal (svex-alist-eval-fixpoint-iterate n x env (append (svarlist-x-env (svex-alist-keys x)) in-env))
                  (svex-alist-eval-fixpoint-iterate n x env in-env))
           :hints(("Goal" :in-theory (enable svex-alist-eval-fixpoint-iterate)))))

  (local (defthm svex-alist-eval-least-fixpoint-of-append-svarlist-x-env
           (equal (svex-alist-eval-least-fixpoint x (append (svarlist-x-env (svex-alist-keys x)) in-env))
                  (svex-alist-eval-least-fixpoint x in-env))
           :hints(("Goal" :in-theory (enable svex-alist-eval-least-fixpoint)))))

  (local (defthm svex-env-extract-append-x-env
           (implies (set-equiv (svarlist-fix keys) (svarlist-fix keys1))
                    (svex-envs-similar (svex-env-extract keys (append (svarlist-x-env keys1) env))
                                       nil))
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))
  
  (defthm netevalcomp-p-implies-<<=-fixpoint
    (implies (and (svex-alist-width network)
                  (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                  (no-duplicatesp-equal (svex-alist-keys network))
                  (netevalcomp-p comp network)
                  (set-equiv (svex-alist-keys comp) (svex-alist-keys network)))
             (svex-alist-<<= comp (svex-alist-least-fixpoint network)))
    :hints(("Goal" :in-theory (e/d (svex-alist-<<=
                                    eval-when-netevalcomp-p)
                                   (neteval-ordering-eval-<<=-fixpoint))
            :use ((:instance neteval-ordering-eval-<<=-fixpoint
                   (env (append (svarlist-x-env (svex-alist-keys network))
                                (svex-alist-<<=-witness comp (svex-alist-least-fixpoint network))))
                   (x (netevalcomp-p-witness comp network))))))))


