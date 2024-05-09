; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "compose-theory-base")
(include-book "ovmonotonicity")
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "arithmetic/top" :Dir :system))
(local (include-book "alist-thms"))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))





(local (defthm alist-keys-of-neteval-ordering-eval
         (equal (alist-keys (neteval-ordering-eval x network env))
                (alist-keys (neteval-ordering-fix x)))
         :hints(("Goal" :in-theory (enable alist-keys)
                 :induct (neteval-ordering-selfinduct x)
                 :expand ((neteval-ordering-eval x network env))))))


;; (define svex-compose-alist-selfbound-keys-p ((keys svarlist-p)
;;                                              (x svex-alist-p))
;;   (if (atom keys)
;;       t
;;     (and (ec-call (svex-eval-equiv (svex-compose-lookup (car keys) x) (svex-var (car keys))))
;;          (svex-compose-alist-selfbound-keys-p (cdr keys) x)))
;;   ///
;;   (defthmd svex-compose-lookup-when-svex-compose-alist-selfbound-keys-p
;;     (implies (and (svex-compose-alist-selfbound-keys-p keys x)
;;                   (member-equal (svar-fix k) (svarlist-fix keys)))
;;              (svex-eval-equiv (svex-compose-lookup k x) (svex-var k)))))


(local (defthmd svex-eval-of-var
         (Equal (svex-eval (svex-var x) env)
                (svex-env-lookup x env))
         :hints(("Goal" :in-theory (enable svex-eval)))))

(defsection svex-envs-nonov-similar
  (defun-sk svex-envs-nonov-similar (x y)
    (forall v
            (and (implies (and (not (svar-override-p v :test))
                               (not (svar-override-p v :val)))
                          (equal (svex-env-lookup v x) (svex-env-lookup v y)))))
    :rewrite :direct)

  (in-theory (disable svex-envs-nonov-similar-necc
                      svex-envs-nonov-similar))

  (defequiv svex-envs-nonov-similar
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svar-override-p-when-other
                                      svex-envs-nonov-similar-necc)))))
  
  (defrefinement svex-envs-ovsimilar svex-envs-nonov-similar
    :hints(("Goal" :in-theory (enable svex-envs-nonov-similar)
            :use ((:instance svex-envs-ovsimilar-necc
                   (v (svex-envs-nonov-similar-witness x y))))))))



(encapsulate nil
  (local
   (defthm svex-compose-lookup-when-nonoverride-p
     (implies (and (svar-override-p v type)
                   (svarlist-nonoverride-p (svex-alist-keys x) type))
              (equal (svex-compose-lookup v x) (svex-var v)))
     :hints(("Goal" :in-theory (enable svex-compose-lookup
                                       svex-lookup-redef
                                       svex-alist-keys svarlist-nonoverride-p)))))

  (local (defthm svex-envs-1mask-equiv-of-append
           (implies (and (equal (alist-keys (svex-env-fix a))
                                (alist-keys (svex-env-fix b)))
                         (svex-envs-1mask-equiv a b)
                         (svex-envs-1mask-equiv c d))
                    (equal (svex-envs-1mask-equiv (append a c) (append b d))
                           t))
           :hints(("goal" :in-theory (disable append))
                  (and stable-under-simplificationp
                       `(:expand (,(car (last clause))))))))

  (local (defthm svex-env-<<=-of-append2
           (implies (and (equal (alist-keys (svex-env-fix a))
                                (alist-keys (svex-env-fix b)))
                         (svex-env-<<= a b)
                         (svex-env-<<= c d))
                    (svex-env-<<= (append a c) (append b d)))
           :hints(("goal" :in-theory (disable append))
                  (and stable-under-simplificationp
                       `(:expand (,(car (last clause))))))))

  (local (defthm alist-keys-of-remove-override
           (equal (Alist-keys (svex-env-remove-override x type))
                  (svarlist-remove-override (alist-keys (svex-env-fix x)) type))
           :hints(("Goal" :in-theory (enable svex-env-remove-override alist-keys svarlist-remove-override svex-env-fix)))))

  (local (defthm alist-keys-of-filter-override
           (equal (Alist-keys (svex-env-filter-override x type))
                  (svarlist-filter-override (alist-keys (svex-env-fix x)) type))
           :hints(("Goal" :in-theory (enable svex-env-filter-override alist-keys svarlist-filter-override svex-env-fix)))))
  
  (local (defthm svex-env-ov<<=-of-append
           (implies (and (equal (alist-keys (svex-env-fix a))
                                (alist-keys (svex-env-fix b)))
                         (svex-env-ov<<= a b)
                         (svex-env-ov<<= c d))
                    (svex-env-ov<<= (append a c) (append b d)))
           :hints(("Goal" :in-theory (enable svex-env-ov<<=)))))

  (local (defthm ash-of-logand
           (equal (ash (logand x y) n)
                  (logand (ash x n) (ash y n)))
           :hints ((bitops::logbitp-reasoning))))
  
  (local (defthm 4vec-1mask-of-4vec-rsh
           (implies (2vec-p n)
                    (equal (4vec-1mask (4vec-rsh n x))
                           (ash (4vec-1mask x) (- (2vec->val n)))))
           :hints(("Goal" :in-theory (enable 4vec-1mask 4vec-rsh 4vec-shift-core)))))

  (local (defthm 4vec-1mask-of-4vec-concat
           (implies (and (2vec-p n)
                         (<= 0 (2vec->val n)))
                    (equal (4vec-1mask (4vec-concat n x y))
                           (logapp (2vec->val n) (4vec-1mask x) (4vec-1mask y))))
           :hints(("Goal" :in-theory (enable 4vec-1mask 4vec-concat))
                  (bitops::logbitp-reasoning))))

  (local (defthm 4vec-1mask-equiv-of-4vec-rsh
           (implies (and (4vec-1mask-equiv x y)
                         (2vec-p n))
                    (equal (4vec-1mask-equiv (4vec-rsh n x) (4vec-rsh n y)) t))
           :hints(("Goal" :in-theory (enable 4vec-1mask-equiv)))))

  (local (defthm 4vec-1mask-equiv-of-4vec-concat
           (implies (and (4vec-1mask-equiv x y)
                         (4vec-1mask-equiv z w)
                         (2vec-p n)
                         (<= 0 (2vec->val n)))
                    (equal (4vec-1mask-equiv (4vec-concat n x z) (4vec-concat n y w)) t))
           :hints(("Goal" :in-theory (enable 4vec-1mask-equiv)))))
  
  (local (in-theory (disable SVEX-ENV-LOOKUP-OF-NETEVAL-ORDERING-EVAL)))
  (local (in-theory (enable svex-ovmonotonic-necc
                            svex-env-ov<<=-necc)))

  (local (defthm svex-env-ov<<=-of-cons
           (implies (svex-env-ov<<= x y)
                    (iff (svex-env-ov<<= (cons (cons v a) x) (cons (cons v b) y))
                         (or (not (svar-p v))
                             (if (svar-override-p v :test)
                                 (4vec-1mask-equiv a b)
                               (4vec-<<= a b)))))
           :hints (("goal" :do-not-induct t
                    :in-theory (enable svex-env-lookup-of-cons-split)
                    :expand ((svex-env-ov<<= (cons (cons v a) x) (cons (cons v b) y)))
                    :use ((:instance svex-env-ov<<=-necc
                           (v (svex-env-ov<<=-witness (cons (cons v a) x) (cons (cons v b) y))))
                          (:instance svex-env-ov<<=-necc
                           (v v)
                           (x (cons (cons v a) x))
                           (y (cons (cons v b) y))))))))
                         
  
  (defthm-neteval-ordering-compile-flag
    (defthm neteval-ordering-eval-ovmonotonic
      (implies (and (svex-alist-ovmonotonic network)
                    (svarlist-nonoverride-p (svex-alist-keys network) :test)
                    (svex-env-ov<<= env1 env2))
               (svex-env-ov<<= (neteval-ordering-eval x network env1)
                               (neteval-ordering-eval x network env2)))
      :hints ('(:expand ((:free (env) (neteval-ordering-eval x network env)))))
      :flag neteval-ordering-compile)

    (defthm neteval-sigordering-eval-ovmonotonic
      (implies (and (svex-alist-ovmonotonic network)
                    (svarlist-nonoverride-p (svex-alist-keys network) :test)
                    (svex-env-ov<<= env1 env2))
               (and (implies (not (svar-override-p signal :test))
                             (4vec-<<= (neteval-sigordering-eval x signal offset network env1)
                                       (neteval-sigordering-eval x signal offset network env2)))
                    (implies (svar-override-p signal :test)
                             (equal (4vec-1mask-equiv
                                     (neteval-sigordering-eval x signal offset network env1)
                                     (neteval-sigordering-eval x signal offset network env2))
                                    t))))
      :hints ('(:expand ((:free (env) (neteval-sigordering-eval x signal offset network env)))))
      :flag neteval-sigordering-compile)


    (defthm neteval-ordering-or-null-eval-ovmonotonic
      (implies (and (svex-alist-ovmonotonic network)
                    (svarlist-nonoverride-p (svex-alist-keys network) :test)
                    (svex-env-ov<<= env1 env2))
               (and (implies (not (svar-override-p signal :test))
                             (4vec-<<= (neteval-ordering-or-null-eval x signal network env1)
                                       (neteval-ordering-or-null-eval x signal network env2)))
                    (implies (svar-override-p signal :test)
                             (equal (4vec-1mask-equiv (neteval-ordering-or-null-eval x signal network env1)
                                                      (neteval-ordering-or-null-eval x signal network env2))
                                    t))))
      :hints ('(:expand ((:free (env) (neteval-ordering-or-null-eval x signal network env))))
              (and stable-under-simplificationp
                   '(:use ((:instance svex-compose-lookup-when-svex-alist-ovmonotonic
                            (x network) (k signal)))
                     :in-theory (e/d (svex-eval-of-var)
                                     (svex-compose-lookup-when-svex-alist-ovmonotonic)))))
      :flag neteval-ordering-or-null-compile))

  (local (defthm member-when-nonoverride-p
           (implies (and (svar-override-p v type)
                         (svarlist-nonoverride-p x type))
                    (not (member-equal (svar-fix v) x)))
           :hints(("Goal" :in-theory (enable svarlist-nonoverride-p)))))
  
  (local (defthm svex-env-<<=-when-ov<<=
           (implies (and (svex-env-ov<<= x y)
                         (svarlist-nonoverride-p (alist-keys (svex-env-fix x)) :test))
                    (svex-env-<<= x y))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause)))
                          :in-theory (enable svex-env-lookup-when-not-boundp
                                             svex-env-boundp-iff-member-alist-keys)
                          :cases ((svar-override-p (svex-env-<<=-witness x y) :test)))))))
  
  (defthm neteval-ordering-compile-ovmonotonic
    (implies (and (svex-alist-ovmonotonic network)
                  (svarlist-nonoverride-p (svex-alist-keys network) :test)
                  (svarlist-nonoverride-p (alist-keys (neteval-ordering-fix x)) :test))
             (svex-alist-ovmonotonic (neteval-ordering-compile x network)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(Car (last clause)))))))

  (defthm svex-alist-ovmonotonic-of-svarlist-x-subst
    (svex-alist-ovmonotonic (svarlist-x-subst keys))
    :hints(("Goal" :in-theory (enable svex-alist-ovmonotonic))))

  (local
   (defthmd ovmonotonic-when-netevalcomp-p-lemma
     (implies (and (svex-alist-ovmonotonic network)
                   (svarlist-nonoverride-p (svex-alist-keys network) :test)
                   (set-equiv (svex-alist-keys
                               (svex-alist-compose
                                       (neteval-ordering-compile ord network)
                                       (svarlist-x-subst (svex-alist-keys network))))
                              (svex-alist-keys network)))
              (svex-alist-ovmonotonic (svex-alist-compose
                                       (neteval-ordering-compile ord network)
                                       (svarlist-x-subst (svex-alist-keys network)))))))
  
  (defthm ovmonotonic-when-netevalcomp-p
    (implies (and (netevalcomp-p values network)
                  (set-equiv (svex-alist-keys values) (svex-alist-keys network))
                  (svex-alist-ovmonotonic network)
                  (svarlist-nonoverride-p (svex-alist-keys network) :test))
             (svex-alist-ovmonotonic values))
    :hints(("Goal" :in-theory (e/d (netevalcomp-p svex-alist-keys-equiv))
            :use ((:instance ovmonotonic-when-netevalcomp-p-lemma
                   (ord (netevalcomp-p-witness values network)))
                  (:instance SVEX-ALIST-EVAL-EQUIV-REFINES-SVEX-ALIST-KEYS-EQUIV
                   (x values)
                   (y (svex-alist-compose
                       (neteval-ordering-compile
                        (netevalcomp-p-witness values network) network)
                       (svarlist-x-subst (svex-alist-keys network)))))))))

  (local (defun-sk envs-ovcongruent-rec-cond (x y)
           (forall v
                   (implies (and (or (svar-override-p v :test)
                                     (svar-override-p v :val))
                                 (case-split (svex-env-boundp v x)))
                            (equal (Svex-env-lookup v x) (svex-env-lookup v y))))
           :rewrite :direct))

  (local (in-theory (disable envs-ovcongruent-rec-cond)))

  (local (defthm 4vec-concat-of-rsh
           (implies (and (natp w) (natp sh))
                    (equal (4vec-concat (2vec w)
                                        (4vec-rsh (2vec sh) x)
                                        (4vec-rsh (2vec (+ w sh)) x))
                           (4vec-rsh (2vec sh) x)))
           :hints(("Goal" :in-theory (enable 4vec-concat
                                             4vec-rsh
                                             4vec-shift-core))
                  (logbitp-reasoning))))

  (local
   (defthm-neteval-ordering-compile-flag
     (defthm neteval-ordering-eval-ovcongruent-rec-cond
       (implies (and ;; (svex-alist-ovcongruent network)
                 (svarlist-nonoverride-p (svex-alist-keys network) :test)
                 (svarlist-nonoverride-p (svex-alist-keys network) :val))
                (envs-ovcongruent-rec-cond (neteval-ordering-eval x network env) env))
       :hints ('(:expand ((:free (env) (neteval-ordering-eval x network env))))
               (and stable-under-simplificationp
                    `(:expand (,(car (last clause)))))
               (And stable-under-simplificationp
                    (let ((call (acl2::find-call-lst 'envs-ovcongruent-rec-cond-witness clause)))
                      (and call
                           `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . key)))))))
               (and stable-under-simplificationp
                    '(:in-theory (enable svex-env-lookup-of-cons-split
                                         svex-env-boundp-of-cons))))
       :flag neteval-ordering-compile)
     (defthm neteval-sigordering-eval-ovcongruent-rec-cond
       (implies (and ;; (svex-alist-ovcongruent network)
                 (svarlist-nonoverride-p (svex-alist-keys network) :test)
                 (svarlist-nonoverride-p (svex-alist-keys network) :val)
                 ;; (not (svar-override-p signal :test))
                 ;; (not (svar-override-p signal :val))
                 )
                (implies (or (svar-override-p signal :test)
                             (svar-override-p signal :val))
                         (equal (neteval-sigordering-eval x signal offset network env)
                                (4vec-rsh (2vec (nfix offset)) (svex-env-lookup signal env)))))
       :hints ('(:expand ((:free (env) (neteval-sigordering-eval x signal offset network env)))))
       :flag neteval-sigordering-compile)

     (defthm neteval-ordering-or-null-eval-ovcongruent-rec-cond
       (implies (and ;; (svex-alist-ovcongruent network)
                 (svarlist-nonoverride-p (svex-alist-keys network) :test)
                 (svarlist-nonoverride-p (svex-alist-keys network) :val)
                 (or (svar-override-p signal :test)
                     (svar-override-p signal :val)))
                (equal (neteval-ordering-or-null-eval x signal network env)
                       (svex-env-lookup signal env)))
       :hints ('(:expand ((:free (env) (neteval-ordering-or-null-eval x signal network env))
                          (:free (v env) (svex-eval (svex-var v) env)))))
       :flag neteval-ordering-or-null-compile)))

  (local
   (defthm neteval-ordering-eval-ovcongruent-rec-cond-rw
     (implies (and ;; (svex-alist-ovcongruent network)
               (svarlist-nonoverride-p (svex-alist-keys network) :test)
               (svarlist-nonoverride-p (svex-alist-keys network) :val)
               (or (svar-override-p v :test)
                   (svar-override-p v :val))
               (case-split (hons-assoc-equal (svar-fix v) (neteval-ordering-fix x))))
              (equal (svex-env-lookup v (neteval-ordering-eval x network env))
                     (svex-env-lookup v env)))
     :hints (("goal" :use neteval-ordering-eval-ovcongruent-rec-cond
              :in-theory (disable neteval-ordering-eval-ovcongruent-rec-cond)))))

  (local (defthm svex-envs-ovsimilar-implies-1mask-equiv-test
           (implies (and (svex-envs-ovsimilar x y)
                         (svar-override-p v :test))
                    (equal (4vec-1mask-equiv (svex-env-lookup v x) (svex-env-lookup v y))
                           t))
           :hints (("goal" :use svex-envs-ovsimilar-necc))))

  (local (defthm svex-envs-ovsimilar-implies-equal-nonoverride
           (implies (and (svex-envs-ovsimilar x y)
                         (not (svar-override-p v :test))
                         (not (svar-override-p v :val)))
                    (equal (equal (svex-env-lookup v x) (svex-env-lookup v y))
                           t))
           :hints (("goal" :use svex-envs-ovsimilar-necc))))

  (local (defthm svex-envs-ovsimilar-implies-equal-val
           (implies (and (svex-envs-ovsimilar x y)
                         (svar-override-p v :val)
                         ;; (4vec-1mask-equiv (svex-env-lookup v2 y)
                         ;;                   (svex-env-lookup (svar-change-override v :test) y))
                         (svar-equiv v2 (svar-change-override v :test)))
                    (equal (equal (4vec-bit?! (svex-env-lookup v2 y)
                                              (svex-env-lookup v x)
                                              0)
                                  (4vec-bit?! (svex-env-lookup v2 y)
                                              (svex-env-lookup v y)
                                              0))
                           t))
           :hints (("goal" :use svex-envs-ovsimilar-necc))))

  (local
   (defthm svex-envs-ovsimilar-of-append
     (implies (and (svex-envs-ovsimilar x1 x2)
                   (svex-envs-ovsimilar y1 y2)
                   (envs-ovcongruent-rec-cond x1 y1)
                   (envs-ovcongruent-rec-cond x2 y2)
                   (equal (alist-keys (svex-env-fix x1))
                          (alist-keys (svex-env-fix x2))))
              (equal (svex-envs-ovsimilar (append x1 y1)
                                          (append x2 y2))
                     t))
     :hints ((and stable-under-simplificationp
                  (let* ((lit (car (last clause))))
                    `(:expand (,lit))))
             (and stable-under-simplificationp
                  (let ((call (acl2::find-call-lst 'svex-envs-ovsimilar-witness clause)))
                      (and call
                           `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . key)))))))
             (and stable-under-simplificationp
                  '(:use ((:instance svex-envs-ovsimilar-necc
                           (x x1) (y x2) (v key))
                          (:instance svex-envs-ovsimilar-necc
                           (x y1) (y y2) (v key)))
                    :in-theory (enable svex-env-boundp-iff-member-alist-keys)
                    :do-not-induct t)))
     :otf-flg t))
                   

  
  ;; (local (defthm svex-envs-ovsimilar-implies-equal-val2
  ;;          (implies (and (svex-envs-ovsimilar x y)
  ;;                        (svar-override-p v :val))
  ;;                   (equal (equal (4vec-bit?! (svex-env-lookup (svar-change-override v :test) x)
  ;;                                             (svex-env-lookup v x)
  ;;                                             0)
  ;;                                 (4vec-bit?! (svex-env-lookup (svar-change-override v :test) x)
  ;;                                             (svex-env-lookup v y)
  ;;                                             0))
  ;;                          t))
  ;;          :hints (("goal" :use svex-envs-ovsimilar-necc))))

  (local (defthm 4vec-bit?!-test-0
           (equal (4vec-bit?! 0 x y)
                  (4vec-fix y))
           :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bitmux)))))

  (defthm-neteval-ordering-compile-flag
    (defthm neteval-ordering-eval-ovcongruent
      (implies (and (svex-alist-ovcongruent network)
                    (svarlist-nonoverride-p (svex-alist-keys network) :test)
                    (svarlist-nonoverride-p (svex-alist-keys network) :val)
                    (svex-envs-ovsimilar env1 env2))
               ;; (and (svex-envs-nonov-similar (neteval-ordering-eval x network env1)
               ;;                               (neteval-ordering-eval x network env2))
               ;;      (implies ()
               ;; (and (implies (and (not (svar-override-p signal :test))
               ;;                    (not (svar-override-p signal :val)))
               ;;               (Equal (svex-env-lookup signal (neteval-ordering-eval x network env1))
               ;;                      (svex-env-lookup signal (neteval-ordering-eval x network env2))))
               ;;      (implies (or (svar-override-p signal :test)
               ;;                   (svar-override-p signal :val))
               ;;               (and (Equal (svex-env-lookup signal (neteval-ordering-eval x network env1))
               ;;                           (svex-env-lookup signal env1))
               ;;                    (Equal (svex-env-lookup signal (neteval-ordering-eval x network env2))
               ;;                           (svex-env-lookup signal env2)))))
               (equal (svex-envs-ovsimilar (neteval-ordering-eval x network env1)
                                           (neteval-ordering-eval x network env2))
                      t))
      :hints ('(:expand ((:free (env) (neteval-ordering-eval x network env))))
              (and stable-under-simplificationp
                   `(:expand (,(car (last clause)))))
              (And stable-under-simplificationp
                   (let ((call (acl2::find-call-lst 'svex-envs-ovsimilar-witness clause)))
                     (and call
                          `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . key)))))))
               (and stable-under-simplificationp
                    '(:in-theory (enable svex-env-lookup-of-cons-split
                                         svex-env-boundp-of-cons
                                         svex-env-lookup-when-not-boundp
                                         svar-override-p-when-other
                                         equal-of-svar-change-override))))
      :flag neteval-ordering-compile)

    (defthm neteval-sigordering-eval-ovcongruent
      (implies (and (svex-alist-ovcongruent network)
                    (svarlist-nonoverride-p (svex-alist-keys network) :test)
                    (svarlist-nonoverride-p (svex-alist-keys network) :val)
                    (svex-envs-ovsimilar env1 env2)
                    (not (svar-override-p signal :test))
                    (not (svar-override-p signal :val))
                    )
               (equal (neteval-sigordering-eval x signal offset network env1)
                      (neteval-sigordering-eval x signal offset network env2)))
      :hints ('(:expand ((:free (env) (neteval-sigordering-eval x signal offset network env)))))
      :flag neteval-sigordering-compile)


    (defthm neteval-ordering-or-null-eval-ovcongruent
      (implies (and (svex-alist-ovcongruent network)
                    (svarlist-nonoverride-p (svex-alist-keys network) :test)
                    (svarlist-nonoverride-p (svex-alist-keys network) :val)
                    (svex-envs-ovsimilar env1 env2)
                    (not (svar-override-p signal :test))
                    (not (svar-override-p signal :val)))
               (equal (neteval-ordering-or-null-eval x signal network env1)
                      (neteval-ordering-or-null-eval x signal network env2)))
      :hints ('(:expand ((:free (env) (neteval-ordering-or-null-eval x signal network env))))
              (and stable-under-simplificationp
                   '(:use ((:instance svex-compose-lookup-when-svex-alist-ovcongruent
                            (x network) (k signal))
                           (:instance svex-envs-ovsimilar-necc
                            (x env1) (y env2) (v signal)))
                     :in-theory (e/d (svex-eval-of-var
                                      svex-ovcongruent-necc)
                                     (svex-compose-lookup-when-svex-alist-ovcongruent)))))
      :flag neteval-ordering-or-null-compile))


  (local (defthm svex-envs-equivalent-when-ovsimilar
           (implies (and (svex-envs-ovsimilar x y)
                         (svarlist-nonoverride-p (alist-keys (svex-env-fix x)) :test)
                         (svarlist-nonoverride-p (alist-keys (svex-env-fix x)) :val)
                         (equal (alist-keys (svex-env-fix x))
                                (alist-keys (svex-env-fix y))))
                    (Equal (svex-envs-equivalent x y) t))
           :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                             svex-env-lookup-when-not-boundp
                                             svex-env-boundp-iff-member-alist-keys)
                   :use ((:instance svex-envs-ovsimilar-necc
                          (v (svex-envs-equivalent-witness x y))))))))
  
  (defthm neteval-ordering-compile-ovcongruent
    (implies (and (svex-alist-ovcongruent network)
                  (svarlist-nonoverride-p (svex-alist-keys network) :test)
                  (svarlist-nonoverride-p (svex-alist-keys network) :val)
                  (svarlist-nonoverride-p (alist-keys (neteval-ordering-fix x)) :test)
                  (svarlist-nonoverride-p (alist-keys (neteval-ordering-fix x)) :val))
             (svex-alist-ovcongruent (neteval-ordering-compile x network)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(Car (last clause)))))))

  (defthm svex-alist-ovcongruent-of-svarlist-x-subst
    (svex-alist-ovcongruent (svarlist-x-subst keys))
    :hints(("Goal" :in-theory (enable svex-alist-ovcongruent))))

  (local
   (defthmd ovcongruent-when-netevalcomp-p-lemma
     (implies (and (svex-alist-ovcongruent network)
                   (svarlist-nonoverride-p (svex-alist-keys network) :test)
                   (svarlist-nonoverride-p (svex-alist-keys network) :val)
                   (set-equiv (svex-alist-keys
                               (svex-alist-compose
                                       (neteval-ordering-compile ord network)
                                       (svarlist-x-subst (svex-alist-keys network))))
                              (svex-alist-keys network)))
              (svex-alist-ovcongruent (svex-alist-compose
                                       (neteval-ordering-compile ord network)
                                       (svarlist-x-subst (svex-alist-keys network)))))))
  
  (defthm ovcongruent-when-netevalcomp-p
    (implies (and (netevalcomp-p values network)
                  (set-equiv (svex-alist-keys values) (svex-alist-keys network))
                  (svex-alist-ovcongruent network)
                  (svarlist-nonoverride-p (svex-alist-keys network) :test)
                  (svarlist-nonoverride-p (svex-alist-keys network) :val))
             (svex-alist-ovcongruent values))
    :hints(("Goal" :in-theory (e/d (netevalcomp-p svex-alist-keys-equiv))
            :use ((:instance ovcongruent-when-netevalcomp-p-lemma
                   (ord (netevalcomp-p-witness values network)))
                  (:instance SVEX-ALIST-EVAL-EQUIV-REFINES-SVEX-ALIST-KEYS-EQUIV
                   (x values)
                   (y (svex-alist-compose
                       (neteval-ordering-compile
                        (netevalcomp-p-witness values network) network)
                       (svarlist-x-subst (svex-alist-keys network))))))))))




