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
(include-book "partial-monotonicity")
(include-book "svex-lattice")
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "arithmetic/top" :Dir :system))
(local (include-book "alist-thms"))
;;(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))





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



(encapsulate nil
  (local (in-theory (enable svex-monotonic-p-necc)))
  (defthm-neteval-ordering-compile-flag
    (defthm neteval-ordering-eval-monotonic
      (implies (and (svex-alist-monotonic-p network)
                    (svex-env-<<= env1 env2))
               (svex-env-<<= (neteval-ordering-eval x network env1)
                             (neteval-ordering-eval x network env2)))
      :hints ('(:expand ((:free (env) (neteval-ordering-eval x network env)))))
      :flag neteval-ordering-compile)

    (defthm neteval-sigordering-eval-monotonic
      (implies (and (svex-alist-monotonic-p network)
                    (svex-env-<<= env1 env2))
               (4vec-<<= (neteval-sigordering-eval x signal offset network env1)
                         (neteval-sigordering-eval x signal offset network env2)))
      :hints ('(:expand ((:free (env) (neteval-sigordering-eval x signal offset network env)))))
      :flag neteval-sigordering-compile)

    (defthm neteval-ordering-or-null-eval-monotonic
      (implies (and (svex-alist-monotonic-p network)
                    (svex-env-<<= env1 env2))
               (4vec-<<= (neteval-ordering-or-null-eval x signal network env1)
                         (neteval-ordering-or-null-eval x signal network env2)))
      :hints ('(:expand ((:free (env) (neteval-ordering-or-null-eval x signal network env)))))
      :flag neteval-ordering-or-null-compile))

  (local (defthm consp-hons-assoc-equal
           (iff (consp (hons-assoc-equal k x))
                (hons-assoc-equal k x))))
  (local (defthm member-alist-keys
           (iff (member-equal k (alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable alist-keys)))))
  
  (local (defthm member-alist-keys-of-svex-env-fix
           (implies (svar-p k)
                    (iff (member-equal k (alist-keys (svex-env-fix x)))
                         (svex-env-boundp k x)))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))

  (local (defthm svex-env-extract-of-append-alists-when-first-keys-not-intersecting
           (implies (not (intersectp-equal (svarlist-fix keys) (alist-keys (svex-env-fix x))))
                    (equal (svex-env-extract keys (append x y))
                           (svex-env-extract keys y)))
           :hints(("Goal" :in-theory (e/d (svex-env-extract svarlist-fix intersectp-equal)
                                          (acl2::intersectp-equal-commute))))))

  (local (defthm svex-envs-similar-of-append-extract-blah
           (implies (equal (svex-env-extract keys w)
                           (svex-env-extract keys (append a w)))
                    (svex-envs-similar (append (svex-env-extract keys w)
                                               a
                                               w)
                                       (append a w)))
           :hints(("Goal" :in-theory (e/d (svex-envs-similar)
                                          (svex-env-lookup-of-svex-env-extract))
                   :use ((:instance svex-env-lookup-of-svex-env-extract
                          (v (svex-envs-similar-witness
                              (append (svex-env-extract keys w)
                                      a
                                      w)
                              (append a w)))
                          (vars keys) (env w))
                         (:instance svex-env-lookup-of-svex-env-extract
                          (v (svex-envs-similar-witness
                              (append (svex-env-extract keys w)
                                      a
                                      w)
                              (append a w)))
                          (vars keys) (env (append a w))))))))

  ;; (local (defthm svex-env-extract-non-intersecting-of-neteval-ordering-eval
  ;;          (implies ;; (not (intersectp-equal (svarlist-fix params) (svex-alist-keys network)))
  ;;           (svex-compose-alist-const/selfbound-keys-p params network)
  ;;                   (equal (svex-env-extract params (append (neteval-ordering-eval x network env) env))
  ;;                          (svex-env-extract params env)))
  ;;          :hints(("Goal" :in-theory (e/d (svex-env-extract
  ;;                                          svarlist-fix
  ;;                                          intersectp-equal
  ;;                                          svex-compose-alist-const/selfbound-keys-p
  ;;                                          lookup-network-fixed-signal-of-neteval-ordering-eval)
  ;;                                         (acl2::intersectp-equal-commute))))))


  (local (defun neteval-sigordering-order-ind (x offset)
           (declare (xargs :measure (neteval-sigordering-count x)))
           (neteval-sigordering-case x
             :segment (neteval-sigordering-order-ind x.rest (+ x.width (nfix offset)))
             :remainder offset)))
  
  (local (defthm neteval-sigordering-eval-equiv-when-constantp
           (implies (and (svex-constantp (svex-compose-lookup signal network))
                         (equal (svex-env-lookup signal env1) (svex-env-lookup signal env2)))
                    (equal (equal (neteval-sigordering-eval x signal offset network env1)
                                  (neteval-sigordering-eval x signal offset network env2))
                           t))
           :hints (("goal" :induct (neteval-sigordering-order-ind x offset)
                    :expand ((:free (env) (neteval-sigordering-eval x signal offset network env))
                             (:free (x env) (neteval-ordering-or-null-eval x signal network env)))
                    :in-theory (enable svex-constantp-necc)))))

  ;; (local (defthm neteval-sigordering-eval-equiv-when-selfequiv
  ;;          (implies (and (svex-eval-equiv (svex-compose-lookup signal network) (svex-var signal))
  ;;                        (equal (svex-env-lookup signal env1) (svex-env-lookup signal env2)))
  ;;                   (equal (equal (neteval-sigordering-eval x signal offset network env1)
  ;;                                 (neteval-sigordering-eval x signal offset network env2))
  ;;                          t))
  ;;          :hints (("goal" :induct (neteval-sigordering-order-ind x offset)
  ;;                   :expand ((:free (env) (neteval-sigordering-eval x signal offset network env))
  ;;                            (:free (x env) (neteval-ordering-or-null-eval x signal network env))
  ;;                            (:free (x env) (svex-eval (svex-var x) env)))
  ;;                   :in-theory (e/d (lookup-network-fixed-signal-of-neteval-ordering-eval)
  ;;                                   (SVEX-ENV-LOOKUP-OF-NETEVAL-ORDERING-EVAL))))))
  
  
  (local (defthm svex-env-extract-of-append-neteval-equivalents
           (implies (and (equal (svex-env-extract keys x) (svex-env-extract keys y))
                         (svex-compose-alist-const/selfbound-keys-p keys a))
                    (equal (equal (svex-env-extract keys (append (neteval-ordering-eval ord a x) x))
                                  (svex-env-extract keys (append (neteval-ordering-eval ord a y) y)))
                           t))
           :hints(("Goal" :in-theory (e/d (svex-env-extract
                                           svex-compose-alist-const/selfbound-keys-p
                                           lookup-network-fixed-signal-of-neteval-ordering-eval)
                                          (svex-env-lookup-of-neteval-ordering-eval))
                   :induct t
                   :expand ((:free (v x) (svex-eval (svex-var v) x))))
                  (and stable-under-simplificationp
                       '(:in-theory (enable svex-env-lookup-of-neteval-ordering-eval))))))


  
  
  
  
  (defthm-neteval-ordering-compile-flag
    (defthm neteval-ordering-eval-partial-monotonic
      (implies (and (svex-alist-partial-monotonic params network)
                    (svex-compose-alist-const/selfbound-keys-p params network)
                    (equal (svex-env-extract params env1)
                           (svex-env-extract params env2))
                    (svex-env-<<= env1 env2))
               (svex-env-<<= (neteval-ordering-eval x network env1)
                             (neteval-ordering-eval x network env2)))
      :hints ('(:expand ((:free (env) (neteval-ordering-eval x network env)))))
      :flag neteval-ordering-compile)

    (defthm neteval-sigordering-eval-partial-monotonic
      (implies (and (svex-alist-partial-monotonic params network)
                    (svex-compose-alist-const/selfbound-keys-p params network)
                    (equal (svex-env-extract params env1)
                           (svex-env-extract params env2))
                    (svex-env-<<= env1 env2))
               (4vec-<<= (neteval-sigordering-eval x signal offset network env1)
                         (neteval-sigordering-eval x signal offset network env2)))
      :hints ('(:expand ((:free (env) (neteval-sigordering-eval x signal offset network env)))))
      :flag neteval-sigordering-compile)

    (defthm neteval-ordering-or-null-eval-partial-monotonic
      (implies (and (svex-alist-partial-monotonic params network)
                    (svex-compose-alist-const/selfbound-keys-p params network)
                    (equal (svex-env-extract params env1)
                           (svex-env-extract params env2))
                    (svex-env-<<= env1 env2))
               (4vec-<<= (neteval-ordering-or-null-eval x signal network env1)
                         (neteval-ordering-or-null-eval x signal network env2)))
      :hints ('(:expand ((:free (env) (neteval-ordering-or-null-eval x signal network env))))
              (and stable-under-simplificationp
                   '(:use ((:instance svex-compose-lookup-when-svex-alist-partial-monotonic
                            (param-keys params) (x network) (k signal))
                           (:instance eval-when-svex-partial-monotonic
                            (param-keys params)
                            (x (svex-compose-lookup signal network))
                            ;; (setting (svex-env-to-subst
                            ;;           (svex-env-extract params env1)))
                            (env1 (APPEND (NETEVAL-ORDERING-EVAL (NETEVAL-ORDERING-OR-NULL-ORDERING->ORD X)
                                                                 NETWORK ENV1)
                                          ENV1))
                            (env2 (APPEND (NETEVAL-ORDERING-EVAL (NETEVAL-ORDERING-OR-NULL-ORDERING->ORD X)
                                                                 NETWORK ENV2)
                                          ENV2))))
                     :in-theory (disable svex-compose-lookup-when-svex-alist-partial-monotonic))))
      :flag neteval-ordering-or-null-compile))

  (defthm neteval-ordering-compile-monotonic
    (implies (svex-alist-monotonic-p network)
             (svex-alist-monotonic-p (neteval-ordering-compile x network)))
    :hints (("goal" :expand ((svex-alist-monotonic-p (neteval-ordering-compile x network))))))

  (defthm neteval-sigordering-compile-monotonic
    (implies (svex-alist-monotonic-p network)
             (svex-monotonic-p (neteval-sigordering-compile x signal offset network)))
    :hints (("goal" :in-theory (enable svex-monotonic-p))))

  (defthm neteval-ordering-or-null-compile-monotonic
    (implies (svex-alist-monotonic-p network)
             (svex-monotonic-p (neteval-ordering-or-null-compile x signal network)))
    :hints (("goal" :in-theory (enable svex-monotonic-p))))


  (local (defthm svex-env-extract-of-append-when-subset-of-first
           (implies (subsetp-equal (svarlist-fix params) (alist-keys (svex-env-fix x)))
                    (equal (svex-env-extract params (append x y))
                           (svex-env-extract params x)))
           :hints(("Goal" :in-theory (enable svex-env-extract svarlist-fix)))))
  
  (defthm neteval-ordering-compile-partial-monotonic
    (implies (and (svex-alist-partial-monotonic params network)
                  (svex-compose-alist-const/selfbound-keys-p params network))
             (svex-alist-partial-monotonic params (neteval-ordering-compile x network)))
    :hints (("goal" :expand ((svex-alist-partial-monotonic params (neteval-ordering-compile x network)))
             :in-theory (enable svex-alist-monotonic-p
                                svex-alist-eval-when-svex-alist-constantp))))

  (defthm neteval-sigordering-compile-partial-monotonic
    (implies (and (svex-alist-partial-monotonic params network)
                  (svex-compose-alist-const/selfbound-keys-p params network))
             (svex-partial-monotonic params (neteval-sigordering-compile x signal offset network)))
    :hints (("goal" :in-theory (enable svex-partial-monotonic svex-monotonic-p
                                       svex-alist-eval-when-svex-alist-constantp))))

  (defthm neteval-ordering-or-null-compile-partial-monotonic
    (implies (and (svex-alist-partial-monotonic params network)
                  (svex-compose-alist-const/selfbound-keys-p params network))
             (svex-partial-monotonic params (neteval-ordering-or-null-compile x signal network)))
    :hints (("goal" :in-theory (enable svex-partial-monotonic svex-monotonic-p
                                       svex-alist-eval-when-svex-alist-constantp))))


  (local (defthm svex-eval-mono-lemma
           (implies (and (svex-<<= x1 x2)
                         (svex-env-<<= env1 env2)
                         (or (svex-monotonic-p x1)
                             (svex-monotonic-p x2)))
                    (4vec-<<= (svex-eval x1 env1)
                              (svex-eval x2 env2)))
           :hints (("goal" :use ((:instance svex-<<=-necc
                                  (x x1) (y x2) (env env2))
                                 (:instance svex-<<=-necc
                                  (x x1) (y x2) (env env1))
                                 (:instance svex-monotonic-p-necc
                                  (x x1) (env1 env1) (env2 env2))
                                 (:instance svex-monotonic-p-necc
                                  (x x2) (env1 env1) (env2 env2)))
                    :in-theory (e/d (4vec-<<=-transitive-1)
                                    (svex-<<=-necc
                                     svex-monotonic-p-necc))))))

  (defthm-neteval-ordering-compile-flag
    (defthm neteval-ordering-eval-preserves-<<=
      (implies (and (or (svex-alist-monotonic-p network1)
                        (svex-alist-monotonic-p network2))
                    ;; (set-equiv (svex-alist-keys network1)
                    ;;            (svex-alist-keys network2))
                    (svex-alist-compose-<<= network1 network2))
               (svex-env-<<= (neteval-ordering-eval x network1 env)
                             (neteval-ordering-eval x network2 env)))
      :hints ('(:expand ((:free (network) (neteval-ordering-eval x network env)))))
      :flag neteval-ordering-compile)

    (defthm neteval-sigordering-eval-preserves-<<=
      (implies (and (or (svex-alist-monotonic-p network1)
                        (svex-alist-monotonic-p network2))
                    ;; (svex-alist-monotonic-p network2)
                    ;; (set-equiv (svex-alist-keys network1)
                    ;;            (svex-alist-keys network2))
                    (svex-alist-compose-<<= network1 network2))
               (4vec-<<= (neteval-sigordering-eval x signal offset network1 env)
                         (neteval-sigordering-eval x signal offset network2 env)))
      :hints ('(:expand ((:free (network) (neteval-sigordering-eval x signal offset network env)))))
      :flag neteval-sigordering-compile)

    (defthm neteval-ordering-or-null-eval-preserves-<<=
      (implies (and (or (svex-alist-monotonic-p network1)
                        (svex-alist-monotonic-p network2))
                    ;; (svex-alist-monotonic-p network2)
                    ;; (set-equiv (svex-alist-keys network1)
                    ;;            (svex-alist-keys network2))
                    (svex-alist-compose-<<= network1 network2))
               (4vec-<<= (neteval-ordering-or-null-eval x signal network1 env)
                         (neteval-ordering-or-null-eval x signal network2 env)))
      :hints ('(:expand ((:free (network) (neteval-ordering-or-null-eval x signal network env)))))
      :flag neteval-ordering-or-null-compile))


  (local (defthm not-svex-constantp-of-var
           (not (Svex-constantp (svex-var x)))
           :hints (("goal" :use ((:instance svex-constantp-necc (x (svex-var x)) (env `((,(svar-fix x) . 1)))))
                    :in-theory (enable svex-eval svex-env-lookup)))))
  
  (local (defthm svex-alist-compose-<<=-and-selfbound-implies-not-constantp
           (implies (and (svex-alist-compose-<<= network1 network2)
                         (svex-eval-equiv (svex-compose-lookup key network1) (svex-var key)))
                    (not (svex-constantp (svex-compose-lookup key network2))))
           :hints (("goal" :expand ((:free (env) (svex-eval (svex-var key) env)))
                    :use ((:instance svex-alist-compose-<<=-necc
                           (x network1) (y network2) (var key))
                          (:instance svex-<<=-necc
                           (x (svex-var key))
                           (y (svex-compose-lookup key network2))
                           (env `((,(svar-fix key) . -1))))
                          (:instance svex-<<=-necc
                           (x (svex-var key))
                           (y (svex-compose-lookup key network2))
                           (env `((,(svar-fix key) . 0)))))
                    :in-theory (e/d (svex-env-lookup
                                     svex-constantp-necc)
                                    (svex-alist-compose-<<=-necc))))))

  ;; (local (defthm neteval-sigordering-eval-equiv-on-networks-when-constantp
  ;;          (implies (and (svex-constantp (svex-compose-lookup signal network1))
  ;;                        (svex-constantp (svex-compose-lookup signal network2)))
  ;;                   (equal (equal (neteval-sigordering-eval x signal offset network1 env)
  ;;                                 (neteval-sigordering-eval x signal offset network2 env))
  ;;                          t))
  ;;          :hints (("goal" :induct (neteval-sigordering-order-ind x offset)
  ;;                   :expand ((:free (network) (neteval-sigordering-eval x signal offset network env))
  ;;                            (:free (x network) (neteval-ordering-or-null-eval x signal network env)))
  ;;                   :in-theory (enable svex-constantp-necc)))))
  
  (local (defthm svex-env-extract-of-append-neteval-network-equivalents
           (implies (and (svex-compose-alist-selfbound-keys-p keys a)
                         (svex-compose-alist-selfbound-keys-p keys b)
                         (svex-alist-compose-<<= network1 network2))
                    (equal (equal (svex-env-extract keys (append (neteval-ordering-eval ord a env) env))
                                  (svex-env-extract keys (append (neteval-ordering-eval ord b env) env)))
                           t))
           :hints(("Goal" :in-theory (e/d (svex-env-extract
                                           svex-compose-alist-selfbound-keys-p
                                           lookup-network-fixed-signal-of-neteval-ordering-eval)
                                          (svex-env-lookup-of-neteval-ordering-eval))
                   :induct t
                   :expand ((:free (v x) (svex-eval (svex-var v) x))))
                  (and stable-under-simplificationp
                       '(:in-theory (enable svex-env-lookup-of-neteval-ordering-eval))))))
  
  (local (defthm svex-eval-partial-mono-lemma
           (implies (and (svex-<<= x1 x2)
                         (svex-env-<<= env1 env2)
                         (bind-free '((params . params)) (params))
                         (equal (svex-env-extract params env1)
                                (svex-env-extract params env2))
                         (or (svex-partial-monotonic params x1)
                             (svex-partial-monotonic params x2)))
                    (4vec-<<= (svex-eval x1 env1)
                              (svex-eval x2 env2)))
           :hints (("goal" :use ((:instance svex-<<=-necc
                                  (x x1) (y x2) (env env2))
                                 (:instance svex-<<=-necc
                                  (x x1) (y x2) (env env1))
                                 (:instance eval-when-svex-partial-monotonic
                                  (param-keys params) (x x1) (env1 env1) (env2 env2))
                                 (:instance eval-when-svex-partial-monotonic
                                  (param-keys params) (x x2) (env1 env1) (env2 env2)))
                    :in-theory (e/d (4vec-<<=-transitive-1)
                                    (svex-<<=-necc
                                     eval-when-svex-partial-monotonic))))))
  

  (defthm-neteval-ordering-compile-flag
    (defthm neteval-ordering-eval-preserves-<<=-when-partial-monotonic
      (implies (and (bind-free '((params . params)) (params))
                    (or (svex-alist-partial-monotonic params network1)
                        (svex-alist-partial-monotonic params network2))
                    (svex-compose-alist-selfbound-keys-p params network1)
                    (svex-compose-alist-selfbound-keys-p params network2)
                    (svex-alist-compose-<<= network1 network2))
               (svex-env-<<= (neteval-ordering-eval x network1 env)
                             (neteval-ordering-eval x network2 env)))
      :hints ('(:expand ((:free (network) (neteval-ordering-eval x network env)))))
      :flag neteval-ordering-compile)

    (defthm neteval-sigordering-eval-preserves-<<=-when-partial-monotonic
      (implies (and (bind-free '((params . params)) (params))
                    (or (svex-alist-partial-monotonic params network1)
                        (svex-alist-partial-monotonic params network2))
                    (svex-compose-alist-selfbound-keys-p params network1)
                    (svex-compose-alist-selfbound-keys-p params network2)
                    (svex-alist-compose-<<= network1 network2))
               (4vec-<<= (neteval-sigordering-eval x signal offset network1 env)
                         (neteval-sigordering-eval x signal offset network2 env)))
      :hints ('(:expand ((:free (network) (neteval-sigordering-eval x signal offset network env)))))
      :flag neteval-sigordering-compile)

    (defthm neteval-ordering-or-null-eval-preserves-<<=-when-partial-monotonic
      (implies (and (bind-free '((params . params)) (params))
                    (or (svex-alist-partial-monotonic params network1)
                        (svex-alist-partial-monotonic params network2))
                    (svex-compose-alist-selfbound-keys-p params network1)
                    (svex-compose-alist-selfbound-keys-p params network2)
                    (svex-alist-compose-<<= network1 network2))
               (4vec-<<= (neteval-ordering-or-null-eval x signal network1 env)
                         (neteval-ordering-or-null-eval x signal network2 env)))
      :hints ('(:expand ((:free (network) (neteval-ordering-or-null-eval x signal network env)))))
      :flag neteval-ordering-or-null-compile))


  (defthm neteval-ordering-compile-preserves-<<=
    (implies (and (or (svex-alist-monotonic-p network1)
                      (svex-alist-monotonic-p network2))
                  (svex-alist-compose-<<= network1 network2))
             ;; note: also svex-alist-compose-<<= because svex-alist-keys are set-equiv
             ;; (by SVEX-ALIST-COMPOSE-<<=-WHEN-ALIST-KEYS-SAME))
             (svex-alist-<<= (neteval-ordering-compile x network1)
                             (neteval-ordering-compile x network2)))
    :hints(("Goal" :in-theory (enable svex-alist-<<=))))

  (defthm neteval-sigordering-compile-preserves-<<=
    (implies (and (or (svex-alist-monotonic-p network1)
                      (svex-alist-monotonic-p network2))
                  ;; (svex-alist-monotonic-p network2)
                  ;; (set-equiv (svex-alist-keys network1)
                  ;;            (svex-alist-keys network2))
                  (svex-alist-compose-<<= network1 network2))
             (svex-<<= (neteval-sigordering-compile x signal offset network1)
                       (neteval-sigordering-compile x signal offset network2)))
    :hints(("Goal" :in-theory (enable svex-<<=))))

  (defthm neteval-ordering-or-null-compile-preserves-<<=
    (implies (and (or (svex-alist-monotonic-p network1)
                      (svex-alist-monotonic-p network2))
                  ;; (svex-alist-monotonic-p network2)
                  ;; (set-equiv (svex-alist-keys network1)
                  ;;            (svex-alist-keys network2))
                  (svex-alist-compose-<<= network1 network2))
             (svex-<<= (neteval-ordering-or-null-compile x signal network1)
                       (neteval-ordering-or-null-compile x signal network2)))
    :hints(("Goal" :in-theory (enable svex-<<=))))


  (defthm neteval-ordering-compile-preserves-<<=-when-partial-monotonic
    (implies (and (bind-free '((params . params)) (params))
                  (or (svex-alist-partial-monotonic params network1)
                      (svex-alist-partial-monotonic params network2))
                  (svex-compose-alist-selfbound-keys-p params network1)
                  (svex-compose-alist-selfbound-keys-p params network2)
                  (svex-alist-compose-<<= network1 network2))
             ;; note: also svex-alist-compose-<<= because svex-alist-keys are set-equiv
             ;; (by SVEX-ALIST-COMPOSE-<<=-WHEN-ALIST-KEYS-SAME))
             (svex-alist-<<= (neteval-ordering-compile x network1)
                             (neteval-ordering-compile x network2)))
    :hints(("Goal" :in-theory (enable svex-alist-<<=))))

  (defthm neteval-sigordering-compile-preserves-<<=-when-partial-monotonic
    (implies (and (bind-free '((params . params)) (params))
                  (or (svex-alist-partial-monotonic params network1)
                      (svex-alist-partial-monotonic params network2))
                  (svex-compose-alist-selfbound-keys-p params network1)
                  (svex-compose-alist-selfbound-keys-p params network2)
                  ;; (svex-alist-monotonic-p network2)
                  ;; (set-equiv (svex-alist-keys network1)
                  ;;            (svex-alist-keys network2))
                  (svex-alist-compose-<<= network1 network2))
             (svex-<<= (neteval-sigordering-compile x signal offset network1)
                       (neteval-sigordering-compile x signal offset network2)))
    :hints(("Goal" :in-theory (enable svex-<<=))))

  (defthm neteval-ordering-or-null-compile-preserves-<<=-when-partial-monotonic
    (implies (and (bind-free '((params . params)) (params))
                  (or (svex-alist-partial-monotonic params network1)
                      (svex-alist-partial-monotonic params network2))
                  (svex-compose-alist-selfbound-keys-p params network1)
                  (svex-compose-alist-selfbound-keys-p params network2)
                  ;; (svex-alist-monotonic-p network2)
                  ;; (set-equiv (svex-alist-keys network1)
                  ;;            (svex-alist-keys network2))
                  (svex-alist-compose-<<= network1 network2))
             (svex-<<= (neteval-ordering-or-null-compile x signal network1)
                       (neteval-ordering-or-null-compile x signal network2)))
    :hints(("Goal" :in-theory (enable svex-<<=)))))


(local (defthmd svex-eval-of-var
         (Equal (svex-eval (svex-var x) env)
                (svex-env-lookup x env))
         :hints(("Goal" :in-theory (enable svex-eval)))))

(defretd eval-compose-lookup-of-neteval-ordering-compile
  (equal (svex-eval (svex-compose-lookup key compose) env)
         (if (hons-assoc-equal (svar-fix key) x)
             (svex-env-lookup key (neteval-ordering-eval x network env))
           (svex-env-lookup key env)))
  :hints (("goal" :in-theory (enable svex-compose-lookup svex-eval-of-var)
           :do-not-induct t))
  :fn neteval-ordering-compile)

(defthm svex-compose-alist-selfbound-keys-p-of-neteval-ordering-compile
  (implies (svex-compose-alist-selfbound-keys-p params network)
           (svex-compose-alist-selfbound-keys-p
            params (neteval-ordering-compile x network)))
  :hints(("Goal" :in-theory (enable svex-compose-alist-selfbound-keys-p
                                    neteval-sigordering-eval-when-signal-not-in-network
                                    eval-compose-lookup-of-neteval-ordering-compile
                                    svex-eval-of-var)
          :induct (svex-compose-alist-selfbound-keys-p params network))
         (and stable-under-simplificationp
              (let ((lit (assoc 'svex-eval-equiv clause)))
                `(:expand (,lit))))))





(defsection netcomp-<<=
  (defun-sk netcomp-<<= (comp decomp)
    (exists ordering
            (svex-alist-compose-<<= comp
                                   (neteval-ordering-compile ordering decomp))))

  
  (in-theory (disable netcomp-<<= netcomp-<<=-suff))




  (deffixcong svex-alist-equiv equal (netcomp-<<= comp decomp) comp
    :hints (("goal" :cases ((netcomp-<<= comp decomp))
             :in-theory (enable netcomp-<<=)
             :use ((:instance netcomp-<<=-suff
                    (comp (svex-alist-fix comp))
                    (ordering (netcomp-<<=-witness comp decomp)))
                   (:instance netcomp-<<=-suff
                    (ordering (netcomp-<<=-witness (svex-alist-fix comp) decomp)))))))

  (deffixcong svex-alist-equiv equal (netcomp-<<= comp decomp) decomp
    :hints (("goal" :cases ((netcomp-<<= comp decomp))
             :in-theory (enable netcomp-<<=)
             :use ((:instance netcomp-<<=-suff
                    (decomp (svex-alist-fix decomp))
                    (ordering (netcomp-<<=-witness comp decomp)))
                   (:instance netcomp-<<=-suff
                    (ordering (netcomp-<<=-witness comp (svex-alist-fix decomp))))))))

  (defcong svex-alist-eval-equiv equal (netcomp-<<= comp decomp) 1
    :hints (("goal" :cases ((netcomp-<<= comp decomp))
             :in-theory (enable netcomp-<<=)
             :use ((:instance netcomp-<<=-suff
                    (comp comp-equiv)
                    (ordering (netcomp-<<=-witness comp decomp)))
                   (:instance netcomp-<<=-suff
                    (ordering (netcomp-<<=-witness comp-equiv decomp)))))))

  (defcong svex-alist-eval-equiv equal (netcomp-<<= comp decomp) 2
    :hints (("goal" :cases ((netcomp-<<= comp decomp))
             :in-theory (enable netcomp-<<=)
             :use ((:instance netcomp-<<=-suff
                    (decomp decomp-equiv)
                    (ordering (netcomp-<<=-witness comp decomp)))
                   (:instance netcomp-<<=-suff
                    (ordering (netcomp-<<=-witness comp decomp-equiv)))))))

  (define netcomp-<<=-same-keys-witness ((comp svex-alist-p)
                                        (decomp svex-alist-p))
    :non-executable t
    :returns (ord neteval-ordering-p)
    :verify-guards nil
    ;; Despite only requiring that comp is compose-<<= netcomp-<<= actually
    ;; assures that there is an ordering that is eval-equiv.
    (neteval-ordering-extract (svex-alist-keys comp)
                              (netcomp-<<=-witness (svex-alist-fix comp)
                                                  (svex-alist-fix decomp)))
    ///

    (defret alist-keys-of-<fn>
      (equal (alist-keys ord)
             (svex-alist-keys comp)))

    ;; (defthm svex-alist-compextract-keys-under-compose-equiv
    ;;   (svex-alist-<<= (svex-alist-compextract (svex-alist-keys x) x) x)
    ;;   :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))
    ;;          (and stable-under-simplificationp
    ;;               '(:in-theory (enable svex-compose-lookup)))))

    (defret netcomp-<<=-implies-same-keys-witness
      (implies (netcomp-<<= comp decomp)
               (svex-alist-<<= comp (neteval-ordering-compile ord decomp)))
      :hints (("goal" 
               :in-theory (e/d (svex-alist-<<=-in-terms-of-lookup)
                               (svex-alist-compose-<<=-necc))
               :use ((:instance netcomp-<<=
                      (comp (svex-alist-fix comp))
                      (decomp (svex-alist-fix decomp)))
                     (:instance svex-alist-compose-<<=-necc
                      (x comp) (y (neteval-ordering-compile
                                   (netcomp-<<=-witness (svex-alist-fix comp)
                                                       (svex-alist-fix decomp))
                                   decomp))
                      (var (svex-alist-<<=-lookup-witness
                            comp (svex-alist-compextract
                                  (svex-alist-keys comp)
                                  (neteval-ordering-compile
                                   (netcomp-<<=-witness (svex-alist-fix comp)
                                                       (svex-alist-fix decomp))
                                   decomp)))))))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-compose-lookup)))))

    (defthmd netcomp-<<=-redef
      (equal (netcomp-<<= comp decomp)
             (let ((ordering (netcomp-<<=-same-keys-witness comp decomp)))
               (svex-alist-<<= comp (neteval-ordering-compile ordering decomp))))
      :hints (("goal" :cases ((netcomp-<<= comp decomp))
               :use ((:instance netcomp-<<=-suff
                      (ordering (netcomp-<<=-same-keys-witness comp decomp))))
               :in-theory (e/d (netcomp-<<=-implies-same-keys-witness)
                               (netcomp-<<=-suff
                                netcomp-<<=-same-keys-witness))))
      :rule-classes :definition))


  (local (defthm svex-compose-lookup-of-append
           (equal (Svex-compose-lookup key (append x y))
                  (or (svex-lookup key x)
                      (svex-compose-lookup key y)))
           :hints(("Goal" :in-theory (enable svex-compose-lookup)))))

  (local (defthm svex-eval-equiv-of-svex-lookup-when-compose-equiv
           (implies (and (svex-alist-compose-equiv x y)
                         (svex-lookup k x) (svex-lookup k y))
                    (equal (svex-eval-equiv (svex-lookup k x) (svex-lookup k y)) t))
           :hints (("goal" :use ((:instance svex-alist-compose-equiv-necc
                                  (var k)))
                    :in-theory (e/d (svex-compose-lookup)
                                    (svex-alist-compose-equiv-necc))))))
  


  (defthmd netcomp-<<=-transitive
    (implies (and (netcomp-<<= x y)
                  (netcomp-<<= y z)
                  (or (svex-alist-monotonic-p y)
                      (svex-alist-monotonic-p z)))
             (netcomp-<<= x z))
    :hints (("goal" :expand ((netcomp-<<= x y)
                             (netcomp-<<= y z))
             :in-theory (enable svex-alist-<<=-transitive-1
                                svex-alist-<<=-transitive-2)
             :use ((:instance netcomp-<<=-suff
                    (comp x) (decomp z)
                    (ordering (neteval-ordering-compose (netcomp-<<=-same-keys-witness x y)
                                                        (netcomp-<<=-same-keys-witness y z))))))))

  (defthmd netcomp-<<=-transitive-when-partial-monotonic
    (implies (and (netcomp-<<= x y)
                  (netcomp-<<= y z)
                  (bind-free '((params . params)) (params))
                  (or (svex-alist-partial-monotonic params y)
                      (svex-alist-partial-monotonic params z))
                  (svex-compose-alist-selfbound-keys-p params y)
                  (svex-compose-alist-selfbound-keys-p params z))
             (netcomp-<<= x z))
    :hints (("goal" :expand ((netcomp-<<= x y)
                             (netcomp-<<= y z))
             :in-theory (enable svex-alist-<<=-transitive-1
                                svex-alist-<<=-transitive-2)
             :use ((:instance netcomp-<<=-suff
                    (comp x) (decomp z)
                    (ordering (neteval-ordering-compose (netcomp-<<=-same-keys-witness x y)
                                                        (netcomp-<<=-same-keys-witness y z))))))))

  (defthmd netcomp-<<=-transitive2
    (implies (and (netcomp-<<= y z)
                  (netcomp-<<= x y)
                  (or (svex-alist-monotonic-p y)
                      (svex-alist-monotonic-p z)))
             (netcomp-<<= x z))
    :hints(("Goal" :in-theory (enable netcomp-<<=-transitive))))


  (defthmd netcomp-<<=-transitive2-when-partial-monotonic
    (implies (and (netcomp-<<= y z)
                  (netcomp-<<= x y)
                  (bind-free '((params . params)) (params))
                  (or (svex-alist-partial-monotonic params y)
                      (svex-alist-partial-monotonic params z))
                  (svex-compose-alist-selfbound-keys-p params y)
                  (svex-compose-alist-selfbound-keys-p params z))
             (netcomp-<<= x z))
    :hints(("Goal" :in-theory (enable netcomp-<<=-transitive-when-partial-monotonic))))

  (defthm netcomp-<<=-reflexive
    (netcomp-<<= x x)
    :hints (("goal" :use ((:instance netcomp-<<=-suff
                           (comp x) (decomp x)
                           (ordering (neteval-ordering-identity (svex-alist-keys x)))))
             :in-theory (enable svex-alist-eval-equiv))))


  (defthm svex-alist-<<=-of-svex-alist-reduce
    (implies (svex-alist-<<= x y)
             (svex-alist-<<= (svex-alist-reduce keys x)
                            (svex-alist-reduce keys y)))
    :hints (("goal" :expand ((:with svex-alist-<<=-in-terms-of-lookup
                              (svex-alist-<<= (svex-alist-reduce keys x)
                                             (svex-alist-reduce keys y)))))))

  (defthm netcomp-<<=-of-svex-alist-reduce
    (implies (netcomp-<<= x y)
             (netcomp-<<= (svex-alist-reduce keys x) y))
    :hints (("goal" :use ((:instance netcomp-<<=-suff
                           (comp (svex-alist-reduce keys x))
                           (decomp y)
                           (ordering (neteval-ordering-reduce keys (netcomp-<<=-same-keys-witness x y)))))
             :expand ((netcomp-<<= x y)))))
  
  (defthm append-svex-alist-eval-when-svex-alist-compose-equiv
    (implies (svex-alist-compose-equiv x y)
             (svex-envs-similar (append (svex-alist-eval x env) env)
                                (append (svex-alist-eval y env) env)))
    :hints(("Goal" :in-theory (e/d (svex-envs-similar svex-compose-lookup)
                                   (svex-alist-compose-equiv-necc
                                    svex-alist-compose-equiv-implies-svex-eval-equiv-svex-compose-lookup-2))
            :expand ((:free (var) (svex-eval (svex-var var) env)))
            :use ((:instance svex-alist-compose-equiv-necc
                   (var (svex-envs-similar-witness
                         (append (svex-alist-eval x env) env)
                                (append (svex-alist-eval y env) env)))))))
    :rule-classes :congruence)
            

  (defcong svex-alist-compose-equiv svex-eval-equiv
    (svex-compose x subst) 2
    :hints(("Goal" :in-theory (enable svex-eval-equiv))))

  (defcong svex-alist-compose-equiv svex-alist-eval-equiv
    (svex-alist-compose x subst) 2
    :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))))


  (defthm svex-alist-<<=-of-svex-alist-compose
    (implies (and (svex-alist-<<= x y)
                  (svex-alist-compose-<<= a b)
                  (or (svex-alist-monotonic-p x)
                      (svex-alist-monotonic-p y)))
             (svex-alist-<<= (svex-alist-compose x a)
                            (svex-alist-compose y b)))
    :hints (("goal" :use ((:instance svex-alist-<<=-transitive-1
                           (x (svex-alist-compose x a))
                           (y (svex-alist-compose x b))
                           (z (svex-alist-compose y b)))
                          (:instance svex-alist-<<=-transitive-1
                           (x (svex-alist-compose x a))
                           (y (svex-alist-compose y a))
                           (z (svex-alist-compose y b)))))))


  (defthm netcomp-<<=-of-svex-alist-compose
    (implies (and (netcomp-<<= x network)
                  (netcomp-<<= subst network)
                  (or (svex-alist-monotonic-p network)
                      (svex-alist-monotonic-p x)))
             (netcomp-<<= (svex-alist-compose x subst) network))
    :hints (("goal" :use ((:instance netcomp-<<=-suff
                           (comp (svex-alist-compose x subst))
                           (decomp network)
                           (ordering (neteval-ordering-compose-aux
                                      (netcomp-<<=-same-keys-witness x network)
                                      (netcomp-<<=-same-keys-witness subst network)))))
             :expand ((netcomp-<<= x network)
                      (netcomp-<<= subst network)))))


  (defthm svex-env-extract-of-append-eval-selfbound
    (implies (svex-compose-alist-selfbound-keys-p params a)
             (equal (svex-env-extract params (append (svex-alist-eval a env) env))
                    (svex-env-extract params env)))
    :hints(("Goal" :in-theory (enable svex-compose-alist-selfbound-keys-p
                                      svex-env-extract
                                      svex-eval-of-var))))

  (defthm svex-alist-<<=-of-svex-alist-compose-when-partial-monotonic-lemma
    (implies (and (svex-alist-compose-<<= a b)
                  (svex-alist-partial-monotonic params x)
                  (svex-compose-alist-selfbound-keys-p params a)
                  (svex-compose-alist-selfbound-keys-p params b))
             (svex-alist-<<= (svex-alist-compose x a)
                             (svex-alist-compose x b)))
    :hints(("Goal" :in-theory (enable svex-alist-<<=))))

  
  (defthm svex-alist-<<=-of-svex-alist-compose-when-partial-monotonic
    (implies (and (svex-alist-<<= x y)
                  (svex-alist-compose-<<= a b)
                  (bind-free '((params . params)) (params))
                  (or (svex-alist-partial-monotonic params x)
                      (svex-alist-partial-monotonic params y))
                  (svex-compose-alist-selfbound-keys-p params a)
                  (svex-compose-alist-selfbound-keys-p params b))
             (svex-alist-<<= (svex-alist-compose x a)
                             (svex-alist-compose y b)))
    :hints (("goal" :use ((:instance svex-alist-<<=-transitive-1
                           (x (svex-alist-compose x a))
                           (y (svex-alist-compose x b))
                           (z (svex-alist-compose y b)))
                          (:instance svex-alist-<<=-transitive-1
                           (x (svex-alist-compose x a))
                           (y (svex-alist-compose y a))
                           (z (svex-alist-compose y b)))))))

  (defthm netcomp-<<=-of-svex-alist-compose-when-partial-monotonic-1
    (implies (and (netcomp-<<= x network)
                  (netcomp-<<= subst network)
                  (svex-alist-partial-monotonic params network)
                  (svex-compose-alist-selfbound-keys-p params network)
                  (svex-compose-alist-selfbound-keys-p params subst))
             (netcomp-<<= (svex-alist-compose x subst) network))
    :hints (("goal" :use ((:instance netcomp-<<=-suff
                           (comp (svex-alist-compose x subst))
                           (decomp network)
                           (ordering (neteval-ordering-compose-aux
                                      (netcomp-<<=-same-keys-witness x network)
                                      (netcomp-<<=-same-keys-witness subst network)))))
             :expand ((netcomp-<<= x network)
                      (netcomp-<<= subst network)))))
  
  (defthm netcomp-<<=-of-svex-alist-compose-when-partial-monotonic-2
    (implies (and (netcomp-<<= x network)
                  (netcomp-<<= subst network)
                  (svex-alist-partial-monotonic params x)
                  (svex-compose-alist-selfbound-keys-p params network)
                  (svex-compose-alist-selfbound-keys-p params subst))
             (netcomp-<<= (svex-alist-compose x subst) network))
    :hints (("goal" :use ((:instance netcomp-<<=-suff
                           (comp (svex-alist-compose x subst))
                           (decomp network)
                           (ordering (neteval-ordering-compose-aux
                                      (netcomp-<<=-same-keys-witness x network)
                                      (netcomp-<<=-same-keys-witness subst network)))))
             :expand ((netcomp-<<= x network)
                      (netcomp-<<= subst network)))))

  (defthm svex-alist-compose-of-svex-identity-subst
    (implies (subsetp-equal vars (svex-alist-keys x))
             (equal (svex-alist-compose (svex-identity-subst vars) x)
                    (svex-alist-reduce vars x)))
    :hints(("Goal" :in-theory (enable svex-alist-compose
                                      ;; svex-alist-keys
                                      svex-identity-subst
                                      svarlist-fix
                                      svex-acons
                                      svex-compose
                                      pairlis$
                                      svarlist->svexes
                                      svex-alist-reduce))))

  (defthm netcomp-<<=-of-svex-identity-subst
    (implies (subsetp-equal (svarlist-fix vars) (svex-alist-keys network))
             (netcomp-<<= (svex-identity-subst vars) network))
    :hints (("goal" :use ((:instance netcomp-<<=-suff
                           (comp (svex-identity-subst vars))
                           (decomp network)
                           (ordering (neteval-ordering-null vars))))
             :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent
                                svex-envs-equivalent))))

  (defthm svex-alist-keys-of-append
    (equal (svex-alist-keys (append x y))
           (append (svex-alist-keys x)
                   (svex-alist-keys y)))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (defthm svex-alist-<<=-of-append
    (implies (and (set-equiv (svex-alist-keys x1)
                             (svex-alist-keys x2))
                  (svex-alist-<<= x1 x2)
                  (svex-alist-<<= y1 y2))
             (svex-alist-<<= (append x1 y1)
                            (append x2 y2)))
    :hints (("goal" :expand ((:with svex-alist-<<=-in-terms-of-lookup
                              (svex-alist-<<= (append x1 y1)
                                             (append x2 y2))))
             :in-theory (e/d (svex-lookup-iff-member-svex-alist-keys)
                             (member-svex-alist-keys)))))

  (defthm netcomp-<<=-of-append
    (implies (and (netcomp-<<= x network)
                  (netcomp-<<= y network))
             (netcomp-<<= (append x y) network))
    :hints (("goal" :expand ((netcomp-<<= x network)
                             (netcomp-<<= y network)
                             (SVEX-ALIST-compose-equiv
                              (APPEND X Y)
                              (APPEND (NETEVAL-ORDERING-COMPILE (NETCOMP-<<=-SAME-KEYS-WITNESS X NETWORK)
                                                                NETWORK)
                                      (NETEVAL-ORDERING-COMPILE (NETCOMP-<<=-SAME-KEYS-WITNESS Y NETWORK)
                                                                NETWORK))))
             :in-theory (disable svex-lookup-of-neteval-ordering-compile)
             :use ((:instance netcomp-<<=-suff
                    (comp (append x y)) (decomp network)
                    (ordering (append (netcomp-<<=-same-keys-witness x network)
                                      (netcomp-<<=-same-keys-witness y network)))))
             :do-not-induct t)))

  (defthm netcomp-<<=-of-nil
    (netcomp-<<= nil network)
    :hints (("goal" :use ((:instance netcomp-<<=-suff
                           (comp nil) (decomp network)
                           (ordering nil)))
             :expand ((neteval-ordering-compile nil network)))))

  (defthmd netcomp-<<=-when-<<=-netcomp
    (implies (and (netcomp-p y z)
                  (svex-alist-compose-<<= x y))
             (netcomp-<<= x z))
    :hints (("goal" :expand ((netcomp-p y z))
             :use ((:instance netcomp-<<=-suff
                    (comp x) (decomp z)
                    (ordering (netcomp-p-eval-equiv-witness y z)))))))

  (local (defthm neteval-ordering-compile-preserves-<<=-free
           (implies (and (svex-alist-eval-equiv y (neteval-ordering-compile x network1))
                         (or (svex-alist-monotonic-p network1)
                             (svex-alist-monotonic-p network2))
                         (svex-alist-compose-<<= network1 network2))
                    (svex-alist-<<= y (neteval-ordering-compile x network2)))))

  (defthmd netcomp-<<=-when-netcomp-of-<<=
    (implies (and (netcomp-p x y)
                  (svex-alist-compose-<<= y z)
                  (or (svex-alist-monotonic-p y)
                      (svex-alist-monotonic-p z)))
             (netcomp-<<= x z))
    :hints (("goal" :expand ((netcomp-p x y))
             :use ((:instance netcomp-<<=-suff
                    (comp x) (decomp z)
                    (ordering (netcomp-p-eval-equiv-witness x y)))))))
  
  (defthmd netcomp-<<=-when-netcomp-of-<<=-partial-monotonic
    (implies (and (netcomp-p x y)
                  (svex-alist-compose-<<= y z)
                  (or (svex-alist-partial-monotonic params y)
                      (svex-alist-partial-monotonic params z))
                  (svex-compose-alist-selfbound-keys-p params y)
                  (svex-compose-alist-selfbound-keys-p params z))
             (netcomp-<<= x z))
    :hints (("goal" :expand ((netcomp-p x y))
             :use ((:instance netcomp-<<=-suff
                    (comp x) (decomp z)
                    (ordering (netcomp-p-eval-equiv-witness x y)))
                   (:instance neteval-ordering-compile-preserves-<<=-when-partial-monotonic
                    (x (netcomp-p-eval-equiv-witness x y))
                    (network1 y)
                    (network2 z))))))

  ;; (defthm netevalcomp-p-when-netcomp-<<=
  ;;   (implies (netcomp-<<= x y)
  ;;            (netevalcomp-p (svex-alist-compose x (svarlist-x-subst (svex-alist-keys y))) y))
  ;;   :hints (("goal" :expand ((netcomp-<<= x y))
  ;;            :use ((:instance netevalcomp-p-suff
  ;;                   (comp (svex-alist-compose x (svarlist-x-subst (svex-alist-keys y))))
  ;;                   (network y)
  ;;                   (ordering (netcomp-<<=-same-keys-witness x y)))))))
  )



