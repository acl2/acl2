; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
(include-book "compose-theory-base")
(include-book "svex-lattice")
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "arithmetic/top" :Dir :system))
;;(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))





(local (defthm alist-keys-of-neteval-ordering-eval
         (equal (alist-keys (neteval-ordering-eval x network env))
                (alist-keys (neteval-ordering-fix x)))
         :hints(("Goal" :in-theory (enable alist-keys)
                 :induct (neteval-ordering-selfinduct x)
                 :expand ((neteval-ordering-eval x network env))))))
                 

(encapsulate nil
  (local (in-theory (enable svex-monotonic-p-necc)))
  (defthm-neteval-ordering-compile-flag
    (defthm neteval-ordering-eval-monotonic
      (implies (and (svex-alist-monotonic-p network)
                    (svex-env-[= env1 env2))
               (svex-env-[= (neteval-ordering-eval x network env1)
                            (neteval-ordering-eval x network env2)))
      :hints ('(:expand ((:free (env) (neteval-ordering-eval x network env)))))
      :flag neteval-ordering-compile)

    (defthm neteval-sigordering-eval-monotonic
      (implies (and (svex-alist-monotonic-p network)
                    (svex-env-[= env1 env2))
               (4vec-[= (neteval-sigordering-eval x signal offset network env1)
                        (neteval-sigordering-eval x signal offset network env2)))
      :hints ('(:expand ((:free (env) (neteval-sigordering-eval x signal offset network env)))))
      :flag neteval-sigordering-compile)

    (defthm neteval-ordering-or-null-eval-monotonic
      (implies (and (svex-alist-monotonic-p network)
                    (svex-env-[= env1 env2))
               (4vec-[= (neteval-ordering-or-null-eval x signal network env1)
                        (neteval-ordering-or-null-eval x signal network env2)))
      :hints ('(:expand ((:free (env) (neteval-ordering-or-null-eval x signal network env)))))
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


  (local (defthm svex-eval-mono-lemma
           (implies (and (svex-[= x1 x2)
                         (svex-env-[= env1 env2)
                         (or (svex-monotonic-p x1)
                             (svex-monotonic-p x2)))
                    (4vec-[= (svex-eval x1 env1)
                             (svex-eval x2 env2)))
           :hints (("goal" :use ((:instance svex-[=-necc
                                  (x x1) (y x2) (env env2))
                                 (:instance svex-[=-necc
                                  (x x1) (y x2) (env env1))
                                 (:instance svex-monotonic-p-necc
                                  (x x1) (env1 env1) (env2 env2))
                                 (:instance svex-monotonic-p-necc
                                  (x x2) (env1 env1) (env2 env2)))
                    :in-theory (e/d (4vec-[=-transitive-1)
                                    (svex-[=-necc
                                     svex-monotonic-p-necc))))))

  (defthm-neteval-ordering-compile-flag
    (defthm neteval-ordering-eval-preserves-[=
      (implies (and (or (svex-alist-monotonic-p network1)
                        (svex-alist-monotonic-p network2))
                    ;; (set-equiv (svex-alist-keys network1)
                    ;;            (svex-alist-keys network2))
                    (svex-alist-compose-[= network1 network2))
               (svex-env-[= (neteval-ordering-eval x network1 env)
                            (neteval-ordering-eval x network2 env)))
      :hints ('(:expand ((:free (network) (neteval-ordering-eval x network env)))))
      :flag neteval-ordering-compile)

    (defthm neteval-sigordering-eval-preserves-[=
      (implies (and (or (svex-alist-monotonic-p network1)
                        (svex-alist-monotonic-p network2))
                    ;; (svex-alist-monotonic-p network2)
                    ;; (set-equiv (svex-alist-keys network1)
                    ;;            (svex-alist-keys network2))
                    (svex-alist-compose-[= network1 network2))
               (4vec-[= (neteval-sigordering-eval x signal offset network1 env)
                        (neteval-sigordering-eval x signal offset network2 env)))
      :hints ('(:expand ((:free (network) (neteval-sigordering-eval x signal offset network env)))))
      :flag neteval-sigordering-compile)

    (defthm neteval-ordering-or-null-eval-preserves-[=
      (implies (and (or (svex-alist-monotonic-p network1)
                        (svex-alist-monotonic-p network2))
                    ;; (svex-alist-monotonic-p network2)
                    ;; (set-equiv (svex-alist-keys network1)
                    ;;            (svex-alist-keys network2))
                    (svex-alist-compose-[= network1 network2))
               (4vec-[= (neteval-ordering-or-null-eval x signal network1 env)
                        (neteval-ordering-or-null-eval x signal network2 env)))
      :hints ('(:expand ((:free (network) (neteval-ordering-or-null-eval x signal network env)))))
      :flag neteval-ordering-or-null-compile))


  (defthm neteval-ordering-compile-preserves-[=
    (implies (and (or (svex-alist-monotonic-p network1)
                      (svex-alist-monotonic-p network2))
                  (svex-alist-compose-[= network1 network2))
             ;; note: also svex-alist-compose-[= because svex-alist-keys are set-equiv
             ;; (by SVEX-ALIST-COMPOSE-[=-WHEN-ALIST-KEYS-SAME))
             (svex-alist-[= (neteval-ordering-compile x network1)
                            (neteval-ordering-compile x network2)))
    :hints(("Goal" :in-theory (enable svex-alist-[=))))

  (defthm neteval-sigordering-compile-preserves-[=
    (implies (and (or (svex-alist-monotonic-p network1)
                      (svex-alist-monotonic-p network2))
                  ;; (svex-alist-monotonic-p network2)
                  ;; (set-equiv (svex-alist-keys network1)
                  ;;            (svex-alist-keys network2))
                  (svex-alist-compose-[= network1 network2))
             (svex-[= (neteval-sigordering-compile x signal offset network1)
                      (neteval-sigordering-compile x signal offset network2)))
    :hints(("Goal" :in-theory (enable svex-[=))))

  (defthm neteval-ordering-or-null-compile-preserves-[=
    (implies (and (or (svex-alist-monotonic-p network1)
                      (svex-alist-monotonic-p network2))
                  ;; (svex-alist-monotonic-p network2)
                  ;; (set-equiv (svex-alist-keys network1)
                  ;;            (svex-alist-keys network2))
                  (svex-alist-compose-[= network1 network2))
             (svex-[= (neteval-ordering-or-null-compile x signal network1)
                      (neteval-ordering-or-null-compile x signal network2)))
    :hints(("Goal" :in-theory (enable svex-[=)))))

(defsection netcomp-[=
  (defun-sk netcomp-[= (comp decomp)
    (exists ordering
            (svex-alist-compose-[= comp
                                   (neteval-ordering-compile ordering decomp))))

  
  (in-theory (disable netcomp-[= netcomp-[=-suff))




  (deffixcong svex-alist-equiv equal (netcomp-[= comp decomp) comp
    :hints (("goal" :cases ((netcomp-[= comp decomp))
             :in-theory (enable netcomp-[=)
             :use ((:instance netcomp-[=-suff
                    (comp (svex-alist-fix comp))
                    (ordering (netcomp-[=-witness comp decomp)))
                   (:instance netcomp-[=-suff
                    (ordering (netcomp-[=-witness (svex-alist-fix comp) decomp)))))))

  (deffixcong svex-alist-equiv equal (netcomp-[= comp decomp) decomp
    :hints (("goal" :cases ((netcomp-[= comp decomp))
             :in-theory (enable netcomp-[=)
             :use ((:instance netcomp-[=-suff
                    (decomp (svex-alist-fix decomp))
                    (ordering (netcomp-[=-witness comp decomp)))
                   (:instance netcomp-[=-suff
                    (ordering (netcomp-[=-witness comp (svex-alist-fix decomp))))))))

  (defcong svex-alist-eval-equiv equal (netcomp-[= comp decomp) 1
    :hints (("goal" :cases ((netcomp-[= comp decomp))
             :in-theory (enable netcomp-[=)
             :use ((:instance netcomp-[=-suff
                    (comp comp-equiv)
                    (ordering (netcomp-[=-witness comp decomp)))
                   (:instance netcomp-[=-suff
                    (ordering (netcomp-[=-witness comp-equiv decomp)))))))

  (defcong svex-alist-eval-equiv equal (netcomp-[= comp decomp) 2
    :hints (("goal" :cases ((netcomp-[= comp decomp))
             :in-theory (enable netcomp-[=)
             :use ((:instance netcomp-[=-suff
                    (decomp decomp-equiv)
                    (ordering (netcomp-[=-witness comp decomp)))
                   (:instance netcomp-[=-suff
                    (ordering (netcomp-[=-witness comp decomp-equiv)))))))

  (define netcomp-[=-same-keys-witness ((comp svex-alist-p)
                                        (decomp svex-alist-p))
    :non-executable t
    :returns (ord neteval-ordering-p)
    :verify-guards nil
    ;; Despite only requiring that comp is compose-[= netcomp-[= actually
    ;; assures that there is an ordering that is eval-equiv.
    (neteval-ordering-extract (svex-alist-keys comp)
                              (netcomp-[=-witness (svex-alist-fix comp)
                                                  (svex-alist-fix decomp)))
    ///

    (defret alist-keys-of-<fn>
      (equal (alist-keys ord)
             (svex-alist-keys comp)))

    ;; (defthm svex-alist-compextract-keys-under-compose-equiv
    ;;   (svex-alist-[= (svex-alist-compextract (svex-alist-keys x) x) x)
    ;;   :hints(("Goal" :in-theory (enable svex-alist-eval-equiv))
    ;;          (and stable-under-simplificationp
    ;;               '(:in-theory (enable svex-compose-lookup)))))

    (defret netcomp-[=-implies-same-keys-witness
      (implies (netcomp-[= comp decomp)
               (svex-alist-[= comp (neteval-ordering-compile ord decomp)))
      :hints (("goal" 
               :in-theory (e/d (svex-alist-[=-in-terms-of-lookup)
                               (svex-alist-compose-[=-necc))
               :use ((:instance netcomp-[=
                      (comp (svex-alist-fix comp))
                      (decomp (svex-alist-fix decomp)))
                     (:instance svex-alist-compose-[=-necc
                      (x comp) (y (neteval-ordering-compile
                                   (netcomp-[=-witness (svex-alist-fix comp)
                                                       (svex-alist-fix decomp))
                                   decomp))
                      (var (svex-alist-[=-lookup-witness
                            comp (svex-alist-compextract
                                  (svex-alist-keys comp)
                                  (neteval-ordering-compile
                                   (netcomp-[=-witness (svex-alist-fix comp)
                                                       (svex-alist-fix decomp))
                                   decomp)))))))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-compose-lookup)))))

    (defthmd netcomp-[=-redef
      (equal (netcomp-[= comp decomp)
             (let ((ordering (netcomp-[=-same-keys-witness comp decomp)))
               (svex-alist-[= comp (neteval-ordering-compile ordering decomp))))
      :hints (("goal" :cases ((netcomp-[= comp decomp))
               :use ((:instance netcomp-[=-suff
                      (ordering (netcomp-[=-same-keys-witness comp decomp))))
               :in-theory (e/d (netcomp-[=-implies-same-keys-witness)
                               (netcomp-[=-suff
                                netcomp-[=-same-keys-witness))))
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
  


  (defthmd netcomp-[=-transitive
    (implies (and (netcomp-[= x y)
                  (netcomp-[= y z)
                  (or (svex-alist-monotonic-p y)
                      (svex-alist-monotonic-p z)))
             (netcomp-[= x z))
    :hints (("goal" :expand ((netcomp-[= x y)
                             (netcomp-[= y z))
             :in-theory (enable svex-alist-[=-transitive-1
                                svex-alist-[=-transitive-2)
             :use ((:instance netcomp-[=-suff
                    (comp x) (decomp z)
                    (ordering (neteval-ordering-compose (netcomp-[=-same-keys-witness x y)
                                                        (netcomp-[=-same-keys-witness y z))))))))

  (defthmd netcomp-[=-transitive2
    (implies (and (netcomp-[= y z)
                  (netcomp-[= x y)
                  (or (svex-alist-monotonic-p y)
                      (svex-alist-monotonic-p z)))
             (netcomp-[= x z))
    :hints(("Goal" :in-theory (enable netcomp-[=-transitive))))

  (defthm netcomp-[=-reflexive
    (netcomp-[= x x)
    :hints (("goal" :use ((:instance netcomp-[=-suff
                           (comp x) (decomp x)
                           (ordering (neteval-ordering-identity (svex-alist-keys x)))))
             :in-theory (enable svex-alist-eval-equiv))))

  (defthm svex-alist-keys-of-svex-alist-reduce
    (equal (svex-alist-keys (svex-alist-reduce keys a))
           (intersection-equal (svarlist-fix keys) (svex-alist-keys a)))
    :hints(("Goal" :in-theory (enable svex-alist-reduce svex-alist-keys))))

  (defthm svex-alist-[=-of-svex-alist-reduce
    (implies (svex-alist-[= x y)
             (svex-alist-[= (svex-alist-reduce keys x)
                            (svex-alist-reduce keys y)))
    :hints (("goal" :expand ((:with svex-alist-[=-in-terms-of-lookup
                              (svex-alist-[= (svex-alist-reduce keys x)
                                             (svex-alist-reduce keys y)))))))

  (defthm netcomp-[=-of-svex-alist-reduce
    (implies (netcomp-[= x y)
             (netcomp-[= (svex-alist-reduce keys x) y))
    :hints (("goal" :use ((:instance netcomp-[=-suff
                           (comp (svex-alist-reduce keys x))
                           (decomp y)
                           (ordering (neteval-ordering-reduce keys (netcomp-[=-same-keys-witness x y)))))
             :expand ((netcomp-[= x y)))))
  
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

  
  (defthm svex-alist-keys-of-svex-alist-compose
    (equal (Svex-alist-keys (Svex-alist-compose x y))
           (svex-alist-keys x))
    :hints(("Goal" :in-theory (enable svex-alist-compose svex-alist-keys))))

  (defthm svex-alist-[=-of-svex-alist-compose
    (implies (and (svex-alist-[= x y)
                  (svex-alist-compose-[= a b)
                  (or (svex-alist-monotonic-p x)
                      (svex-alist-monotonic-p y)))
             (svex-alist-[= (svex-alist-compose x a)
                            (svex-alist-compose y b)))
    :hints (("goal" :use ((:instance svex-alist-[=-transitive-1
                           (x (svex-alist-compose x a))
                           (y (svex-alist-compose x b))
                           (z (svex-alist-compose y b)))
                          (:instance svex-alist-[=-transitive-1
                           (x (svex-alist-compose x a))
                           (y (svex-alist-compose y a))
                           (z (svex-alist-compose y b)))))))


  (defthm netcomp-[=-of-svex-alist-compose
    (implies (and (netcomp-[= x network)
                  (netcomp-[= subst network)
                  (or (svex-alist-monotonic-p network)
                      (svex-alist-monotonic-p x)))
             (netcomp-[= (svex-alist-compose x subst) network))
    :hints (("goal" :use ((:instance netcomp-[=-suff
                           (comp (svex-alist-compose x subst))
                           (decomp network)
                           (ordering (neteval-ordering-compose-aux
                                      (netcomp-[=-same-keys-witness x network)
                                      (netcomp-[=-same-keys-witness subst network)))))
             :expand ((netcomp-[= x network)
                      (netcomp-[= subst network)))))

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

  (defthm netcomp-[=-of-svex-identity-subst
    (implies (subsetp-equal (svarlist-fix vars) (svex-alist-keys network))
             (netcomp-[= (svex-identity-subst vars) network))
    :hints (("goal" :use ((:instance netcomp-[=-suff
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

  (Defthmd svex-lookup-iff-member-svex-alist-keys
    (iff (svex-lookup v x)
         (member-equal (svar-fix v) (svex-alist-keys x))))

  (defthm svex-alist-[=-of-append
    (implies (and (set-equiv (svex-alist-keys x1)
                             (svex-alist-keys x2))
                  (svex-alist-[= x1 x2)
                  (svex-alist-[= y1 y2))
             (svex-alist-[= (append x1 y1)
                            (append x2 y2)))
    :hints (("goal" :expand ((:with svex-alist-[=-in-terms-of-lookup
                              (svex-alist-[= (append x1 y1)
                                             (append x2 y2))))
             :in-theory (e/d (svex-lookup-iff-member-svex-alist-keys)
                             (member-svex-alist-keys)))))

  (defthm netcomp-[=-of-append
    (implies (and (netcomp-[= x network)
                  (netcomp-[= y network))
             (netcomp-[= (append x y) network))
    :hints (("goal" :expand ((netcomp-[= x network)
                             (netcomp-[= y network)
                             (SVEX-ALIST-compose-equiv
                              (APPEND X Y)
                              (APPEND (NETEVAL-ORDERING-COMPILE (NETCOMP-[=-SAME-KEYS-WITNESS X NETWORK)
                                                                NETWORK)
                                      (NETEVAL-ORDERING-COMPILE (NETCOMP-[=-SAME-KEYS-WITNESS Y NETWORK)
                                                                NETWORK))))
             :in-theory (disable svex-lookup-of-neteval-ordering-compile)
             :use ((:instance netcomp-[=-suff
                    (comp (append x y)) (decomp network)
                    (ordering (append (netcomp-[=-same-keys-witness x network)
                                      (netcomp-[=-same-keys-witness y network)))))
             :do-not-induct t)))

  (defthm netcomp-[=-of-nil
    (netcomp-[= nil network)
    :hints (("goal" :use ((:instance netcomp-[=-suff
                           (comp nil) (decomp network)
                           (ordering nil)))
             :expand ((neteval-ordering-compile nil network)))))

  (defthmd netcomp-[=-when-[=-netcomp
    (implies (and (netcomp-p y z)
                  (svex-alist-compose-[= x y))
             (netcomp-[= x z))
    :hints (("goal" :expand ((netcomp-p y z))
             :use ((:instance netcomp-[=-suff
                    (comp x) (decomp z)
                    (ordering (netcomp-p-eval-equiv-witness y z)))))))

  (local (defthm neteval-ordering-compile-preserves-[=-free
           (implies (and (svex-alist-eval-equiv y (neteval-ordering-compile x network1))
                         (or (svex-alist-monotonic-p network1)
                             (svex-alist-monotonic-p network2))
                         (svex-alist-compose-[= network1 network2))
                    (svex-alist-[= y (neteval-ordering-compile x network2)))))

  (defthmd netcomp-[=-when-netcomp-of-[=
    (implies (and (netcomp-p x y)
                  (svex-alist-compose-[= y z)
                  (or (svex-alist-monotonic-p y)
                      (svex-alist-monotonic-p z)))
             (netcomp-[= x z))
    :hints (("goal" :expand ((netcomp-p x y))
             :use ((:instance netcomp-[=-suff
                    (comp x) (decomp z)
                    (ordering (netcomp-p-eval-equiv-witness x y)))))))

  (defthm netevalcomp-p-when-netcomp-[=
    (implies (netcomp-[= x y)
             (netevalcomp-p (svex-alist-compose x (svarlist-x-subst (svex-alist-keys y))) y))
    :hints (("goal" :expand ((netcomp-[= x y))
             :use ((:instance netevalcomp-p-suff
                    (comp (svex-alist-compose x (svarlist-x-subst (svex-alist-keys y))))
                    (network y)
                    (ordering (netcomp-[=-same-keys-witness x y))))))))

