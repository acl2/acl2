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


(defthm compose-conservatively-modified-ok
  (implies (and (netcomp-p part-composed orig)
                (svex-alist-compose-[= modified part-composed)
                (netcomp-p final-composed modified)
                (svex-alist-monotonic-p orig))
           (let ((witness (neteval-ordering-compose
                           (netcomp-p-eval-equiv-witness final-composed modified)
                           (netcomp-p-eval-equiv-witness part-composed orig))))
             (svex-alist-[= final-composed
                            (neteval-ordering-compile witness orig))))
  :hints(("Goal" :in-theory (enable netcomp-p-redef)
          :use ((:instance neteval-ordering-compile-preserves-[=
                 (x (netcomp-p-eval-equiv-witness final-composed modified))
                 (network1 modified)
                 (network2 part-composed))
                (:instance neteval-ordering-compile-monotonic
                 (x (netcomp-p-eval-equiv-witness part-composed orig))
                 (network orig))))))
         
