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

(include-book "svtv-data-obj-spec")
(include-book "svtv-idealize-defs")
(include-book "fsm-override-smart-check")
(include-book "svtv-generalize-defs")
(include-book "override-envlist-defs")
(include-book "std/util/defredundant" :dir :system)

(local (include-book "../svex/fixpoint-override"))
(local (include-book "svtv-spec-override-transparency"))
(local (include-book "svtv-stobj-pipeline-monotonicity"))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "../svex/compose-theory-ovmonotonicity"))
(local (include-book "clause-processors/find-subterms" :dir :system))

(std::defredundant :names (svtv-spec-stimulus-equiv
                           svtv-spec-stimulus-equiv-is-an-equivalence
                           svtv-spec-stimulus-equiv-implies-equal-svtv-spec-override-syntax-checks-1))
  


(defsection override-transparency-of-svtv-data-obj->ideal-spec
  (local (defthm svex-env-reduce-is-extract
           (svex-envs-similar (svex-env-reduce keys x)
                              (svex-env-extract keys x))
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))


  (local
   (defthm svex-env-<<=-of-append-svex-env-extracts
     (iff (svex-env-<<= (append (svex-env-extract keys1 x)
                                (svex-env-extract keys2 x))
                        y)
          (and (svex-env-<<= (svex-env-extract keys1 x) y)
               (svex-env-<<= (svex-env-extract keys2 x) y)))
     :hints ((and stable-under-simplificationp
                  (b* ((lit (assoc 'svex-env-<<= clause))
                       (append-p (and (consp (cadr lit))
                                      (eq (caadr lit) 'acl2::binary-append))))
                    (if append-p
                        `(:expand (,lit)
                          :use ((:instance svex-env-<<=-necc
                                 (x (svex-env-extract keys1 x))
                                 (var (svex-env-<<=-witness . ,(cdr lit))))
                                (:instance svex-env-<<=-necc
                                 (x (svex-env-extract keys2 x))
                                 (var (svex-env-<<=-witness . ,(cdr lit)))))
                          :in-theory (disable svex-env-<<=-necc))
                      `(:expand (,lit)
                        :use ((:instance svex-env-<<=-necc
                               (x (append (svex-env-extract keys1 x)
                                          (svex-env-extract keys2 x)))
                               (var (svex-env-<<=-witness . ,(cdr lit)))))
                        :in-theory (disable svex-env-<<=-necc))))))))
  
  (local (defcong svex-alist-keys-equiv set-equiv (svtv-assigns-override-vars assigns config) 1
           :hints(("Goal" :in-theory (enable svtv-assigns-override-vars
                                             svex-alist-keys-equiv)))))
  
  (local (defthm flatnorm-res->assigns-of-design->flatnorm
           (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                         (svtv-data-obj->flatten-validp x)
                         (svtv-data-obj->flatnorm-validp x)
                         (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup x)))
                    (svex-alist-eval-equiv! (FLATNORM-RES->ASSIGNS (DESIGN->FLATNORM (SVTV-DATA-OBJ->DESIGN X)))
                                            (flatnorm-res->assigns (svtv-data-obj->flatnorm x))))
           :hints(("Goal" :in-theory (enable design->flatnorm
                                             svtv-normalize-assigns)))))

  (local (defthm flatnorm-res->delays-of-design->flatnorm
           (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                         (svtv-data-obj->flatten-validp x)
                         (svtv-data-obj->flatnorm-validp x)
                         (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup x)))
                    (equal (FLATNORM-RES->DELAYS (DESIGN->FLATNORM (SVTV-DATA-OBJ->DESIGN X)))
                           (flatnorm-res->delays (svtv-data-obj->flatnorm x))))
           :hints(("Goal" :in-theory (enable design->flatnorm
                                             flatnorm-of-svtv-data-obj
                                             svtv-normalize-assigns)))))

  (local (in-theory (disable FLATNORM-OF-SVTV-DATA-OBJ)))

  (local (defthm design-flatten-okp-of-svtv-data-obj
           (b* (((svtv-data-obj x)))
             (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                           x.flatten-validp)
                      (design-flatten-okp x.design)))
           :hints(("Goal" :in-theory (enable design-flatten-okp)))))
   
  (defthm override-transparency-of-svtv-data-obj->ideal-spec
    (b* (((svtv-spec spec) (svtv-data-obj->ideal-spec x))
         ((svtv-data-obj x))
         ((flatnorm-res x.flatnorm))
         (spec-run (svtv-spec-run spec spec-env :base-ins base-ins :initst spec-initst))
         (impl-run (svtv-spec-run spec pipe-env))
         (overridekeys (svtv-assigns-override-vars x.flatnorm.assigns
                                                   (phase-fsm-config->override-config x.phase-fsm-setup))))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup)

                    (svtv-spec-override-syntax-checks spec overridekeys triplemaps)

                    
                    (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run)
                    (svex-env-<<= (svex-env-reduce (append (svex-alist-vars spec.initst-alist)
                                                           (svex-alistlist-vars spec.in-alists))
                                                   pipe-env)
                                  spec-env)

                    (svarlist-nonoverride-p (svex-envlist-all-keys base-ins) :test))
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :in-theory (e/d (svtv-data-obj->ideal-spec)
                                   (design->ideal-fsm-overridekey-transparent))
            :use ((:instance design->ideal-fsm-overridekey-transparent
                   (x (svtv-data-obj->design x))
                   (config (svtv-data-obj->phase-fsm-setup x)))))))

  

  (local (defthm svarlist-addr-p-of-flatnorm-res->assigns-vars
           (B* (((svtv-data-obj x)))
             (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                           x.flatten-validp
                           x.flatnorm-validp)
                      (svarlist-addr-p (svex-alist-vars (flatnorm-res->assigns x.flatnorm)))))
           :hints(("Goal" :use flatnorm-of-svtv-data-obj
                   :in-theory (disable flatnorm-of-svtv-data-obj)))))

  (defthm base-fsm-ovmonotonic-of-svtv-data-obj->phase-fsm
    (b* (((svtv-data-obj x)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup))
               (base-fsm-ovmonotonic x.phase-fsm)))
    ;; :hints(("Goal" :in-theory (e/d (;; base-fsm-ovcongruent
    ;;                                 ;; phase-fsm-composition-p
    ;;                                 PHASE-FSM-COMPOSITION-P-IMPLIES-VALUES-KEYS)
    ;;                                (phase-fsm-validp-of-svtv-data-obj))
    ;;         :use ((:INSTANCE PHASE-FSM-VALIDP-OF-SVTV-DATA-OBJ))))
    :hints(("Goal" :in-theory (e/d ()
                                   (phase-fsm-validp-of-svtv-data-obj))
            :use phase-fsm-validp-of-svtv-data-obj)))

  ;; (defrefinement svex-alist-keys-equiv svex-alist-eval-equiv


  (local (defthmd svex-env-extract-nonoverride-when-ovsimilar
           (implies (and (svex-envs-ovsimilar env1 env2)
                         (svarlist-override-p vars nil))
                    (equal (svex-env-extract vars env1)
                           (svex-env-extract vars env2)))
           :hints(("Goal" :in-theory (enable svex-env-extract
                                             svarlist-override-p)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:use ((:instance svex-envs-ovsimilar-necc
                                (v (car vars))
                                (x env1) (y env2)))
                         :in-theory (e/d (svar-override-p-when-other)
                                         (svex-envs-ovsimilar-necc)))))))
  
  (local (defthmd svex-alist-eval-when-no-override-vars-and-envs-ovsimilar
           (implies (and (svarlist-override-p (svex-alist-vars x) nil)
                         (svex-envs-ovsimilar env1 env2))
                    (equal (equal (svex-alist-eval x env1)
                                  (svex-alist-eval x env2))
                           t))
           :hints (("Goal" :use ((:instance svex-alist-eval-of-reduce-var-supserset
                                  (vars (svex-alist-vars x))
                                  (env env1))
                                 (:instance svex-alist-eval-of-reduce-var-supserset
                                  (vars (svex-alist-vars x))
                                  (env env2))
                                 (:instance svex-env-extract-nonoverride-when-ovsimilar
                                  (vars (svex-alist-vars x))))
                    :in-theory (e/d (SVEXLIST-VARS-OF-SVEX-ALIST-VALS)
                                    (svex-alist-eval-of-reduce-var-supserset
                                     svex-alist-eval-of-extract-var-supserset))))))

  (local (defthmd similar-when-equal
           (implies (equal x y)
                    (svex-envs-similar x y))))
  
  (local (Defthm svex-alist-ovcongruent-when-vars-nonoverride-p
           (implies (svarlist-override-p (svex-alist-vars x) nil)
                    (svex-alist-ovcongruent x))
           :hints(("Goal" :in-theory (enable similar-when-equal
                                             svex-alist-ovcongruent
                                             svex-alist-eval-when-no-override-vars-and-envs-ovsimilar)))))

  (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))

  (local (defthm 4vec-bit?!-lemma
           (implies (equal (4vec-bit?! x y 0) (4vec-bit?! x z 0))
                    (equal (equal (4vec-bit?! x y a) (4vec-bit?! x z a))
                           t))
           :hints (("goal" :in-theory (enable 4vec-bit?! 4vec-bitmux))
                   (bitops::logbitp-reasoning)
                   (and stable-under-simplificationp
                        '(:in-theory (enable b-ite))))))
                        
  
  (local (defthm eval-bit?!-when-ovsimilar
           (implies (svex-envs-ovsimilar x y)
                    (b* ((test (svar-change-override v :test))
                         (val (svar-change-override v :val))
                         (non (svar-change-override v nil)))
                      (equal (equal (4vec-bit?! (svex-env-lookup test x)
                                                (svex-env-lookup val x)
                                                (svex-env-lookup non x))
                                    (4vec-bit?! (svex-env-lookup test y)
                                                (svex-env-lookup val y)
                                                (svex-env-lookup non y)))
                             t)))
           :hints (("Goal" :use ((:instance svex-envs-ovsimilar-necc (v (svar-change-override v :test)))
                                 (:instance svex-envs-ovsimilar-necc (v (svar-change-override v :val)))
                                 (:instance svex-envs-ovsimilar-necc (v (svar-change-override v nil))))))))
           
  
  (local (defthm eval-svarlist-to-override-alist-when-ovsimilar
           (implies (svex-envs-ovsimilar env1 env2)
                    (b* ((a (svarlist-to-override-alist x)))
                      (equal (svex-envs-similar
                              (svex-alist-eval a env1)
                              (svex-alist-eval a env2))
                             t)))
           :hints(("Goal" :in-theory (enable svex-envs-similar
                                             svex-apply
                                             svex-lookup-of-svarlist-to-override-alist)
                   :expand ((:free (v env) (svex-eval (svex-var v) env)))
                   ))))
  
  (local (defthm svex-alist-ovcongruent-of-svarlist-to-override-alist
           (svex-alist-ovcongruent (svarlist-to-override-alist x))
           :hints(("Goal" :in-theory (enable svex-alist-ovcongruent)))))

  (local (defthm svarlist-nonoverride-p-when-override-p-nil
           (implies (svarlist-override-p x nil)
                    (and (svarlist-nonoverride-p x :test)
                         (svarlist-nonoverride-p x :val)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svarlist-nonoverride-p
                                             svar-override-p-when-other)))))

  (local (defthm svex-envs-equivalent-of-append
           (implies (And (svex-envs-equivalent x1 x2)
                         (svex-envs-equivalent y1 y2))
                    (equal (svex-envs-equivalent (append x1 y1) (append x2 y2)) t))
           :hints(("goal" :do-not-induct t)
                  (and stable-under-simplificationp
                       `(:expand (,(car (last clause))))))))
  
  (local (defthm svex-alist-ovcongruent-of-append
           (implies (and (svex-alist-ovcongruent x)
                         (svex-alist-ovcongruent y))
                    (svex-alist-ovcongruent (append x y)))
           :hints(("goal" :do-not-induct t
                   :in-theory (enable svex-alist-ovcongruent-necc))
                  (and stable-under-simplificationp
                       `(:expand (,(car (last clause))))))))

  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))
  
  (local (defthm base-fsm-ovcongruent-when-phase-fsm-composition-p
           (b* (((flatnorm-res flat)))
             (implies (and (phase-fsm-composition-p x flat config)
                           (svarlist-override-p (svex-alist-vars flat.assigns) nil)
                           (svarlist-override-p (svex-alist-keys flat.assigns) nil)
                           (svarlist-override-p (svex-alist-vars flat.delays) nil)
                           (svarlist-override-p (svex-alist-keys flat.delays) nil))
                      (base-fsm-ovcongruent x)))
           :hints(("Goal" :in-theory (e/d (base-fsm-ovcongruent
                                             phase-fsm-composition-p
                                             svtv-flatnorm-apply-overrides))))))

  
  
  
  (defthm base-fsm-ovcongruent-of-svtv-data-obj->phase-fsm
    (b* (((svtv-data-obj x)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp)
               (base-fsm-ovcongruent x.phase-fsm)))
    :hints(("Goal" :in-theory (e/d (;; base-fsm-ovcongruent
                                    ;; phase-fsm-composition-p
                                    PHASE-FSM-COMPOSITION-P-IMPLIES-VALUES-KEYS)
                                   (phase-fsm-validp-of-svtv-data-obj))
            :use ((:INSTANCE PHASE-FSM-VALIDP-OF-SVTV-DATA-OBJ)))))

  ;; (local (defthm base-fsm-overridekey-transparent-p-of-svtv-data-obj->phase-fsm
  ;;          (b* (((svtv-data-obj x))
  ;;               ((flatnorm-res x.flatnorm))
  ;;               (override-mux-keys (svtv-assigns-override-vars x.flatnorm.assigns
  ;;                                                              (phase-fsm-config->override-config x.phase-fsm-setup))))
  ;;            (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
  ;;                          x.flatten-validp
  ;;                          x.flatnorm-validp
  ;;                          x.phase-fsm-validp
  ;;                          (flatnorm-setup->monotonify x.flatnorm-setup))
  ;;                     (base-fsm-partial-monotonic (svarlist-change-override override-mux-keys :test) x.phase-fsm)))
  ;;          :hints(("Goal" :in-theory (enable base-fsm-partial-monotonic)))))
                
                     
   

  (defthm override-transparency-of-svtv-data-obj->spec-with-smart-check
    (b* (((svtv-spec spec) (svtv-data-obj->spec x))
         ((svtv-data-obj x))
         ;; ((flatnorm-res x.flatnorm))
         (spec-run (svtv-spec-run spec spec-env :base-ins base-ins :initst spec-initst))
         (impl-run (svtv-spec-run spec pipe-env))
         ;; (override-mux-keys (svtv-assigns-override-vars x.flatnorm.assigns
         ;;                                                (phase-fsm-config->override-config x.phase-fsm-setup)))
         ;; ((base-fsm spec.fsm))
         ;; (overridetriples (svar->svex-override-triplelist
         ;;                   (svarlist-to-override-triples overridekeys)
         ;;                   spec.fsm.values))
         )
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup)

                    (svtv-spec-override-syntax-checks spec overridekeys triplemaps)
                    (base-fsm-override-smart-check spec.fsm overridekeys)

                    ;; (not (svexlist-check-overridetriples (svex-alist-vals spec.fsm.values) overridetriples))
                    ;; (not (svexlist-check-overridetriples (svex-alist-vals spec.fsm.nextstate) overridetriples))
                    
                    (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run)
                    (svex-env-<<= (svex-env-reduce (append (svex-alist-vars spec.initst-alist)
                                                           (svex-alistlist-vars spec.in-alists))
                                                   pipe-env)
                                  spec-env)

                    (svarlist-nonoverride-p (svex-envlist-all-keys base-ins) :test))
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :in-theory (e/d (svtv-data-obj->spec
                                    base-fsm-overridekey-transparent-p
                                    )
                                   (design->ideal-fsm-overridekey-transparent
                                    base-fsm-overridekey-transparent-p-when-base-fsm-override-smart-check))
            :use ((:instance base-fsm-overridekey-transparent-p-when-base-fsm-override-smart-check
                   (keys overridekeys)
                   (x (svtv-data-obj->phase-fsm x))))
            ;; :use ((:instance design->ideal-fsm-overridekey-transparent
            ;;        (x (svtv-data-obj->design x))
            ;;        (config (svtv-data-obj->phase-fsm-setup x))))
            )))

  (defthm svtv-spec-stimulus-equiv-of-svtv-data-obj->ideal-spec
    (B* (((svtv-data-obj x)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup))
               (svtv-spec-stimulus-equiv (svtv-data-obj->ideal-spec x)
                                         (svtv-data-obj->spec x))))
    :hints(("Goal" :in-theory (e/d (svtv-spec-stimulus-equiv
                                    svtv-data-obj->spec
                                    svtv-data-obj->ideal-spec
                                    phase-fsm-composition-p
                                    ;; svex-alist-eval-equiv!
                                    )
                                   (phase-fsm-validp-of-svtv-data-obj))
            :use phase-fsm-validp-of-svtv-data-obj)))

  (local (defthm svex-alist-width-of-flatnorm-res
           (B* (((svtv-data-obj x))
                ((flatnorm-res x.flatnorm)))
             (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                           x.flatten-validp
                           x.flatnorm-validp)
                      (svex-alist-width x.flatnorm.assigns)))
           :hints(("Goal" :in-theory (enable flatnorm-of-svtv-data-obj))
                  (and stable-under-simplificationp
                       '(:in-theory (enable svtv-normalize-assigns
                                            svex-normalize-assigns))))))

  ;; (local (defthm member-of-svarlist-change-override
  ;;          (implies (svar-override-p key nil)
  ;;                   (not (member-equal key (svarlist-change-override other :test))))
  ;;          :hints(("Goal" :in-theory (enable svarlist-override-p svarlist-change-override)))))
   
  (local (defthm intersectp-equal-when-svarlist-override-p
           (implies (svarlist-override-p keys nil)
                    (not (intersectp-equal keys (svarlist-change-override other :test))))
           :hints(("Goal" :in-theory (enable intersectp-equal svarlist-override-p
                                             member-of-svarlist-change-override)))))

  ;; (local (defthm svex-alist-<<=-of-compose-svarlist-to-override-alist
  ;;          (implies (and (svarlist-override-p (svex-alist-keys x1) nil)
  ;;                        (svarlist-override-p (svex-alist-keys x2) nil)
  ;;                        (svex-alist-<<= x1 x2))
  ;;                   (svex-alist-<<= (svex-alist-compose (svarlist-to-override-alist overridekeys) x1)
  ;;                                   (svex-alist-compose (svarlist-to-override-alist overridekeys) x2)))
  ;;          :hints(("Goal" :in-theory (enable svex-alist-<<=)))))

  (local (defthm svar-override-p-when-member-special
           (implies (and (member-equal (svar-fix key) (svarlist-fix vars))
                         (svarlist-override-p vars nil)
                         (not (svar-overridetype-equiv type nil)))
                    (not (svar-override-p key type)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svar-override-p-when-other)))))

  (local (defthm svex-env-ov<<=-when-agree-except
           (implies (and (svex-env-<<= x y)
                         (svex-envs-agree-except vars x y)
                         (svarlist-override-p vars nil))
                    (svex-env-ov<<= x y))
           :hints (("goal" :expand ((:with svex-env-ov<<=-by-witness (svex-env-ov<<= x y))))
                   (and stable-under-simplificationp
                        (let ((call (acl2::find-call-lst 'svex-env-ov<<=-witness clause)))
                          (and call
                               `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . key)))))))
                   (and stable-under-simplificationp
                        '(:use ((:instance svex-envs-agree-except-implies
                                 (var key))))))))

  (defthm svex-alist-monotonic-on-vars-when-ovmonotonic
    (implies (and (svex-alist-ovmonotonic x)
                  (svarlist-override-p vars nil))
             (svex-alist-monotonic-on-vars vars x))
    :hints (("goal" :expand (svex-alist-monotonic-on-vars vars x)
             :in-theory (enable svex-alist-ovmonotonic-necc))
            (and stable-under-simplificationp
                 (let ((call (acl2::find-call-lst 'svex-alist-ovmonotonic-witness clause)))
                   (and call
                        `(:clause-processor (acl2::generalize-with-alist-cp clause '(((mv-nth '0 ,call) . env1)
                                                                                     ((mv-nth '1 ,call) . env2))))))))) 
  ;; (local (defthm svex-alist-monotonic-on-vars-of-flatnorm-res
  ;;          (B* (((svtv-data-obj x))
  ;;               ((flatnorm-res x.flatnorm)))
  ;;            (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
  ;;                          x.flatten-validp
  ;;                          x.flatnorm-validp
  ;;                          (flatnorm-setup->monotonify x.flatnorm-setup)
  ;;                          (svarlist-override-p keys nil))
  ;;                     (svex-alist-monotonic-on-vars keys (flatnorm-res->assigns
  ;;                                                         (flatnorm-add-overrides
  ;;                                                          x.flatnorm overridekeys)))))
  ;;          :hints(("Goal" :use ((:instance svex-alist-partial-monotonic-of-flatnorm-add-overrides
  ;;                                (x (svtv-data-obj->flatnorm x))))
  ;;                  :in-theory (disable svex-alist-partial-monotonic-of-flatnorm-add-overrides)))))

  ;; (local (defthm svex-alist-monotonic-on-vars-of-flatnorm-add-overrides-design->flatnorm
  ;;          (B* (((svtv-data-obj x))
  ;;               ;; ((flatnorm-res x.flatnorm))
  ;;               )
  ;;            (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
  ;;                          x.flatten-validp
  ;;                          x.flatnorm-validp
  ;;                          (flatnorm-setup->monotonify x.flatnorm-setup)
  ;;                          (svarlist-override-p keys nil))
  ;;                     (svex-alist-monotonic-on-vars keys (flatnorm-res->assigns
  ;;                                                         (flatnorm-add-overrides
  ;;                                                          (design->flatnorm x.design) overridekeys)))))
  ;;          :hints(("Goal" :use ((:instance svex-alist-partial-monotonic-of-flatnorm-add-overrides
  ;;                                (x (design->flatnorm (svtv-data-obj->design x)))))
  ;;                  :in-theory (disable svex-alist-partial-monotonic-of-flatnorm-add-overrides)))))

     
  ;; (local (defthm svex-alist-width-of-c
  ;;          (B* (((svtv-data-obj x)))
  ;;            (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
  ;;                          x.flatten-validp
  ;;                          x.flatnorm-validp)
  ;;                     (svarlist-addr-p (svex-alist-vars (flatnorm-res->assigns x.flatnorm)))))
  ;;          :hints(("Goal" :in-theory (enable flatnorm-of-svtv-data-obj)))))
        


  (local (defthm no-duplicate-keys-of-flatnorm-res->assigns
           (B* (((svtv-data-obj x)))
             (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                           x.flatten-validp
                           x.flatnorm-validp)
                      (no-duplicatesp-equal (svex-alist-keys (flatnorm-res->assigns x.flatnorm)))))
           :hints(("Goal" :in-theory (enable flatnorm-of-svtv-data-obj)))))

  (local (defcong set-equiv svex-alist-compose-equiv (svarlist-to-override-alist vars) 1
           :hints(("Goal" :in-theory (enable svex-alist-compose-equiv
                                             svex-compose-lookup
                                             svex-lookup-of-svarlist-to-override-alist)))))

  (local (defcong set-equiv svex-alist-eval-equiv (svarlist-to-override-alist vars) 1
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                             svex-lookup-of-svarlist-to-override-alist)))))

  (local (defthm netevalcomp-p-base-fsm->values-of-svtv-data-obj
           (B* (((svtv-data-obj x))
                ((flatnorm-res flat) (Design->flatnorm x.design)))
             (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                           x.flatten-validp
                           x.flatnorm-validp
                           x.phase-fsm-validp
                           (flatnorm-setup->monotonify x.flatnorm-setup))
                      (netevalcomp-p (base-fsm->values x.phase-fsm)
                                     (flatnorm-res->assigns
                                      (flatnorm-add-overrides
                                       flat
                                       (svtv-assigns-override-vars
                                        flat.assigns (phase-fsm-config->override-config x.phase-fsm-setup)))))))
           :hints(("Goal" :in-theory (enable flatnorm-add-overrides
                                             phase-fsm-composition-p
                                             svtv-flatnorm-apply-overrides)
                   :use phase-fsm-validp-of-svtv-data-obj))))
           
  (local (defthmd svex-alist-compose-flatnorm-add-overrides
           (svex-alist-eval-equiv
            (svex-alist-compose
             (flatnorm-res->delays (flatnorm-add-overrides flat overridekeys))
             values)
            (svex-alist-compose
             (flatnorm-res->delays flat)
             (append (svex-alist-compose (svarlist-to-override-alist overridekeys) values)
                     values)))
           :hints(("Goal" :in-theory (enable flatnorm-add-overrides
                                             svex-alist-eval-equiv-in-terms-of-envs-equivalent)))))

  (local (defthm svex-alist-compose-<<=-of-append
           (implies (and (double-rewrite (set-equiv (svex-alist-keys x) (svex-alist-keys y)))
                         (svex-alist-<<= x y)
                         (svex-alist-compose-<<= x2 y2))
                    (svex-alist-compose-<<= (append x x2) (append y y2)))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))
  


  
  (local (defthm base-fsm-<<=-ideal-of-svtv-data-obj->phase-fsm
           (B* (((svtv-data-obj x)))
             (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                           x.flatten-validp
                           x.flatnorm-validp
                           x.phase-fsm-validp
                           (flatnorm-setup->monotonify x.flatnorm-setup))
                      (base-fsm-<<= x.phase-fsm (design->ideal-fsm x.design x.phase-fsm-setup))))
           :hints(("Goal" :in-theory (e/d (base-fsm-<<=
                                           design->ideal-fsm
                                           flatnorm->ideal-fsm
                                           phase-fsm-composition-p
                                           svtv-flatnorm-apply-overrides
                                           ;; flatnorm-add-overrides
                                           ;; flatnorm-of-svtv-data-obj
                                           svex-alist-compose-flatnorm-add-overrides)
                                          (phase-fsm-validp-of-svtv-data-obj))
                   :use phase-fsm-validp-of-svtv-data-obj))))

  (local (defthm svex-alist-keys-of-base-fsm->nextstate
           (B* (((svtv-data-obj x)))
             (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                           x.flatten-validp
                           x.flatnorm-validp
                           x.phase-fsm-validp)
                      (equal (svex-alist-keys (base-fsm->nextstate x.phase-fsm))
                             (Svex-alist-keys (flatnorm-res->delays x.flatnorm)))))
           :hints(("Goal" :in-theory (e/d (base-fsm-<<=
                                           design->ideal-fsm
                                           flatnorm->ideal-fsm
                                           phase-fsm-composition-p
                                           svtv-flatnorm-apply-overrides
                                           ;; flatnorm-add-overrides
                                           ;; flatnorm-of-svtv-data-obj
                                           svex-alist-compose-flatnorm-add-overrides)
                                          (phase-fsm-validp-of-svtv-data-obj))
                   :use phase-fsm-validp-of-svtv-data-obj))))

  
  
  (local
   (defthm override-transparency-of-svtv-data-obj->spec/ideal-spec-abstraction-lemma
     (b* (((svtv-spec spec) (svtv-data-obj->ideal-spec x))
          ((svtv-spec abs)  (svtv-data-obj->spec x))
          ((svtv-data-obj x))
          ((flatnorm-res x.flatnorm))
          (spec-run (svtv-spec-run spec spec-env :base-ins base-ins :initst spec-initst))
          (impl-run (svtv-spec-run abs pipe-env))
          (overridekeys (svtv-assigns-override-vars x.flatnorm.assigns
                                                    (phase-fsm-config->override-config x.phase-fsm-setup))))
       (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                     x.flatten-validp
                     x.flatnorm-validp
                     x.phase-fsm-validp
                     (flatnorm-setup->monotonify x.flatnorm-setup)

                     (svtv-spec-override-syntax-checks spec overridekeys triplemaps)

                    
                     (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run)
                     (svex-env-<<= (svex-env-reduce (append (svex-alist-vars spec.initst-alist)
                                                           (svex-alistlist-vars spec.in-alists))
                                                   pipe-env)
                                  spec-env)

                     (svarlist-nonoverride-p (svex-envlist-all-keys base-ins) :test))
                (svex-env-<<= impl-run spec-run)))
     :hints(("Goal" :in-theory (e/d (svtv-data-obj->ideal-spec
                                     svtv-data-obj->spec
                                     svtv-spec-stimulus-equiv
                                     )
                                    (design->ideal-fsm-overridekey-transparent))
             :use ((:instance design->ideal-fsm-overridekey-transparent
                    (x (svtv-data-obj->design x))
                    (config (svtv-data-obj->phase-fsm-setup x))))))))

  ;; The only difference here is that the syntax check and input/initst
  ;; variable computations are done wrt the computed svtv-spec rather than the
  ;; ideal-spec, which is then something that can be relieved by execution.
   (defthm override-transparency-of-svtv-data-obj->spec/ideal-spec-abstraction
     (b* (((svtv-spec spec) (svtv-data-obj->ideal-spec x))
          ((svtv-spec abs)  (svtv-data-obj->spec x))
          ((svtv-data-obj x))
          ((flatnorm-res x.flatnorm))
          (spec-run (svtv-spec-run spec spec-env :base-ins base-ins :initst spec-initst))
          (impl-run (svtv-spec-run abs pipe-env))
          (overridekeys (svtv-assigns-override-vars x.flatnorm.assigns
                                                    (phase-fsm-config->override-config x.phase-fsm-setup))))
       (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                     x.flatten-validp
                     x.flatnorm-validp
                     x.phase-fsm-validp
                     (flatnorm-setup->monotonify x.flatnorm-setup)

                     (svtv-spec-override-syntax-checks abs overridekeys triplemaps)

                    
                     (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run)
                     (svex-env-<<= (svex-env-reduce (append (svex-alist-vars abs.initst-alist)
                                                            (svex-alistlist-vars abs.in-alists))
                                                   pipe-env)
                                  spec-env)

                     (svarlist-nonoverride-p (svex-envlist-all-keys base-ins) :test))
                (svex-env-<<= impl-run spec-run)))
     :hints(("Goal" :use override-transparency-of-svtv-data-obj->spec/ideal-spec-abstraction-lemma)
            (and stable-under-simplificationp
                 '(:in-theory (enable svtv-data-obj->spec
                                      svtv-data-obj->ideal-spec))))))
