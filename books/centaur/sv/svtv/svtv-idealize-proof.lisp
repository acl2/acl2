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

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

(include-book "svtv-idealize-defs")
(include-book "cycle-probe")
(include-book "override-envlist-defs")
(local (include-book "svtv-spec-override-mux"))
(local (include-book "../svex/alist-thms"))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "../svex/compose-theory-deps"))

(local (in-theory (disable mod floor ceiling)))

(local (std::add-default-post-define-hook :fix))

(defsection base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation
  (local (defthm subsetp-of-set-difference
           (implies (subsetp-equal a c)
                    (subsetp-equal (set-difference-equal a b) c))))

  ;; (local (in-theory (disable SVAR-OVERRIDE-TRIPLELIST-ENVLISTS-MUXES-<<=-IN-TERMS-OF-RENAMED-KEYS
  ;;                            SVEX-ENVLISTS-OVERRIDE-VAR-MUXES-<<=-IMPLIES-SVAR-OVERRIDE-TRIPLELIST-ENVLISTS-MUXES-<<=-OF-SVARLIST-TO-OVERRIDE-TRIPLES)))

  (local (defthm svar-override-p-nil-when-member-svarlist-override-okp
           (implies (and (member-equal (svar-fix var) (svarlist-fix keys))
                         (svarlist-override-okp keys))
                    (equal (svar-override-p var nil)
                           (not (or (svar-override-p var :test)
                                    (svar-override-p var :val)))))
           :hints(("Goal" :in-theory (enable svarlist-override-okp
                                             svar-override-okp
                                             svarlist-fix
                                             svar-override-p-when-other)))))

  (local
   (defthmd svex-alist-not-depends-on-compose-free
     (implies (and (svex-alist-eval-equiv! y (svex-alist-compose x a))
                   (case-split (or (not (svex-alist-depends-on v x))
                                   (svex-lookup v a)))
                   (not (svex-alist-depends-on v a)))
              (not (svex-alist-depends-on v y)))))

  (local (defthm svex-alist-vars-of-svarlist-to-override-alist
           (implies (svarlist-override-p x nil)
                    (set-equiv (svex-alist-vars (svarlist-to-override-alist x))
                               (append (svarlist-fix x)
                                       (svarlist-change-override x :test)
                                       (svarlist-change-override x :val))))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             svarlist-to-override-alist-in-terms-of-svarlist-to-override-triples
                                             svarlist-to-override-triples
                                             svar-override-triplelist->override-alist
                                             svex-alist-vars
                                             svarlist-fix
                                             svarlist-override-p)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable acl2::set-unequal-witness-rw))))))

  (local (defthmd svex-alist-not-depends-on-of-netevalcomp-split
           (implies (and (netevalcomp-p comp network)
                         (subsetp-equal (svex-alist-keys comp) (svex-alist-keys network))
                         (case-split
                           (not (member-equal (svar-fix v) (set-difference-equal (svex-alist-vars network)
                                                                                 (svex-alist-keys network))))))
                    (not (svex-alist-depends-on v comp)))
           :hints(("Goal" :in-theory (enable svex-alist-not-depends-on-of-netevalcomp)))))

  (local (defthmd vars-of-svex-alist-compose-strong-split
           (implies (and (case-split (not (member-equal v (set-difference-equal (svex-alist-vars x) (svex-alist-keys y)))))
                         (not (member-equal v (svex-alist-vars y))))
                    (not (member-equal v (svex-alist-vars (svex-alist-compose x y)))))
           :hints(("Goal" :in-theory (enable vars-of-svex-alist-compose-strong)))))


  (defthm vars-of-svtv-assigns-override-vars
    (implies (not (member-equal v (svex-alist-keys assigns)))
             (not (member-equal v (svtv-assigns-override-vars assigns config))))
    :hints(("Goal" :in-theory (enable svtv-assigns-override-vars))))

  (defthm svex-alist-depends-on-of-append
    (implies (and (not (svex-alist-depends-on v x))
                  (not (svex-alist-depends-on v y)))
             (not (svex-alist-depends-on v (append x y))))
    :hints (("goal" :expand ((svex-alist-depends-on v (append x y))))))

  (local (defthm svex-alist-depends-on-of-svex-alist-compose-strong-split
         (implies (and (case-split (or (not (svex-alist-depends-on v x))
                                       (svex-lookup v a)))
                       (not (svex-alist-depends-on v a)))
                  (not (svex-alist-depends-on v (svex-alist-compose x a))))
         :hints (("goal" :expand ((svex-alist-depends-on v (svex-alist-compose x a))))
                 '(:cases ((svex-lookup v a))))))

  (local (defthm svex-alist-not-depends-on-of-phase-fsm-compositionp
           (b* (((flatnorm-res flatnorm))
                ((phase-fsm-config config))
                (override-vars (svtv-assigns-override-vars flatnorm.assigns config.override-config)))
             (implies (and (phase-fsm-composition-p phase-fsm flatnorm config)
                           (svarlist-override-p (svex-alist-keys flatnorm.assigns) nil)
                           (not (member-equal (svar-fix v)
                                              (set-difference-equal (svex-alist-vars flatnorm.assigns)
                                                                    (svex-alist-keys flatnorm.assigns))))
                           (not (member-equal (svar-fix v)
                                              (svarlist-change-override override-vars :test)))
                           (not (member-equal (svar-fix v)
                                              (svarlist-change-override override-vars :val))))
                      (and (not (svex-alist-depends-on v (base-fsm->values phase-fsm)))
                           (implies (not (member-equal (svar-fix v)
                                                       (set-difference-equal (svex-alist-vars flatnorm.delays)
                                                                             (svex-alist-keys flatnorm.assigns))))
                                    (not (svex-alist-depends-on v (base-fsm->nextstate phase-fsm)))))))
           :hints(("Goal" :in-theory (enable phase-fsm-composition-p
                                             vars-of-svex-alist-compose-strong-split
                                             svex-alist-not-depends-on-of-netevalcomp-split
                                             svex-alist-not-depends-on-compose-free
                                             ;; svex-alist-not-depends-on-neteval-ordering-compile-x-subst-free
                                             svtv-flatnorm-apply-overrides)))))

  (local (defthm svex-alist-not-depends-on-of-obj-phase-fsm
           (b* (((svtv-data-obj data))
                ((flatnorm-res flatnorm) data.flatnorm)
                ((phase-fsm-config config) data.phase-fsm-setup)
                (override-vars (svtv-assigns-override-vars flatnorm.assigns config.override-config)))
             (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic data))
                           data.flatten-validp
                           data.flatnorm-validp
                           data.phase-fsm-validp
                           ;; (modalist-addr-p (design->modealist data.design))
                           (not (member-equal (svar-fix v)
                                              (set-difference-equal (svex-alist-vars flatnorm.assigns)
                                                                    (svex-alist-keys flatnorm.assigns))))
                           (not (member-equal (svar-fix v)
                                              (svarlist-change-override override-vars :test)))
                           (not (member-equal (svar-fix v)
                                              (svarlist-change-override override-vars :val))))
                      (and (not (svex-alist-depends-on v (base-fsm->values data.phase-fsm)))
                           (implies (not (member-equal (svar-fix v)
                                                       (set-difference-equal (svex-alist-vars flatnorm.delays)
                                                                             (svex-alist-keys flatnorm.assigns))))
                                    (not (svex-alist-depends-on v (base-fsm->nextstate data.phase-fsm)))))))
           :hints (("goal" :use ((:instance phase-fsm-validp-of-svtv-data-obj (x data)))
                    :in-theory (disable phase-fsm-validp-of-svtv-data-obj)))))

  (defthm svex-env-<<=-of-removekeys-when-svex-env-<<=-filter-override
    (implies (and (svex-env-<<= (svex-env-filter-override override-inputs nil) ref-inputs)
                  (svarlist-override-okp keys)
                  (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
                  (svarlist-override-p (svar-override-triplelist->valvars triples) :val)
                  (subsetp-equal (svarlist-filter-override keys :test) (svar-override-triplelist->testvars triples))
                  (subsetp-equal (svarlist-filter-override keys :val) (svar-override-triplelist->valvars triples)))
             (svex-env-<<= (svex-env-removekeys
                            (svar-override-triplelist-override-vars triples)
                            (svex-env-extract keys override-inputs))
                           ref-inputs))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (car (last clause)))
                      (w `(svex-env-<<=-witness . ,(cdr lit))))
                   `(:expand (,lit)
                     :use ((:instance svex-env-<<=-necc
                            (x (svex-env-filter-override override-inputs nil))
                            (y ref-inputs)
                            (var ,w)))
                     :in-theory (e/d ()
                                     (svex-env-<<=-necc)))))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svar-override-triplelist-override-vars-under-set-equiv)
                                   (svex-env-<<=-necc)))))
    :otf-flg t)


  (local (defun ind (override-inputs ref-inputs)
           (if (atom override-inputs)
               ref-inputs
             (ind (cdr override-inputs) (cdr ref-inputs)))))

  (defthm svex-envlist-<<=-of-removekeys-when-svex-envlist-<<=-filter-override
    (implies (and (svex-envlist-<<= (svex-envlist-filter-override override-inputs nil) ref-inputs)
                  (svarlist-override-okp keys)
                  (svarlist-override-p (svar-override-triplelist->testvars triples) :test)
                  (svarlist-override-p (svar-override-triplelist->valvars triples) :val)
                  (subsetp-equal (svarlist-filter-override keys :test) (svar-override-triplelist->testvars triples))
                  (subsetp-equal (svarlist-filter-override keys :val) (svar-override-triplelist->valvars triples)))
             (svex-envlist-<<= (svex-envlist-removekeys
                                (svar-override-triplelist-override-vars triples)
                                (svex-envlist-extract-keys keys override-inputs))
                               ref-inputs))
    :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                      svex-envlist-removekeys
                                      svex-envlist-extract-keys
                                      svex-envlist-filter-override)
            :induct (ind override-inputs ref-inputs))))

  (local (defthm svarlist-override-okp-when-svarlist-override-p-nil
           (implies (svarlist-override-p x nil)
                    (svarlist-override-okp x))
           :hints(("Goal" :in-theory (enable svarlist-override-p)))))

  (local (defthm set-difference-of-append
           (Equal (set-difference-equal (append a b) c)
                  (append (set-difference-equal a c) (set-difference-equal b c)))))


  (local (defthm member-when-not-svar-override-okp
           (implies (and (not (svar-override-okp v))
                         (svarlist-override-okp x))
                    (not (member-equal v x)))
           :hints(("Goal" :in-theory (enable svarlist-override-okp)))))


  (local (defretd svarlist-override-okp-by-badguy-split
           (implies (and (acl2::rewriting-positive-literal `(svarlist-override-okp ,x))
                         (case-split
                          (or (not (member-equal badguy (svarlist-fix x)))
                              (svar-override-okp badguy))))
                    (svarlist-override-okp x))
           :hints(("Goal" :in-theory (enable svarlist-override-okp-iff-badguy)))
           :fn svarlist-override-okp-badguy))

  (defthm svarlist-override-okp-dependencies-of-phase-fsm-composition
    (b* (((flatnorm-res flatnorm))
         ((phase-fsm-config config))
         ;; (override-vars (svtv-assigns-override-vars flatnorm.assigns config.override-config))
         )
      (implies (and (phase-fsm-composition-p phase-fsm flatnorm config)
                    (svarlist-override-p (svex-alist-keys flatnorm.assigns) nil)
                    (svarlist-override-okp (svex-alist-vars flatnorm.assigns)))
               (and (svarlist-override-okp (svex-alist-dependencies (base-fsm->values phase-fsm)))
                    (implies (svarlist-override-okp (svex-alist-vars flatnorm.delays))
                             (svarlist-override-okp (svex-alist-dependencies (base-fsm->nextstate phase-fsm)))))))
    :hints(("Goal" :in-theory (enable svarlist-override-okp-by-badguy-split))))

  (defthm svarlist-non-override-p-svex-alist-vars-of-obj-flatnorm
    (b* (((svtv-data-obj data))
         ((flatnorm-res flatnorm) data.flatnorm))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic data))
                    data.flatten-validp
                    data.flatnorm-validp)
               (and (svarlist-override-p (svex-alist-vars flatnorm.assigns) nil)
                    (svarlist-override-p (svex-alist-vars flatnorm.delays) nil))))
    :hints(("Goal" :in-theory (e/d (svarlist-override-okp-iff-badguy)
                                   (flatnorm-of-svtv-data-obj))
            :use ((:instance flatnorm-of-svtv-data-obj (x data))))))




  (defthm svarlist-override-okp-dependencies-of-obj-phase-fsm
    (b* (((svtv-data-obj data))
         ((flatnorm-res flatnorm) data.flatnorm)
         ((phase-fsm-config config) data.phase-fsm-setup))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic data))
                    data.flatten-validp
                    data.flatnorm-validp
                    data.phase-fsm-validp)
               (and (svarlist-override-okp (svex-alist-dependencies (base-fsm->values data.phase-fsm)))
                    (svarlist-override-okp (svex-alist-dependencies (base-fsm->nextstate data.phase-fsm))))))
    :hints (("goal" :use ((:instance phase-fsm-validp-of-svtv-data-obj (x data)))
             :in-theory (disable phase-fsm-validp-of-svtv-data-obj))))


  (defthm svarlist-filter-override-of-append
    (equal (svarlist-filter-override (append a b) type)
           (append (svarlist-filter-override a type)
                   (svarlist-filter-override b type)))
    :hints(("Goal" :in-theory (enable svarlist-filter-override))))


  (local (defthmd subsetp-witness-backchain-1
           (implies (let ((a (acl2::subsetp-witness x y)))
                      (or (member a y) (not (member a x))))
                    (subsetp x y))
           :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))

  (local (defthmd subsetp-witness-backchain-2
           (implies (let ((a (acl2::subsetp-witness x y)))
                      (or (not (member a x)) (member a y)))
                    (subsetp x y))
           :hints(("Goal" :in-theory (enable acl2::subsetp-witness-rw)))))


  (local (defthm member-when-svar-override-p
           (implies (and (svar-override-p v type)
                         (svar-p v)
                         (not (svar-overridetype-equiv type nil))
                         (svarlist-override-p x nil))
                    (not (member-equal v x)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svar-override-p-when-other)))))

  (local (defthm member-of-svarlist-change-override
           (implies (and (svar-override-p v type2)
                         (not (svar-overridetype-equiv type type2)))
                    (not (member-equal v (svarlist-change-override x type))))
           :hints(("Goal" :in-theory (enable svarlist-change-override)))))


  (local (in-theory (disable (:CONGRUENCE
                              SET-EQUIV-IMPLIES-SVEX-ENVLISTS-SIMILAR-SVEX-ENVLIST-REMOVEKEYS-1)
                             (:REWRITE
                              SVAR-OVERRIDE-TRIPLELIST-ENVLISTS-MUXES-<<=-IN-TERMS-OF-RENAMED-KEYS))))

  (defthm base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation
    (b* (((svtv-data-obj data))
         (ideal-fsm (design->ideal-fsm data.design data.phase-fsm-setup))
         (spec-values (base-fsm-eval ref-inputs ref-initst ideal-fsm))
         (impl-values (base-fsm-eval override-inputs override-initst data.phase-fsm)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic data))
                    data.flatten-validp
                    data.flatnorm-validp
                    data.phase-fsm-validp
                    (flatnorm-setup->monotonify data.flatnorm-setup)

                    (equal (len override-inputs) (len ref-inputs))
                    (svex-envlists-override-var-muxes-<<= override-inputs ref-inputs spec-values)
                    (svex-envlist-<<= (svex-envlist-filter-override override-inputs nil) ref-inputs)
                    (svex-envlists-override-test-vars-subsetp ref-inputs override-inputs)

                    (svex-env-<<= override-initst ref-initst))
               (svex-envlist-<<= impl-values spec-values)))
    :hints (("Goal" :do-not-induct t
             :use ((:instance base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-when-triples-ok
                    (override-inputs
                     (b* (((svtv-data-obj data))
                          ((flatnorm-res fl) data.flatnorm)
                          (triples
                           (svarlist-to-override-triples
                            (svtv-assigns-override-vars fl.assigns
                                                        (phase-fsm-config->override-config data.phase-fsm-setup)))))
                       (svex-envlist-extract-keys
                        (append (svex-alist-dependencies (base-fsm->values data.phase-fsm))
                                (svex-alist-dependencies (base-fsm->nextstate data.phase-fsm))
                                (svar-override-triplelist->testvars triples)
                                (svar-override-triplelist->valvars triples))
                        override-inputs)))))
             :in-theory (e/d (svar-override-triplelist-override-vars-under-set-equiv
                              testvars-of-svarlist-to-override-triples
                              valvars-of-svarlist-to-override-triples)
                             (base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-when-triples-ok)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svar-override-triplelist-override-vars-under-set-equiv
                                    testvars-of-svarlist-to-override-triples
                                    valvars-of-svarlist-to-override-triples
                                    subsetp-witness-backchain-1)
                                   (base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-when-triples-ok)))))
    :otf-flg t)
  
  (defthm base-fsm-final-state-of-design->ideal-fsm-refines-overridden-approximation
    (b* (((svtv-data-obj data))
         ((base-fsm ideal-fsm) (design->ideal-fsm data.design data.phase-fsm-setup))
         (spec-values (base-fsm-eval ref-inputs ref-initst ideal-fsm))
         (spec-finalstate (base-fsm-final-state ref-inputs ref-initst ideal-fsm.nextstate))
         (impl-finalstate (base-fsm-final-state override-inputs override-initst (base-fsm->nextstate data.phase-fsm))))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic data))
                    data.flatten-validp
                    data.flatnorm-validp
                    data.phase-fsm-validp
                    (flatnorm-setup->monotonify data.flatnorm-setup)

                    (equal (len override-inputs) (len ref-inputs))
                    (svex-envlists-override-var-muxes-<<= override-inputs ref-inputs spec-values)
                    (svex-envlist-<<= (svex-envlist-filter-override override-inputs nil) ref-inputs)
                    (svex-envlists-override-test-vars-subsetp ref-inputs override-inputs)

                    (svex-env-<<= override-initst ref-initst))
               (svex-env-<<= impl-finalstate spec-finalstate)))
    :hints (("Goal" :do-not-induct t
             :use ((:instance base-fsm-final-state-of-design->ideal-fsm-refines-overridden-approximation-when-triples-ok
                    (override-inputs
                     (b* (((svtv-data-obj data))
                          ((flatnorm-res fl) data.flatnorm)
                          (triples
                           (svarlist-to-override-triples
                            (svtv-assigns-override-vars fl.assigns
                                                        (phase-fsm-config->override-config data.phase-fsm-setup)))))
                       (svex-envlist-extract-keys
                        (append (svex-alist-dependencies (base-fsm->values data.phase-fsm))
                                (svex-alist-dependencies (base-fsm->nextstate data.phase-fsm))
                                (svar-override-triplelist->testvars triples)
                                (svar-override-triplelist->valvars triples))
                        override-inputs)))))
             :in-theory (e/d (svar-override-triplelist-override-vars-under-set-equiv
                              testvars-of-svarlist-to-override-triples
                              valvars-of-svarlist-to-override-triples)
                             (base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-when-triples-ok)))
            (and stable-under-simplificationp
                 '(:in-theory (e/d (svar-override-triplelist-override-vars-under-set-equiv
                                    testvars-of-svarlist-to-override-triples
                                    valvars-of-svarlist-to-override-triples
                                    subsetp-witness-backchain-1)
                                   (base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-when-triples-ok)))))
    :otf-flg t))


(local
 (encapsulate nil
   ;; The original version of this theorem isn't quite general enough for
   ;; us. Generalizing by making it explicit that the ref-inputs only have to be
   ;; greater than the override inputs on variables that are used in the FSM.
   
   ;; To instantiate that theorem and prove this one, we need to instantiate with ref-inputs-inst satisfying
   ;; (svex-envlist-<<= (svex-envlist-removekeys override-vars override-inputs) ref-inputs-inst)
   ;; for which the FSM will evaluate to the same as with just ref-inputs.
   ;; but we only have
   ;; (svex-envlist-<<= (svex-envlist-reduce input-vars override-inputs) ref-inputs)
   ;; They only need to agree on input-vars.

   (local (defun compose-ref-input-envs (override-inputs ref-inputs input-vars)
            (if (atom override-inputs)
                (svex-envlist-fix ref-inputs)
              (cons (append (svex-env-extract input-vars (car ref-inputs)) (svex-env-fix (car override-inputs)))
                    (compose-ref-input-envs (cdr override-inputs) (cdr ref-inputs) input-vars)))))

   (local (defthm svex-env-reduce-vars-lemma
            (implies (subsetp-equal (svarlist-fix vars1) (svarlist-fix vars2))
                     (equal (svex-env-extract vars1 (append env1 (svex-env-extract vars2 env2) env3))
                            (svex-env-extract vars1 (append env1 env2))))
            :hints(("Goal" :in-theory (enable svex-env-extract)
                    :induct (len vars1)))))
   

   (local (defthm svex-alist-eval-append-reduce
            (implies (subsetp-equal (svex-alist-vars x) (svarlist-fix input-vars))
                     (equal (svex-alist-eval x (append env1 (svex-env-extract input-vars env2) env3))
                            (svex-alist-eval x (append env1 env2))))
            :hints(("Goal" :in-theory (enable svex-alist-eval-equal-when-extract-vars-similar)))))
                          
   
   (local (defthm base-fsm-eval-of-compose-ref-input-envs
            (b* (((base-fsm fsm)))
              (implies (and (subsetp-equal (svex-alist-vars fsm.values) (svarlist-fix input-vars))
                            (subsetp-equal (svex-alist-vars fsm.nextstate) (svarlist-fix input-vars))
                            (<= (len override-inputs) (len ref-inputs)))
                       (equal (base-fsm-eval (compose-ref-input-envs override-inputs ref-inputs input-vars)
                                             initst fsm)
                              (base-fsm-eval ref-inputs initst fsm))))
            :hints(("Goal" :in-theory (enable base-fsm-eval
                                              base-fsm-step
                                              base-fsm-step-outs
                                              base-fsm-step-env)))))


   (local (defthm len-of-compose-ref-input-envs
            (equal (len (compose-ref-input-envs override-inputs ref-inputs input-vars))
                   (max (len override-inputs) (len ref-inputs)))))

   (local (defthm svex-envlist-<<=-removekeys-compose-ref-input-envs-lemma
            (implies (svex-env-<<= (svex-env-reduce (set-difference-equal (svarlist-fix input-vars)
                                                                          (svarlist-fix override-vars))
                                                    override-input) ref-input)
                     (svex-env-<<= (svex-env-removekeys override-vars override-input)
                                   (append (svex-env-extract input-vars ref-input)
                                           override-input)))
            :hints ((and stable-under-simplificationp
                         (b* ((lit (car (last clause)))
                              (witness `(svex-env-<<=-witness . ,(cdr lit))))
                           `(:expand (,lit)
                             :use ((:instance svex-env-<<=-necc
                                    (var ,witness)
                                    (x (svex-env-reduce (set-difference-equal (svarlist-fix input-vars)
                                                                               (svarlist-fix override-vars))
                                                         override-input))
                                    (y ref-input)))
                             :in-theory (disable svex-env-<<=-necc)))))))
                                    
   

   (local (defthm svex-envlist-<<=-removekeys-compose-ref-input-envs
            (implies (svex-envlist-<<= (svex-envlist-reduce (set-difference-equal (svarlist-fix input-vars)
                                                                                  (svarlist-fix override-vars))
                                                            override-inputs)
                                       ref-inputs)
                     (svex-envlist-<<= (svex-envlist-removekeys override-vars override-inputs)
                                       (compose-ref-input-envs override-inputs ref-inputs input-vars)))
            :hints(("Goal" :in-theory (enable svex-envlist-removekeys
                                              svex-envlist-<<=
                                              svex-envlist-reduce
                                              compose-ref-input-envs)))))

   (local (defthm set-diff-of-append
            (equal (set-difference-equal (append a b) b)
                   (set-difference-equal a b))
            :hints(("Goal" :in-theory (enable set-difference-equal)))))
   

   (local (defthm svex-envlist-removekeys-of-repeat-nil
            (equal (svex-envlist-removekeys keys (repeat n nil))
                   (repeat n nil))
            :hints(("Goal" :in-theory (enable svex-envlist-removekeys
                                              repeat)))))

   (local (defthm svex-envlist-<<=-of-repeat-nil
            (svex-envlist-<<= (repeat n nil) y)
            :hints(("Goal" :in-theory (enable repeat svex-envlist-<<=)
                    :induct (nthcdr n y)))))

   (local (defthm svex-envlist-<<=-of-append-repeat-nil
            (equal (svex-envlist-<<= (append x (repeat n nil)) y)
                   (svex-envlist-<<= x y))
            :hints(("Goal" :in-theory (enable svex-envlist-<<=)))))


   (local
    (defthm svex-envlist-<<=-of-base-fsm-eval-append-repeat
      (svex-envlist-<<= (base-fsm-eval ins initst fsm)
                        (base-fsm-eval (append ins (repeat n nil)) initst fsm))
      :hints(("Goal" :in-theory (enable base-fsm-eval
                                        svex-envlist-<<=)))))
   
   

   (local (defthm svar-override-triplelist-muxes-<<=-of-nil
            (svar-override-triplelist-muxes-<<=
             triples nil spec-env spec-out)
            :hints(("Goal" :in-theory (enable svar-override-triplelist-muxes-<<=
                                              svar-override-triple-mux-<<=)))))

   (local (in-theory (disable svar-override-triplelist-envlists-muxes-<<=-in-terms-of-renamed-keys)))


   (local (defun ind (n spec-envs spec-outs)
            (if (zp n)
                (list spec-outs spec-envs)
              (ind (1- n) (cdr spec-envs) (cdr spec-outs)))))
   
   (local (defthm svar-override-triplelist-envlists-muxes-<<=-of-repeat-nil
            (svar-override-triplelist-envlists-muxes-<<=
             triples (repeat n nil) spec-envs spec-outs)
            :hints(("Goal" :in-theory (enable svar-override-triplelist-envlists-muxes-<<= repeat)
                    :induct (ind n spec-envs spec-outs)))))

   (local (defthm svar-override-triplelist-envlists-muxes-<<=-of-append
            (equal (svar-override-triplelist-envlists-muxes-<<=
                    triples (append impl1 impl2) spec-envs spec-outs)
                   (and (svar-override-triplelist-envlists-muxes-<<=
                         triples impl1 spec-envs spec-outs)
                         ;; (take (len impl1) spec-envs)
                        ;; (take (len impl1) spec-outs)
                        (svar-override-triplelist-envlists-muxes-<<=
                         triples impl2 (nthcdr (len impl1) spec-envs) (nthcdr (len impl1) spec-outs))))
            :hints(("Goal" :in-theory (enable svar-override-triplelist-envlists-muxes-<<=)
                    :induct (svar-override-triplelist-envlists-muxes-<<=
                             triples impl1 spec-envs spec-outs)))))

   (local (defun ind2 (impl-envs spec-envs spec-outs)
            (if (atom impl-envs)
                (list spec-envs spec-outs)
              (ind2 (cdr impl-envs) (cdr spec-envs) (cdr spec-outs)))))


   (local (defthm svar-override-triplelist-muxes-<<=-of-append-extract
            (implies (subsetp-equal (svar-override-triplelist-override-vars triples)
                                    (svarlist-fix input-vars))
                     (equal (svar-override-triplelist-muxes-<<= triples impl-env (append (svex-env-extract input-vars spec-env) rspec-env2) spec-outs)
                            (svar-override-triplelist-muxes-<<= triples impl-env spec-env spec-outs)))
            :hints(("Goal" :in-theory (enable svar-override-triplelist-muxes-<<=
                                              svar-override-triplelist-override-vars
                                              svar-override-triple-mux-<<=)))))
   
   (local (defthm svar-override-triplelist-envlists-muxes-<<=-of-compose-ref-input-envs
            (implies (subsetp-equal (svar-override-triplelist-override-vars triples)
                                    (svarlist-fix input-vars))
                     (equal (svar-override-triplelist-envlists-muxes-<<=
                             triples impl-envs
                             (compose-ref-input-envs impl-envs spec-envs input-vars)
                             spec-outs)
                            (svar-override-triplelist-envlists-muxes-<<=
                             triples impl-envs spec-envs spec-outs)))
            :hints(("Goal" :in-theory (enable svar-override-triplelist-envlists-muxes-<<=
                                              compose-ref-input-envs)
                    :induct (ind2 impl-envs spec-envs spec-outs)))))


   (local (defthm svex-env-muxtests-subsetp-of-compose-ref-input-envs
            (implies (subsetp-equal (svarlist-fix testvars)
                                    (svarlist-fix input-vars))
                     (equal (svex-env-muxtests-subsetp
                             testvars (append (svex-env-extract input-vars spec-env) spec-env2) impl-env)
                            (svex-env-muxtests-subsetp testvars spec-env impl-env)))
            :hints(("Goal" :in-theory (enable svex-env-muxtests-subsetp)))))

   
   (local (defthm svex-envlists-muxtests-subsetp-of-compose-ref-input-envs
            (implies (and (subsetp-equal (svarlist-fix testvars)
                                         (svarlist-fix input-vars))
                          (<= (len impl-envs1) (len spec-envs)))
                     (equal (svex-envlists-muxtests-subsetp
                             testvars (compose-ref-input-envs impl-envs1 spec-envs input-vars) impl-envs)
                            (svex-envlists-muxtests-subsetp testvars spec-envs impl-envs)))
            :hints(("Goal" :in-theory (enable svex-envlists-muxtests-subsetp
                                              compose-ref-input-envs)))))
   
   ;; (local (defthm svar-override-triplelist-envlists-ok-of-repeat-nil
   ;;          (svar-override-triplelist-envlists-ok-<<=
   ;;           triples (repeat n nil) refs)
   ;;          :hints(("Goal" :in-theory (enable svar-override-triplelist-envlists-ok-<<= repeat)
   ;;                  :induct (nthcdr n refs)))))
   
   ;; (local (defthm svar-override-triplelist-envlists-ok-of-append-repeat-nil
   ;;          (equal (svar-override-triplelist-envlists-ok-<<=
   ;;                  triples (append override-inputs (repeat n nil)) refs)
   ;;                 (svar-override-triplelist-envlists-ok-<<=
   ;;                  triples override-inputs refs))
   ;;          :hints(("Goal" :in-theory (enable svar-override-triplelist-envlists-ok-<<=)))))
   
   (defthm base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-gen
     (b* (((svtv-data-obj data))
          ((base-fsm ideal-fsm) (design->ideal-fsm data.design data.phase-fsm-setup))
          (triples
           (svarlist-to-override-triples
            (svtv-assigns-override-vars (flatnorm-res->assigns data.flatnorm)
                                        (phase-fsm-config->override-config data.phase-fsm-setup))))
          (override-vars (svar-override-triplelist-override-vars triples))
          (test-vars (svar-override-triplelist->testvars triples))
          (spec-values (base-fsm-eval ref-inputs ref-initst ideal-fsm))
          (impl-values (base-fsm-eval override-inputs override-initst data.phase-fsm)))
       (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic data))
                     data.flatten-validp
                     data.flatnorm-validp
                     data.phase-fsm-validp
                     (flatnorm-setup->monotonify data.flatnorm-setup)

                     (equal (len override-inputs) (len ref-inputs))
                     (svex-envlist-<<= (svex-envlist-reduce (set-difference-equal (svarlist-fix input-vars)
                                                                                  override-vars)
                                                            override-inputs)
                                       ref-inputs)
                     (subsetp-equal (svex-alist-vars ideal-fsm.values)
                                    (svarlist-fix input-vars))
                     (subsetp-equal (svex-alist-vars ideal-fsm.nextstate)
                                    (svarlist-fix input-vars))
                     (svar-override-triplelist-envlists-muxes-<<= triples override-inputs ref-inputs spec-values)
                     (svex-envlists-muxtests-subsetp test-vars ref-inputs override-inputs)
                     (svex-env-<<= override-initst ref-initst))
                (svex-envlist-<<= impl-values spec-values)))
     :hints (("Goal" :do-not-induct t
              :use ((:instance base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-when-triples-ok
                     (ref-inputs (compose-ref-input-envs
                                  override-inputs ref-inputs
                                  (append input-vars
                                          (b* (((svtv-data-obj data))
                                               ((base-fsm ideal-fsm) (design->ideal-fsm data.design data.phase-fsm-setup))
                                               (triples
                                                (svarlist-to-override-triples
                                                 (svtv-assigns-override-vars (flatnorm-res->assigns data.flatnorm)
                                                                             (phase-fsm-config->override-config data.phase-fsm-setup))))
                                               (override-vars (svar-override-triplelist-override-vars triples)))
                                            override-vars))))
                     (override-inputs override-inputs)))
              :in-theory (e/d (svex-envlist-<<=-transitive-2
                               svex-envlist-<<=-transitive-1)
                              (base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-when-triples-ok))))
     :otf-flg t)

   (defthm base-fsm-eval-of-design->ideal-fsm-refines-overridden-ideal-fsm-gen
     (b* (((svtv-data-obj data))
          ((base-fsm ideal-fsm) (design->ideal-fsm data.design data.phase-fsm-setup))
          (triples
           (svarlist-to-override-triples
            (svtv-assigns-override-vars (flatnorm-res->assigns data.flatnorm)
                                        (phase-fsm-config->override-config data.phase-fsm-setup))))
          (override-vars (svar-override-triplelist-override-vars triples))
          (test-vars (svar-override-triplelist->testvars triples))
          (spec-values (base-fsm-eval ref-inputs ref-initst ideal-fsm))
          (impl-values (base-fsm-eval override-inputs override-initst ideal-fsm)))
       (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic data))
                     data.flatten-validp
                     data.flatnorm-validp
                     (flatnorm-setup->monotonify data.flatnorm-setup)

                     (equal (len override-inputs) (len ref-inputs))
                     (svex-envlist-<<= (svex-envlist-reduce (set-difference-equal (svarlist-fix input-vars)
                                                                                  override-vars)
                                                            override-inputs)
                                       ref-inputs)
                     (subsetp-equal (svex-alist-vars ideal-fsm.values)
                                    (svarlist-fix input-vars))
                     (subsetp-equal (svex-alist-vars ideal-fsm.nextstate)
                                    (svarlist-fix input-vars))
                     (svar-override-triplelist-envlists-muxes-<<= triples override-inputs ref-inputs spec-values)
                     (svex-envlists-muxtests-subsetp test-vars ref-inputs override-inputs)
                     (svex-env-<<= override-initst ref-initst))
                (svex-envlist-<<= impl-values spec-values)))
     :hints (("Goal" :do-not-induct t
              :use ((:instance base-fsm-eval-of-design->ideal-fsm-refines-overridden-ideal-fsm-when-triples-ok
                     (ref-inputs (compose-ref-input-envs
                                  override-inputs ref-inputs
                                  (append input-vars
                                          (b* (((svtv-data-obj data))
                                               ((base-fsm ideal-fsm) (design->ideal-fsm data.design data.phase-fsm-setup))
                                               (triples
                                                (svarlist-to-override-triples
                                                 (svtv-assigns-override-vars (flatnorm-res->assigns data.flatnorm)
                                                                             (phase-fsm-config->override-config data.phase-fsm-setup))))
                                               (override-vars (svar-override-triplelist-override-vars triples)))
                                            override-vars))))
                     (override-inputs override-inputs)))
              :in-theory (e/d (svex-envlist-<<=-transitive-2
                               svex-envlist-<<=-transitive-1)
                              (base-fsm-eval-of-design->ideal-fsm-refines-overridden-ideal-fsm-when-triples-ok))))
     :otf-flg t)))



(local
 (defsection svarlist-override-difference-lemma

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

   (local (defrefinement svex-alist-eval-equiv svex-alist-keys-equiv
            :hints(("Goal" :in-theory (enable svex-alist-keys-equiv)))))

   (defthm svarlist-override-difference-lemma
     (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                   (svtv-data-obj->flatten-validp x)
                   (svtv-data-obj->flatnorm-validp x)
                   (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup x)))
              (SVARLIST-OVERRIDE-P
               (SET-DIFFERENCE-EQUAL
                (APPEND (SVEX-ALIST-VARS
                         (BASE-FSM->NEXTSTATE
                          (DESIGN->IDEAL-FSM (SVTV-DATA-OBJ->DESIGN X)
                                             (SVTV-DATA-OBJ->PHASE-FSM-SETUP X))))
                        (SVEX-ALIST-VARS
                         (BASE-FSM->VALUES
                          (DESIGN->IDEAL-FSM (SVTV-DATA-OBJ->DESIGN X)
                                             (SVTV-DATA-OBJ->PHASE-FSM-SETUP X)))))
                (APPEND
                 (SVARLIST-CHANGE-OVERRIDE
                  (SVTV-ASSIGNS-OVERRIDE-VARS
                   (FLATNORM-RES->ASSIGNS (SVTV-DATA-OBJ->FLATNORM X))
                   (PHASE-FSM-CONFIG->OVERRIDE-CONFIG (SVTV-DATA-OBJ->PHASE-FSM-SETUP X)))
                  :VAL)
                 (SVARLIST-CHANGE-OVERRIDE
                  (SVTV-ASSIGNS-OVERRIDE-VARS
                   (FLATNORM-RES->ASSIGNS (SVTV-DATA-OBJ->FLATNORM X))
                   (PHASE-FSM-CONFIG->OVERRIDE-CONFIG (SVTV-DATA-OBJ->PHASE-FSM-SETUP X)))
                  :TEST)))
               NIL))
     :hints(("Goal" :in-theory (enable design-flatten-okp))
            (and stable-under-simplificationp
                 (b* ((lit (car (last clause)))
                      (set (cadr lit)))
                   `(:use ((:instance svarlist-addr-p-by-badguy (x ,set))))))))))



(defsection svtv-data-obj->ideal-spec



  
  (local (in-theory (disable SVAR-OVERRIDE-TRIPLELIST-ENVLISTS-MUXES-<<=-IN-TERMS-OF-RENAMED-KEYS)))
  (local (std::set-define-current-function svtv-data-obj->ideal-spec))
  (local (in-theory (enable svtv-data-obj->ideal-spec)))

  (defthm svex-env-reduce-<<=-same
    (svex-env-<<= (svex-env-reduce keys x) x)
    :hints(("Goal" :in-theory (enable svex-env-<<=))))
  
  (local (defthm svex-envlist-reduce-<<=-lemma
           (svex-envlist-<<= (svex-envlist-reduce keys x) x)
           :hints(("Goal" :in-theory (enable svex-envlist-reduce
                                             svex-envlist-<<=)))))

  (local (defthm svex-envlist-reduce-<<=-rw
           (implies (svex-envlist-<<= x y)
                    (svex-envlist-<<= (svex-envlist-reduce keys x) y))
           :hints(("Goal" :in-theory (enable svex-envlist-<<=-transitive-2
                                             svex-envlist-<<=-transitive-1)))))

  (local (defthm svex-envlist-x-override->>=-rw
           (implies (svex-envlist-<<= x y)
                    (svex-envlist-<<= x (svex-envlist-x-override y z)))
           :hints(("Goal" :in-theory (enable svex-envlist-<<=-transitive-2
                                             svex-envlist-<<=-transitive-1)))))

  (defthm design-flatten-okp-when-flatten-validp
    (b* (((svtv-data-obj x)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp)
               (design-flatten-okp x.design)))
    :hints(("Goal" :in-theory (enable design-flatten-okp))))

  (local (defthm max-when-<=
           (implies (and (<= b a)
                         (rationalp b) (rationalp a))
                    (equal (max a b)
                           a))))

  (local (defthm <<=-4vec-x-override-when-<<=-first-arg
           (implies (4vec-<<= a b)
                    (4vec-<<= a (4vec-x-override b c)))
           :hints(("Goal" :in-theory (enable 4vec-<<=-transitive-1
                                             4vec-<<=-transitive-2)))))

  (local (defthm svex-env-<<=-of-svex-env-x-override
           (implies (svex-env-<<= a b)
                    (svex-env-<<= a (svex-env-x-override b c)))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))
  


  (local
   (defthm svex-envlist-<<=-of-svtv-spec-pipe-env->phase-envs-reduce
     (b* (((svtv-spec spec)))
       (implies (and (svex-env-<<= (svex-env-reduce vars pipe-env1) pipe-env2)
                     (subsetp-equal (svex-alistlist-vars spec.in-alists) (svarlist-fix vars))
                     (subsetp-equal (svex-alistlist-vars spec.override-test-alists) (svarlist-fix vars))
                     (subsetp-equal (svex-alistlist-vars spec.override-val-alists) (svarlist-fix vars))
                     (svex-alistlist-check-monotonic spec.in-alists)
                     (svex-alistlist-check-monotonic spec.override-test-alists)
                     (svex-alistlist-check-monotonic spec.override-val-alists))
                (svex-envlist-<<= (svtv-spec-pipe-env->phase-envs spec pipe-env1)
                                  (svtv-spec-pipe-env->phase-envs spec pipe-env2))))
     :hints(("Goal" :use ((:instance svtv-spec-pipe-env->phase-envs-of-svex-env-reduce
                           (env pipe-env1)))
             :in-theory (e/d () (svtv-spec-pipe-env->phase-envs-of-svex-env-reduce))))))

  (local (in-theory (enable svexlist-vars-of-svex-alist-vals)))
  
  (local (defthm svex-env-<<=-of-svex-alist-eval-when-<<=-on-vars
           (implies (and (svex-env-<<= (svex-env-reduce vars a) b)
                         (subsetp-equal (svex-alist-vars x) (svarlist-fix vars))
                         (svex-alist-monotonic-p x))
                    (svex-env-<<= (svex-alist-eval x a)
                                  (svex-alist-eval x b)))
           :hints (("goal" :use ((:instance svex-alist-monotonic-p-necc
                                  (env1 (svex-env-reduce vars a))
                                  (env2 b)))
                    :in-theory (disable svex-alist-monotonic-p-necc)))))


  (local (defthm svex-env-reduce-of-svex-env-filter-overrides
           (implies (svarlist-override-p vars nil)
                    (equal (svex-env-reduce vars (svex-env-filter-override env nil))
                           (svex-env-reduce vars env)))
           :hints(("Goal" :in-theory (enable svex-env-reduce-redef
                                             svarlist-override-p)
                   :induct (len vars)))))
  
  (local (defthm svex-envlist-reduce-of-svex-envlist-filter-overrides
           (implies (svarlist-override-p vars nil)
                    (equal (svex-envlist-reduce vars (svex-envlist-filter-override envs nil))
                           (svex-envlist-reduce vars envs)))
           :hints(("Goal" :in-theory (enable svex-envlist-reduce
                                             svex-envlist-filter-override)))))
  

  (local (defthm svex-envlist-reduce-non-override-vars-of-svtv-spec-pipe-env->phase-envs
           (implies (and (equal override-tests (svtv-spec->override-test-alists x))
                         (equal override-vals (svtv-spec->override-val-alists x))
                         (syntaxp (not (and (equal override-vals ''nil)
                                            (equal override-tests ''nil))))
                         (svarlist-override-p vars nil)
                         (svarlist-override-p (svtv-cyclephaselist-keys (svtv-spec->cycle-phases x)) nil))
                    (equal (svex-envlist-reduce vars (svtv-spec-pipe-env->phase-envs x env))
                           (svex-envlist-reduce vars
                                                (svtv-spec-pipe-env->phase-envs
                                                 (change-svtv-spec x :override-test-alists nil :override-val-alists nil)
                                                 env))))
           :hints (("goal" :use ((:instance svex-envlist-reduce-of-svex-envlist-filter-overrides
                                  (envs (svtv-spec-pipe-env->phase-envs x env))))
                    :in-theory (disable svex-envlist-reduce-of-svex-envlist-filter-overrides)))))


  (local (defthm svex-env-<<=-of-svex-env-reduce-both
           (equal (svex-env-<<= (svex-env-reduce vars envs1)
                                    (svex-env-reduce vars envs2))
                  (svex-env-<<= (svex-env-reduce vars envs1) envs2))
           :hints(("goal" :cases ((svex-env-<<= (svex-env-reduce vars envs1) envs2)))
                  (and stable-under-simplificationp
                       (b* ((lit (assoc 'svex-env-<<= clause))
                            (witness `(svex-env-<<=-witness . ,(cdr lit)))
                            (other (if (eq (caddr lit) 'envs2) '(svex-env-reduce vars envs2) 'envs2)))
                         `(:expand (,lit)
                           :use ((:instance svex-env-<<=-necc
                                  (var ,witness)
                                  (x (svex-env-reduce vars envs1))
                                  (y ,other)))
                           :in-theory (disable svex-env-<<=-necc)))))
           :otf-flg t))
  

  (local (defun cdr2 (x y)
           (if (atom x)
               y
             (cdr2 (cdr x) (cdr y)))))
  
  (local (defthm svex-envlist-<<=-of-svex-envlist-reduce-both
           (equal (svex-envlist-<<= (svex-envlist-reduce vars envs1)
                                    (svex-envlist-reduce vars envs2))
                  (svex-envlist-<<= (svex-envlist-reduce vars envs1) envs2))
           :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                             svex-envlist-reduce)
                   :induct (cdr2 envs1 envs2)
                   :expand ((svex-envlist-reduce vars envs1)
                            (svex-envlist-reduce vars envs2))))))
  

  (local (defthm svex-envlist-<<=-of-svex-envlist-reduce-try-crazy-thing
           (implies (and (equal envs3 (svex-envlist-reduce vars envs2))
                         (bind-free
                          (case-match envs3
                            (('svex-envlist-reduce & envs4) `((envs4 . ,envs4)))
                            (& `((envs4 . ,envs3))))
                          (envs4))
                         (syntaxp (not (equal envs2 envs4)))
                         (equal (svex-envlist-reduce vars envs4) envs3))
                    (equal (svex-envlist-<<= (svex-envlist-reduce vars envs1) envs2)
                           (svex-envlist-<<= (svex-envlist-reduce vars envs1) envs4)))
           :hints (("goal" :use ((:instance svex-envlist-<<=-of-svex-envlist-reduce-both)
                                 (:instance svex-envlist-<<=-of-svex-envlist-reduce-both
                                  (envs2 envs4)))
                    :in-theory (disable svex-envlist-<<=-of-svex-envlist-reduce-both)))))


  ;; (local (in-theory (enable (:COMPOUND-RECOGNIZER ACL2::NATP-COMPOUND-RECOGNIZER)
  ;;       (:CONGRUENCE BASE-FSM-EVAL-SVEX-ENV-EQUIV-CONGRUENCE-ON-PREV-ST)
  ;;       (:CONGRUENCE BASE-FSM-EVAL-SVEX-ENVLIST-EQUIV-CONGRUENCE-ON-INS)
  ;;       (:CONGRUENCE ACL2::SET-EQUIV-IMPLIES-EQUAL-SET-DIFFERENCE-EQUAL-2)
  ;;       (:CONGRUENCE
  ;;            SVEX-ALIST-KEYS-LIST-SVEX-ALISTLIST-EQUIV-CONGRUENCE-ON-X)
  ;;       (:CONGRUENCE
  ;;        SVEX-ALISTLIST-CHECK-MONOTONIC-SVEX-ALISTLIST-EQUIV-CONGRUENCE-ON-X)
  ;;       (:CONGRUENCE
  ;;            SVEX-ALISTLIST-VARS-SVEX-ALISTLIST-EQUIV-CONGRUENCE-ON-X)
  ;;       (:CONGRUENCE
  ;;         SVTV-CYCLEPHASELIST-KEYS-SVTV-CYCLEPHASELIST-EQUIV-CONGRUENCE-ON-X)
  ;;       (:CONGRUENCE
  ;;        SVTV-CYCLEPHASELIST-UNIQUE-I/O-PHASE-SVTV-CYCLEPHASELIST-EQUIV-CONGRUENCE-ON-PHASES)
  ;;       (:CONGRUENCE
  ;;        SVTV-NAME-LHS-MAP-EXTRACT-LIST-SVTV-NAME-LHS-MAP-EQUIV-CONGRUENCE-ON-X)
  ;;       (:CONGRUENCE
  ;;        SVTV-OVERRIDE-TRIPLEMAPLIST-SYNTAX-CHECK-SVEX-ALISTLIST-EQUIV-CONGRUENCE-ON-TEST-ALISTS)
  ;;       (:CONGRUENCE
  ;;        SVTV-OVERRIDE-TRIPLEMAPLIST-SYNTAX-CHECK-SVEX-ALISTLIST-EQUIV-CONGRUENCE-ON-VAL-ALISTS)
  ;;       (:CONGRUENCE
  ;;        SVTV-OVERRIDE-TRIPLEMAPLIST-SYNTAX-CHECK-SVTV-PROBEALIST-EQUIV-CONGRUENCE-ON-PROBES)
  ;;       (:CONGRUENCE
  ;;         SVTV-PROBEALIST-OUTVARS-SVTV-PROBEALIST-EQUIV-CONGRUENCE-ON-PROBES)
  ;;       (:CONGRUENCE SVTV-SPEC-BASE-FSM-EQUIV-CONGRUENCE-ON-FSM)
  ;;       (:CONGRUENCE SVTV-SPEC-SVEX-ALIST-EQUIV-CONGRUENCE-ON-INITST-ALIST)
  ;;       (:CONGRUENCE SVTV-SPEC-SVEX-ALISTLIST-EQUIV-CONGRUENCE-ON-IN-ALISTS)
  ;;       (:CONGRUENCE
  ;;            SVTV-SPEC-SVTV-CYCLEPHASELIST-EQUIV-CONGRUENCE-ON-CYCLE-PHASES)
  ;;       (:CONGRUENCE SVTV-SPEC-SVTV-NAME-LHS-MAP-EQUIV-CONGRUENCE-ON-NAMEMAP)
  ;;       (:CONGRUENCE SVTV-SPEC-SVTV-PROBEALIST-EQUIV-CONGRUENCE-ON-PROBES)
  ;;       (:DEFINITION MAX)
  ;;       (:DEFINITION NOT)
  ;;       (:DEFINITION SVTV-DATA-OBJ->IDEAL-SPEC)
  ;;       (:DEFINITION SVTV-DATA-OBJ->SPEC)
  ;;       (:DEFINITION SVTV-SPEC-RUN-FN)
  ;;       (:DEFINITION SYNP)
  ;;       (:EXECUTABLE-COUNTERPART BASE-FSM-FIX$INLINE)
  ;;       (:EXECUTABLE-COUNTERPART LEN)
  ;;       (:EXECUTABLE-COUNTERPART NOT)
  ;;       (:EXECUTABLE-COUNTERPART SUBSETP-EQUAL)
  ;;       (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-CHECK-MONOTONIC)
  ;;       (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-FIX$INLINE)
  ;;       (:EXECUTABLE-COUNTERPART SVEX-ALISTLIST-VARS)
  ;;       (:REWRITE BASE-FSM-FIX-WHEN-BASE-FSM-P)
  ;;       (:REWRITE BASE-FSM-P-OF-DESIGN->IDEAL-FSM)
  ;;       (:REWRITE BASE-FSM-P-OF-SVTV-DATA-OBJ->PHASE-FSM)
  ;;       (:REWRITE COMMUTATIVITY-OF-+)
  ;;       (:REWRITE LEN-OF-BASE-FSM-EVAL)
  ;;       (:REWRITE LEN-OF-SVEX-ALIST-KEYS-LIST)
  ;;       (:REWRITE LEN-OF-SVEX-ENVLIST-X-OVERRIDE)
  ;;       (:REWRITE LEN-OF-SVTV-SPEC-PIPE-ENV->PHASE-ENVS)
  ;;       (:REWRITE ACL2::LOWER-BOUND-OF-LEN-WHEN-SUBLISTP)
  ;;       (:REWRITE MAX-WHEN-<=)
  ;;       (:REWRITE ACL2::NFIX-WHEN-NATP)
  ;;       (:REWRITE ACL2::PREFIXP-WHEN-EQUAL-LENGTHS)
  ;;       (:REWRITE RETURN-TYPE-OF-SVEX-ALIST-VARS)
  ;;       (:REWRITE RETURN-TYPE-OF-SVEX-ALISTLIST-VARS)
  ;;       (:REWRITE ACL2::SUBLISTP-WHEN-PREFIXP)
  ;;       (:REWRITE ACL2::SUBSETP-NIL)
  ;;       (:REWRITE ACL2::SUBSETP-OF-APPEND-WHEN-SUBSET-OF-EITHER)
  ;;       (:REWRITE ACL2::SUBSETP-REFL)
  ;;       (:REWRITE
  ;;        SVAR-OVERRIDE-TRIPLELIST-ENVLISTS-MUXES-<<=-OF-SVEX-ENVLIST-X-OVERRIDE)
  ;;       (:REWRITE
  ;;        SVAR-OVERRIDE-TRIPLELIST-OVERRIDE-VARS-OF-TRIPLES-WHEN-SVARLIST-OVERRIDE-P)
  ;;       (:REWRITE SVARLIST-ADDR-P-OF-SVTV-ASSIGNS-OVERRIDE-VARS)
  ;;       (:REWRITE SVARLIST-FIX-OF-APPEND)
  ;;       (:REWRITE SVARLIST-FIX-WHEN-SVARLIST-P)
  ;;       (:REWRITE SVARLIST-OVERRIDE-DIFFERENCE-LEMMA)
  ;;       (:REWRITE SVARLIST-OVERRIDE-P-OF-OVERRIDE-TEST-VARS)
  ;;       (:REWRITE SVARLIST-OVERRIDE-P-WHEN-SVARLIST-ADDR-P)
  ;;       (:REWRITE SVEX-ALIST-FIX-UNDER-SVEX-ALIST-EQUIV)
  ;;       (:REWRITE SVEX-ALIST-FIX-WHEN-SVEX-ALIST-P)
  ;;       (:REWRITE SVEX-ALIST-MONOTONIC-P-WHEN-SVEX-ALIST-CHECK-MONOTONIC)
  ;;       (:REWRITE SVEX-ALIST-P-OF-PIPELINE-SETUP->INITST)
  ;;       (:REWRITE SVEX-ALISTLIST-FIX-UNDER-SVEX-ALISTLIST-EQUIV)
  ;;       (:REWRITE SVEX-ALISTLIST-FIX-WHEN-SVEX-ALISTLIST-P)
  ;;       (:REWRITE SVEX-ALISTLIST-P-OF-PIPELINE-SETUP->OVERRIDE-TESTS)
  ;;       (:REWRITE SVEX-ALISTLIST-P-OF-PIPELINE-SETUP->OVERRIDE-VALS)
  ;;       (:REWRITE SVEX-ENV-<<=-OF-SVEX-ALIST-EVAL-WHEN-<<=-ON-VARS)
  ;;       (:REWRITE SVEX-ENV-<<=-OF-SVEX-ENV-X-OVERRIDE)
  ;;       (:REWRITE SVEX-ENV-<<=-OF-SVTV-SPEC-PHASE-OUTS->PIPE-OUT)
  ;;       (:REWRITE SVEX-ENV-FIX-UNDER-SVEX-ENV-EQUIV)
  ;;       (:REWRITE SVEX-ENV-X-OVERRIDE-WHEN-B-NIL)
  ;;       (:REWRITE SVEX-ENVLIST-<<=-OF-SVEX-ENVLIST-REDUCE-TRY-CRAZY-THING)
  ;;       (:REWRITE SVEX-ENVLIST-<<=-OF-SVTV-SPEC-PIPE-ENV->PHASE-ENVS-REDUCE)
  ;;       (:REWRITE SVEX-ENVLIST-<<=-SELF)
  ;;       (:REWRITE SVEX-ENVLIST-FIX-UNDER-SVEX-ENVLIST-EQUIV)
  ;;       (:REWRITE SVEX-ENVLIST-REDUCE-<<=-RW)
  ;;       (:REWRITE
  ;;        SVEX-ENVLIST-REDUCE-NON-OVERRIDE-VARS-OF-SVTV-SPEC-PIPE-ENV->PHASE-ENVS)
  ;;       (:REWRITE SVEX-ENVLIST-X-OVERRIDE->>=-RW)
  ;;       (:REWRITE SVEX-ENVLIST-X-OVERRIDE-WHEN-B-EMPTY)
  ;;       (:REWRITE SVEX-ENVLISTS-MUXTESTS-SUBSETP-OF-SVEX-ENVLIST-X-OVERRIDE)
  ;;       (:REWRITE SVTV-CYCLEPHASELIST-FIX-UNDER-SVTV-CYCLEPHASELIST-EQUIV)
  ;;       (:REWRITE SVTV-CYCLEPHASELIST-FIX-WHEN-SVTV-CYCLEPHASELIST-P)
  ;;       (:REWRITE SVTV-CYCLEPHASELIST-P-OF-SVTV-DATA-OBJ->CYCLE-PHASES)
  ;;       (:REWRITE
  ;;          SVTV-DATA-OBJ-OK-IMPLIES-SVARLIST-ADDR-P-OF-FLATNORM-ASSIGNS-KEYS)
  ;;       (:REWRITE SVTV-NAME-LHS-MAP-FIX-UNDER-SVTV-NAME-LHS-MAP-EQUIV)
  ;;       (:REWRITE
  ;;        SVTV-OVERRIDE-TRIPLEMAPLIST-MUXES-<<=-OF-SPEC-OUTS-IMPLIES-SVAR-OVERRIDE-KEYS-CHECK-SEPARATE-OVERRIDE-ENVLISTS-OF-SPEC-INS)
  ;;       (:REWRITE SVTV-OVERRIDE-TRIPLEMAPLIST-MUXES-<<=-WHEN-<<=)
  ;;       (:REWRITE
  ;;        SVTV-OVERRIDE-TRIPLEMAPLIST-MUXTESTS-SUBSETP-OF-SPEC-OUTS-IMPLIES-SVEX-ENVLISTS-MUXTESTS-SUBSETP-TESTVARS)
  ;;       (:REWRITE SVTV-PROBEALIST-FIX-UNDER-SVTV-PROBEALIST-EQUIV)
  ;;       (:REWRITE SVTV-PROBEALIST-FIX-WHEN-SVTV-PROBEALIST-P)
  ;;       (:REWRITE SVTV-PROBEALIST-P-OF-PIPELINE-SETUP->PROBES)
  ;;       (:REWRITE SVTV-SPEC->CYCLE-PHASES-OF-SVTV-SPEC)
  ;;       (:REWRITE SVTV-SPEC->FSM-OF-SVTV-SPEC)
  ;;       (:REWRITE SVTV-SPEC->IN-ALISTS-OF-SVTV-SPEC)
  ;;       (:REWRITE SVTV-SPEC->INITST-ALIST-OF-SVTV-SPEC)
  ;;       (:REWRITE SVTV-SPEC->NAMEMAP-OF-SVTV-SPEC)
  ;;       (:REWRITE SVTV-SPEC->OVERRIDE-TEST-ALISTS-OF-SVTV-SPEC)
  ;;       (:REWRITE SVTV-SPEC->OVERRIDE-VAL-ALISTS-OF-SVTV-SPEC)
  ;;       (:REWRITE SVTV-SPEC->PROBES-OF-SVTV-SPEC)
  ;;       (:REWRITE SVTV-SPEC-PHASE-OUTS->PIPE-OUT-OF-SVTV-SPEC)
  ;;       (:REWRITE SVTV-SPEC-PIPE-ENV->PHASE-ENVS-OF-SVTV-SPEC)
  ;;       (:REWRITE ACL2::TAKE-OF-TOO-MANY)
  ;;       (:REWRITE-QUOTED-CONSTANT BASE-FSM-FIX-UNDER-BASE-FSM-EQUIV)
  ;;       (:TYPE-PRESCRIPTION FLATNORM-SETUP->MONOTONIFY$INLINE)
  ;;       (:TYPE-PRESCRIPTION LEN)
  ;;       (:TYPE-PRESCRIPTION LIST-EQUIV)
  ;;       (:TYPE-PRESCRIPTION NO-DUPLICATESP-EACH)
  ;;       (:TYPE-PRESCRIPTION SVARLIST-OVERRIDE-P)
  ;;       (:TYPE-PRESCRIPTION SVEX-ALIST-CHECK-MONOTONIC)
  ;;       (:TYPE-PRESCRIPTION SVEX-ALISTLIST-CHECK-MONOTONIC)
  ;;       (:TYPE-PRESCRIPTION SVEX-ENV-<<=)
  ;;       (:TYPE-PRESCRIPTION SVEX-ENVLIST-<<=)
  ;;       (:TYPE-PRESCRIPTION SVTV-CYCLEPHASELIST-UNIQUE-I/O-PHASE)
  ;;       (:TYPE-PRESCRIPTION SVTV-DATA$AP)
  ;;       (:TYPE-PRESCRIPTION SVTV-DATA-OBJ->FLATNORM-VALIDP$INLINE)
  ;;       (:TYPE-PRESCRIPTION SVTV-DATA-OBJ->FLATTEN-VALIDP$INLINE)
  ;;       (:TYPE-PRESCRIPTION SVTV-OVERRIDE-TRIPLEMAPLIST-MUXES-<<=)
  ;;       (:TYPE-PRESCRIPTION SVTV-OVERRIDE-TRIPLEMAPLIST-MUXTESTS-SUBSETP)
  ;;       (:TYPE-PRESCRIPTION SVTV-OVERRIDE-TRIPLEMAPLIST-SYNTAX-CHECK))))
                           
  (local
   (defret <fn>-run-refines-svtv-spec-run-with-len-spec-base-ins-bound
    (b* (((svtv-spec impl) (svtv-data-obj->spec x))
         ((svtv-spec spec))
         ((svtv-data-obj x))
         ((pipeline-setup x.pipeline-setup))
         (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
         (impl-run (svtv-spec-run impl pipe-env)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp
                    x.cycle-fsm-validp
                    x.pipeline-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup)
                    

                    (svtv-override-triplemaplist-muxes-<<= triplemaps pipe-env spec-pipe-env spec-run)
                    (svtv-override-triplemaplist-muxtests-subsetp triplemaps spec-pipe-env pipe-env)
                    (svtv-override-triplemaplist-syntax-check
                     x.pipeline-setup.override-tests x.pipeline-setup.override-vals
                     x.pipeline-setup.probes triplemaps)
                    
                    (svarlist-override-p (svtv-cyclephaselist-keys x.cycle-phases) nil)
                    (svtv-cyclephaselist-unique-i/o-phase x.cycle-phases)
                    (equal (svex-alist-keys-list x.pipeline-setup.override-tests)
                           (svex-alist-keys-list x.pipeline-setup.override-vals))
                    (no-duplicatesp-each (svex-alist-keys-list x.pipeline-setup.override-tests))
                    (svarlist-override-p
                     (svtv-name-lhs-map-list-all-keys
                      (svtv-name-lhs-map-inverse-list
                       (svtv-name-lhs-map-extract-list
                        (take (len (svtv-probealist-outvars x.pipeline-setup.probes))
                              (svex-alist-keys-list x.pipeline-setup.override-tests))
                        x.namemap)))
                     nil)
                    (<= (len x.pipeline-setup.override-tests)
                        (len (svtv-probealist-outvars x.pipeline-setup.probes)))
                    (<= (len spec-base-ins)
                        (* (len x.cycle-phases)
                           (len (svtv-probealist-outvars x.pipeline-setup.probes))))
                    
                    (svex-env-<<= (svex-env-reduce
                                   (append (svex-alist-vars x.pipeline-setup.initst)
                                           (svex-alistlist-vars x.pipeline-setup.inputs))
                                   pipe-env)
                                  spec-pipe-env)
                    (svarlist-override-p (svex-envlist-all-keys spec-base-ins) nil)
                    
                    (svex-alistlist-check-monotonic x.pipeline-setup.inputs)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-vals)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-tests)
                    (svex-alist-check-monotonic x.pipeline-setup.initst)
                    )
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :in-theory (e/d (svtv-spec-run
                                    svtv-data-obj->spec
                                    svar-override-triplelist-override-vars-of-triples-when-svarlist-override-p)
                                   (base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-when-triples-ok
                                    base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-gen))
            :restrict ((svtv-override-triplemaplist-muxes-<<=-of-spec-outs-implies-svar-override-keys-check-separate-override-envlists-of-spec-ins
                        ((triplemaps triplemaps)))
                       (svtv-override-triplemaplist-muxtests-subsetp-of-spec-outs-implies-svex-envlists-muxtests-subsetp
                        ((triplemaps triplemaps))))
            :use ((:instance base-fsm-eval-of-design->ideal-fsm-refines-overridden-approximation-gen
                   (data x)
                   (ref-inputs (b* (((svtv-data-obj x))
                                    ((pipeline-setup x.pipeline-setup)))
                                 (svex-envlist-x-override
                                  (svtv-spec-pipe-env->phase-envs
                                   (make-svtv-spec :fsm (design->ideal-fsm x.design x.phase-fsm-setup)
                                                   :cycle-phases x.cycle-phases
                                                   :namemap x.namemap
                                                   :probes x.pipeline-setup.probes
                                                   :in-alists x.pipeline-setup.inputs
                                                   :override-test-alists x.pipeline-setup.override-tests
                                                   :override-val-alists x.pipeline-setup.override-vals
                                                   :initst-alist x.pipeline-setup.initst)
                                   spec-pipe-env)
                                  spec-base-ins)))
                   (input-vars (b* (((svtv-data-obj x))
                                    ((base-fsm fsm) (design->ideal-fsm x.design x.phase-fsm-setup)))
                                 (append (svex-alist-vars fsm.nextstate)
                                         (svex-alist-vars fsm.values))))
                   (ref-initst (svex-env-x-override
                                (b* (((svtv-data-obj x))
                                     ((pipeline-setup x.pipeline-setup)))
                                  (svex-alist-eval x.pipeline-setup.initst spec-pipe-env))
                                spec-initst))
                   (override-inputs (svtv-spec-pipe-env->phase-envs
                                     (svtv-data-obj->spec x)
                                     pipe-env))
                   (override-initst (b* (((svtv-data-obj x))
                                         ((pipeline-setup x.pipeline-setup)))
                                      (svex-alist-eval x.pipeline-setup.initst pipe-env)))))))))


  
  (local (defthm svarlist-override-p-of-envlist-all-keys-of-take
           (implies (svarlist-override-p (svex-envlist-all-keys x) type)
                    (svarlist-override-p (svex-envlist-all-keys (take n x)) type))
           :hints(("Goal" :in-theory (e/d (svex-envlist-all-keys)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))
                   :expand ((svarlist-override-p nil type))))))


  
  
    
  (defret <fn>-run-refines-svtv-spec-run
    (b* (((svtv-spec impl) (svtv-data-obj->spec x))
         ((svtv-spec spec))
         ((svtv-data-obj x))
         ((pipeline-setup x.pipeline-setup))
         (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
         (impl-run (svtv-spec-run impl pipe-env)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp
                    x.cycle-fsm-validp
                    x.pipeline-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup)
                    

                    (svtv-override-triplemaplist-muxes-<<= triplemaps pipe-env spec-pipe-env spec-run)
                    (svtv-override-triplemaplist-muxtests-subsetp triplemaps spec-pipe-env pipe-env)
                    
                    (svtv-override-triplemaplist-syntax-check
                     x.pipeline-setup.override-tests x.pipeline-setup.override-vals
                     x.pipeline-setup.probes triplemaps)
                    
                    (svarlist-override-p (svtv-cyclephaselist-keys x.cycle-phases) nil)
                    (svtv-cyclephaselist-unique-i/o-phase x.cycle-phases)
                    (equal (svex-alist-keys-list x.pipeline-setup.override-tests)
                           (svex-alist-keys-list x.pipeline-setup.override-vals))
                    (no-duplicatesp-each (svex-alist-keys-list x.pipeline-setup.override-tests))
                    (svarlist-override-p
                     (svtv-name-lhs-map-list-all-keys
                      (svtv-name-lhs-map-inverse-list
                       (svtv-name-lhs-map-extract-list
                        (take (len (svtv-probealist-outvars x.pipeline-setup.probes))
                              (svex-alist-keys-list x.pipeline-setup.override-tests))
                        x.namemap)))
                     nil)
                    (<= (len x.pipeline-setup.override-tests)
                        (len (svtv-probealist-outvars x.pipeline-setup.probes)))


                    (svex-env-<<= (svex-env-reduce
                                   (append (svex-alist-vars x.pipeline-setup.initst)
                                           (svex-alistlist-vars x.pipeline-setup.inputs))
                                   pipe-env)
                                  spec-pipe-env)
                    (svarlist-override-p (svex-envlist-all-keys spec-base-ins) nil)
                    
                    (svex-alistlist-check-monotonic x.pipeline-setup.inputs)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-vals)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-tests)
                    (svex-alist-check-monotonic x.pipeline-setup.initst)
                    )
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :use ((:instance <fn>-run-refines-svtv-spec-run-with-len-spec-base-ins-bound
                          (spec-base-ins (b* (((svtv-data-obj x))
                                              ((pipeline-setup x.pipeline-setup)))
                                           (take (* (len x.cycle-phases)
                                                    (len (svtv-probealist-outvars x.pipeline-setup.probes)))
                                                 spec-base-ins)))))
            :in-theory (disable <fn>-run-refines-svtv-spec-run-with-len-spec-base-ins-bound))))


  (local
   (defret <fn>-run-refines-svtv-ideal-spec-run-with-len-spec-base-ins-bound
     (b* (((svtv-spec spec))
          ((svtv-data-obj x))
          ((pipeline-setup x.pipeline-setup))
          (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
          (impl-run (svtv-spec-run spec pipe-env)))
       ;; Note: this isn't fully general given we don't allow base-ins/initst in the impl-run,
       ;; but the conditions for this to be OK are more complicated that we want to deal with.
       ;; E.g., we need
       ;; (svex-env-<<= (svex-env-x-override impl-pipe-initst-result impl-initst)
       ;;               (svex-env-x-override spec-pipe-initst-result spec-initst))
       ;; and even if we have (svex-env-<<= impl-pipe-initst-result spec-pipe-initst-result)
       ;; as well as (svex-env-<<= impl-initst spec-initst),
       ;; we can't conclude that without more complicated conditions -- namely,
       ;; impl-initst must be <<= (svex-env-x-override spec-pipe-initst-result spec-initst)
       ;; wherever impl-pipe-initst-result is x.
       ;; Similar strangeness holds for inputs.
       ;; :base-ins base-ins :initst initst
       (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                     x.flatten-validp
                     x.flatnorm-validp
                     x.phase-fsm-validp
                     x.cycle-fsm-validp
                     x.pipeline-validp
                     (flatnorm-setup->monotonify x.flatnorm-setup)
                    

                     (svtv-override-triplemaplist-muxes-<<= triplemaps pipe-env spec-pipe-env spec-run)
                     (svtv-override-triplemaplist-muxtests-subsetp triplemaps spec-pipe-env pipe-env)
                     (svtv-override-triplemaplist-syntax-check
                      x.pipeline-setup.override-tests x.pipeline-setup.override-vals
                      x.pipeline-setup.probes triplemaps)
                    
                     (svarlist-override-p (svtv-cyclephaselist-keys x.cycle-phases) nil)
                     (svtv-cyclephaselist-unique-i/o-phase x.cycle-phases)
                     (equal (svex-alist-keys-list x.pipeline-setup.override-tests)
                            (svex-alist-keys-list x.pipeline-setup.override-vals))
                     (no-duplicatesp-each (svex-alist-keys-list x.pipeline-setup.override-tests))
                     (svarlist-override-p
                      (svtv-name-lhs-map-list-all-keys
                       (svtv-name-lhs-map-inverse-list
                        (svtv-name-lhs-map-extract-list
                         (take (len (svtv-probealist-outvars x.pipeline-setup.probes))
                               (svex-alist-keys-list x.pipeline-setup.override-tests))
                         x.namemap)))
                      nil)
                     (<= (len x.pipeline-setup.override-tests)
                         (len (svtv-probealist-outvars x.pipeline-setup.probes)))
                     (<= (len spec-base-ins)
                         (* (len x.cycle-phases)
                            (len (svtv-probealist-outvars x.pipeline-setup.probes))))
                    
                     (svex-env-<<= (svex-env-reduce
                                    (append (svex-alist-vars x.pipeline-setup.initst)
                                            (svex-alistlist-vars x.pipeline-setup.inputs))
                                    pipe-env)
                                   spec-pipe-env)
                     (svarlist-override-p (svex-envlist-all-keys spec-base-ins) nil)
                     ;; (svarlist-override-p (svex-envlist-all-keys base-ins) nil)
                    
                     (svex-alistlist-check-monotonic x.pipeline-setup.inputs)
                     (svex-alistlist-check-monotonic x.pipeline-setup.override-vals)
                     (svex-alistlist-check-monotonic x.pipeline-setup.override-tests)
                    
                     (svex-alist-check-monotonic x.pipeline-setup.initst)
                     ;; (svex-envlist-<<= base-ins spec-base-ins)
                     ;; (svex-env-<<= initst spec-initst)
                     )
                (svex-env-<<= impl-run spec-run)))
     :hints(("Goal" :in-theory (e/d (svtv-spec-run
                                     svtv-data-obj->spec
                                     svar-override-triplelist-override-vars-of-triples-when-svarlist-override-p)
                                    (base-fsm-eval-of-design->ideal-fsm-refines-overridden-ideal-fsm-when-triples-ok
                                     base-fsm-eval-of-design->ideal-fsm-refines-overridden-ideal-fsm-gen))
             :restrict ((svtv-override-triplemaplist-muxes-<<=-of-spec-outs-implies-svar-override-keys-check-separate-override-envlists-of-spec-ins
                         ((triplemaps triplemaps)))
                        (svtv-override-triplemaplist-muxtests-subsetp-of-spec-outs-implies-svex-envlists-muxtests-subsetp
                         ((triplemaps triplemaps))))
             :use ((:instance base-fsm-eval-of-design->ideal-fsm-refines-overridden-ideal-fsm-gen
                    (data x)
                    (ref-inputs (b* (((svtv-data-obj x))
                                     ((pipeline-setup x.pipeline-setup)))
                                  (svex-envlist-x-override
                                   (svtv-spec-pipe-env->phase-envs
                                    (make-svtv-spec :fsm (design->ideal-fsm x.design x.phase-fsm-setup)
                                                    :cycle-phases x.cycle-phases
                                                    :namemap x.namemap
                                                    :probes x.pipeline-setup.probes
                                                    :in-alists x.pipeline-setup.inputs
                                                    :override-test-alists x.pipeline-setup.override-tests
                                                    :override-val-alists x.pipeline-setup.override-vals
                                                    :initst-alist x.pipeline-setup.initst)
                                    spec-pipe-env)
                                   spec-base-ins)))
                    (input-vars (b* (((svtv-data-obj x))
                                     ((base-fsm fsm) (design->ideal-fsm x.design x.phase-fsm-setup)))
                                  (append (svex-alist-vars fsm.nextstate)
                                          (svex-alist-vars fsm.values))))
                    (ref-initst (svex-env-x-override
                                 (b* (((svtv-data-obj x))
                                      ((pipeline-setup x.pipeline-setup)))
                                   (svex-alist-eval x.pipeline-setup.initst spec-pipe-env))
                                 spec-initst))
                    (override-inputs (b* (((svtv-data-obj x))
                                          ((pipeline-setup x.pipeline-setup)))
                                       (svex-envlist-x-override
                                        (svtv-spec-pipe-env->phase-envs
                                         (make-svtv-spec :fsm (design->ideal-fsm x.design x.phase-fsm-setup)
                                                         :cycle-phases x.cycle-phases
                                                         :namemap x.namemap
                                                         :probes x.pipeline-setup.probes
                                                         :in-alists x.pipeline-setup.inputs
                                                         :override-test-alists x.pipeline-setup.override-tests
                                                         :override-val-alists x.pipeline-setup.override-vals
                                                         :initst-alist x.pipeline-setup.initst)
                                         pipe-env)
                                        nil)))
                    (override-initst (svex-env-x-override
                                      (b* (((svtv-data-obj x))
                                           ((pipeline-setup x.pipeline-setup)))
                                        (svex-alist-eval x.pipeline-setup.initst pipe-env))
                                      nil))))
             :do-not-induct t))
     :otf-flg t))


  (defret <fn>-run-refines-svtv-ideal-spec-run
    (b* (((svtv-spec spec))
         ((svtv-data-obj x))
         ((pipeline-setup x.pipeline-setup))
         (spec-run (svtv-spec-run spec spec-pipe-env :base-ins spec-base-ins :initst spec-initst))
         (impl-run (svtv-spec-run spec pipe-env
                                  ;; Note: this isn't fully general given we don't allow base-ins/initst in the impl-run,
                                  ;; but the conditions for this to be OK are more complicated that we want to deal with.
                                  ;; :base-ins base-ins :initst initst
                                  )))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp
                    x.cycle-fsm-validp
                    x.pipeline-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup)
                    

                    (svtv-override-triplemaplist-muxes-<<= triplemaps pipe-env spec-pipe-env spec-run)
                    (svtv-override-triplemaplist-muxtests-subsetp triplemaps spec-pipe-env pipe-env)
                    
                    (svtv-override-triplemaplist-syntax-check
                     x.pipeline-setup.override-tests x.pipeline-setup.override-vals
                     x.pipeline-setup.probes triplemaps)
                    
                    (svarlist-override-p (svtv-cyclephaselist-keys x.cycle-phases) nil)
                    (svtv-cyclephaselist-unique-i/o-phase x.cycle-phases)
                    (equal (svex-alist-keys-list x.pipeline-setup.override-tests)
                           (svex-alist-keys-list x.pipeline-setup.override-vals))
                    (no-duplicatesp-each (svex-alist-keys-list x.pipeline-setup.override-tests))
                    (svarlist-override-p
                     (svtv-name-lhs-map-list-all-keys
                      (svtv-name-lhs-map-inverse-list
                       (svtv-name-lhs-map-extract-list
                        (take (len (svtv-probealist-outvars x.pipeline-setup.probes))
                              (svex-alist-keys-list x.pipeline-setup.override-tests))
                        x.namemap)))
                     nil)
                    (<= (len x.pipeline-setup.override-tests)
                        (len (svtv-probealist-outvars x.pipeline-setup.probes)))


                    (svex-env-<<= (svex-env-reduce
                                   (append (svex-alist-vars x.pipeline-setup.initst)
                                           (svex-alistlist-vars x.pipeline-setup.inputs))
                                   pipe-env)
                                  spec-pipe-env)
                    (svarlist-override-p (svex-envlist-all-keys spec-base-ins) nil)
                    
                    (svex-alistlist-check-monotonic x.pipeline-setup.inputs)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-vals)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-tests)
                    (svex-alist-check-monotonic x.pipeline-setup.initst)
                    )
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :use ((:instance <fn>-run-refines-svtv-ideal-spec-run-with-len-spec-base-ins-bound
                          (spec-base-ins (b* (((svtv-data-obj x))
                                              ((pipeline-setup x.pipeline-setup)))
                                           (take (* (len x.cycle-phases)
                                                    (len (svtv-probealist-outvars x.pipeline-setup.probes)))
                                                 spec-base-ins)))))
            :in-theory (disable <fn>-run-refines-svtv-spec-run-with-len-spec-base-ins-bound)))))


  
