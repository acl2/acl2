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
                                                   (phase-fsm-config->override-config x.phase-fsm-setup)))
         (params (svarlist-change-override overridekeys :test)))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup)

                    (svtv-spec-override-syntax-checks spec overridekeys params triplemaps)

                    
                    (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run)
                    (svex-env-<<= (svex-env-reduce (append (svex-alist-vars spec.initst-alist)
                                                           (svex-alistlist-vars spec.in-alists))
                                                   pipe-env)
                                  spec-env)

                    (svarlist-override-p* (svex-envlist-all-keys base-ins) '(nil :val)))
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :in-theory (e/d (svtv-data-obj->ideal-spec)
                                   (design->ideal-fsm-overridekey-transparent))
            :use ((:instance design->ideal-fsm-overridekey-transparent
                   (x (svtv-data-obj->design x))
                   (config (svtv-data-obj->phase-fsm-setup x)))))))



  (defthm base-fsm-partial-monotonic-of-svtv-data-obj->phase-fsm
    (b* (((svtv-data-obj x))
         ((flatnorm-res x.flatnorm))
         (override-mux-keys (svtv-assigns-override-vars x.flatnorm.assigns
                                                        (phase-fsm-config->override-config x.phase-fsm-setup))))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup))
               (base-fsm-partial-monotonic (svarlist-change-override override-mux-keys :test) x.phase-fsm)))
    :hints(("Goal" :in-theory (enable base-fsm-partial-monotonic))))

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
         ((flatnorm-res x.flatnorm))
         (spec-run (svtv-spec-run spec spec-env :base-ins base-ins :initst spec-initst))
         (impl-run (svtv-spec-run spec pipe-env))
         (override-mux-keys (svtv-assigns-override-vars x.flatnorm.assigns
                                                        (phase-fsm-config->override-config x.phase-fsm-setup)))
         (params (svarlist-change-override override-mux-keys :test))
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

                    (svtv-spec-override-syntax-checks spec overridekeys params triplemaps)
                    (base-fsm-override-smart-check spec.fsm overridekeys)

                    ;; (not (svexlist-check-overridetriples (svex-alist-vals spec.fsm.values) overridetriples))
                    ;; (not (svexlist-check-overridetriples (svex-alist-vals spec.fsm.nextstate) overridetriples))
                    
                    (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run)
                    (svex-env-<<= (svex-env-reduce (append (svex-alist-vars spec.initst-alist)
                                                           (svex-alistlist-vars spec.in-alists))
                                                   pipe-env)
                                  spec-env)

                    (svarlist-override-p* (svex-envlist-all-keys base-ins) '(nil :val)))
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

  
  (local (defthm svex-alist-monotonic-on-vars-of-flatnorm-res
           (B* (((svtv-data-obj x))
                ((flatnorm-res x.flatnorm)))
             (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                           x.flatten-validp
                           x.flatnorm-validp
                           (flatnorm-setup->monotonify x.flatnorm-setup)
                           (svarlist-override-p keys nil))
                      (svex-alist-monotonic-on-vars keys (flatnorm-res->assigns
                                                          (flatnorm-add-overrides
                                                           x.flatnorm overridekeys)))))
           :hints(("Goal" :use ((:instance svex-alist-partial-monotonic-of-flatnorm-add-overrides
                                 (x (svtv-data-obj->flatnorm x))))
                   :in-theory (disable svex-alist-partial-monotonic-of-flatnorm-add-overrides)))))

  (local (defthm svex-alist-monotonic-on-vars-of-flatnorm-add-overrides-design->flatnorm
           (B* (((svtv-data-obj x))
                ;; ((flatnorm-res x.flatnorm))
                )
             (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                           x.flatten-validp
                           x.flatnorm-validp
                           (flatnorm-setup->monotonify x.flatnorm-setup)
                           (svarlist-override-p keys nil))
                      (svex-alist-monotonic-on-vars keys (flatnorm-res->assigns
                                                          (flatnorm-add-overrides
                                                           (design->flatnorm x.design) overridekeys)))))
           :hints(("Goal" :use ((:instance svex-alist-partial-monotonic-of-flatnorm-add-overrides
                                 (x (design->flatnorm (svtv-data-obj->design x)))))
                   :in-theory (disable svex-alist-partial-monotonic-of-flatnorm-add-overrides)))))

  ;; (local (defthm svarlist-addr-p-of-flatnorm-res->assigns-vars
  ;;          (B* (((svtv-data-obj x)))
  ;;            (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
  ;;                          x.flatten-validp
  ;;                          x.flatnorm-validp)
  ;;                     (svarlist-addr-p (svex-alist-vars (flatnorm-res->assigns x.flatnorm)))))
  ;;          :hints(("Goal" :in-theory (enable flatnorm-of-svtv-data-obj)))))

     
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
                                                    (phase-fsm-config->override-config x.phase-fsm-setup)))
          (params (svarlist-change-override overridekeys :test)))
       (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                     x.flatten-validp
                     x.flatnorm-validp
                     x.phase-fsm-validp
                     (flatnorm-setup->monotonify x.flatnorm-setup)

                     (svtv-spec-override-syntax-checks spec overridekeys params triplemaps)

                    
                     (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run)
                     (svex-env-<<= (svex-env-reduce (append (svex-alist-vars spec.initst-alist)
                                                           (svex-alistlist-vars spec.in-alists))
                                                   pipe-env)
                                  spec-env)

                     (svarlist-override-p* (svex-envlist-all-keys base-ins) '(nil :val)))
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
                                                    (phase-fsm-config->override-config x.phase-fsm-setup)))
          (params (svarlist-change-override overridekeys :test)))
       (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                     x.flatten-validp
                     x.flatnorm-validp
                     x.phase-fsm-validp
                     (flatnorm-setup->monotonify x.flatnorm-setup)

                     (svtv-spec-override-syntax-checks abs overridekeys params triplemaps)

                    
                     (svtv-override-triplemaplist-envs-ok triplemaps pipe-env spec-env spec-run)
                     (svex-env-<<= (svex-env-reduce (append (svex-alist-vars abs.initst-alist)
                                                            (svex-alistlist-vars abs.in-alists))
                                                   pipe-env)
                                  spec-env)

                     (svarlist-override-p* (svex-envlist-all-keys base-ins) '(nil :val)))
                (svex-env-<<= impl-run spec-run)))
     :hints(("Goal" :use override-transparency-of-svtv-data-obj->spec/ideal-spec-abstraction-lemma)
            (and stable-under-simplificationp
                 '(:in-theory (enable svtv-data-obj->spec
                                      svtv-data-obj->ideal-spec))))))
