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

(include-book "fsm-override")
(include-book "cycle-probe")
(include-book "override-envlist-defs")
(include-book "svtv-data-obj-spec")
(local (include-book "svtv-spec-override-mux"))
(local (include-book "../svex/alist-thms"))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))

(local (in-theory (disable mod floor ceiling)))

(local (std::add-default-post-define-hook :fix))




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


   (local (defthmd extract-keys-of-append-extract-when-equal
            (implies (equal (svex-env-extract keys ref-ins)
                            (svex-env-extract keys ov-ins))
                     (equal (svex-env-extract keys (append (svex-env-extract vars ref-ins)
                                                           ov-ins))
                            (svex-env-extract keys ov-ins)))
            :hints(("Goal" :in-theory (enable svex-env-extract)))))

   (local (defthm equal-extract-keys-of-compose-ref-input-envs
            (implies (equal (svex-envlist-extract-keys keys ref-inputs)
                            (svex-envlist-extract-keys keys override-inputs))
                     (equal (svex-envlist-extract-keys keys
                                                       (compose-ref-input-envs
                                                        override-inputs ref-inputs
                                                        in-vars))
                            (svex-envlist-extract-keys keys override-inputs)))
            :hints(("Goal" :in-theory (enable compose-ref-input-envs
                                              svex-envlist-extract-keys
                                              extract-keys-of-append-extract-when-equal)))))


   
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
   
   (defthm base-fsm-eval-refines-overridden-approximation-when-check-overridetriples-gen
     (b* (((base-fsm fsm))
          (svar-triples
           (svarlist-to-override-triples ov-vars))
          (triples (svar->svex-override-triplelist svar-triples fsm.values))
          (override-vars (svar-override-triplelist-override-vars svar-triples))
          (test-vars (svar-override-triplelist->testvars svar-triples))
          (spec-values (base-fsm-eval ref-inputs ref-initst fsm))
          (impl-values (base-fsm-eval override-inputs override-initst fsm))
          (non-test-params (set-difference-equal (svarlist-fix params) test-vars)))
       (implies (and (svex-alist-partial-monotonic params fsm.values)
                    (svex-alist-partial-monotonic params fsm.nextstate)
                    (no-duplicatesp-equal (svarlist-fix ov-vars))
                    (svarlist-override-p ov-vars nil)

                    (equal (svex-envlist-extract-keys non-test-params ref-inputs)
                           (svex-envlist-extract-keys non-test-params override-inputs))

                    (not (svexlist-check-overridetriples (svex-alist-vals fsm.values) triples))
                    (not (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) triples))
                    (svarlist-override-p (svex-alist-keys fsm.nextstate) nil)
                    (svarlist-override-p params :test)

                     (equal (len override-inputs) (len ref-inputs))
                     (svex-envlist-<<= (svex-envlist-reduce (set-difference-equal (svarlist-fix input-vars)
                                                                                  override-vars)
                                                            override-inputs)
                                       ref-inputs)
                     (subsetp-equal (svex-alist-vars fsm.values)
                                    (svarlist-fix input-vars))
                     (subsetp-equal (svex-alist-vars fsm.nextstate)
                                    (svarlist-fix input-vars))
                     (svar-override-triplelist-envlists-muxes-<<= svar-triples override-inputs ref-inputs spec-values)
                     (svex-envlists-muxtests-subsetp test-vars ref-inputs override-inputs)
                     (svex-env-<<= override-initst ref-initst))
                (svex-envlist-<<= impl-values spec-values)))
     :hints (("Goal" :do-not-induct t
              :use ((:instance fsm-eval-with-overrides-matches-spec-when-svexlist-check-overridetriples
                     (ref-inputs (compose-ref-input-envs
                                  override-inputs ref-inputs
                                  (append input-vars
                                          (b* ((triples
                                                (svarlist-to-override-triples ov-vars))
                                               (override-vars (svar-override-triplelist-override-vars triples)))
                                            override-vars))))
                     (override-inputs override-inputs)))
              :in-theory (e/d (svex-envlist-<<=-transitive-2
                               svex-envlist-<<=-transitive-1)
                              (fsm-eval-with-overrides-matches-spec-when-svexlist-check-overridetriples))))
     :otf-flg t)))




(local (include-book "svtv-stobj-pipeline-monotonicity"))

(define svex-alistlist-removekeys ((keys svarlist-p)
                                   (alists svex-alistlist-p))
  (if (atom alists)
      nil
    (cons (svex-alist-removekeys keys (Car alists))
          (svex-alistlist-removekeys keys (cdr alists)))))



(local
 (defsection svex-envlist-<<=-of-reduce-pipe-env->phase-envs

   ;; ;; We have the following proof obligation in svtv-data-obj->spec-run-of-overrides-when-triples-checked --
   ;; (SVEX-ENVLIST-<<=
   ;;  (SVEX-ENVLIST-REDUCE
   ;;   (SET-DIFFERENCE-EQUAL
   ;;    fsm-vars
   ;;    (APPEND override-val-vars override-test-vars))
   ;;   (SVTV-SPEC-PIPE-ENV->PHASE-ENVS spec PIPE-ENV))
   ;;  (SVTV-SPEC-PIPE-ENV->PHASE-ENVS spec SPEC-PIPE-ENV))
   ;; ;; under the assumptions
   ;; (SVEX-ENV-<<=
   ;;  (SVEX-ENV-REDUCE
   ;;   (APPEND (SVEX-ALIST-VARS spec.initst-alist)
   ;;           (SVEX-ALISTLIST-VARS spec.in-alists))
   ;;   PIPE-ENV)
   ;;  SPEC-PIPE-ENV)
   ;; (equal (svex-env-extract
   ;;         (svex-alistlist-vars
   ;;          (svex-alistlist-removekeys override-val-vars spec.override-vals))
   ;;         spec-pipe-env)
   ;;        (svex-env-extract
   ;;         (svex-alistlist-vars
   ;;          (svex-alistlist-removekeys override-val-vars spec.override-vals))
   ;;         pipe-env))
   ;; (equal (svex-env-extract
   ;;         (svex-alistlist-vars
   ;;          (svex-alistlist-removekeys override-test-vars spec.override-tests))
   ;;         spec-pipe-env)
   ;;        (svex-env-extract
   ;;         (svex-alistlist-vars
   ;;          (svex-alistlist-removekeys override-test-vars spec.override-tests))
   ;;         pipe-env))


   (defthmd append-of-filter-overrides-set-equiv-when-svarlist-override-okp
     (implies (Svarlist-override-okp x)
              (set-equiv (append (svarlist-filter-override x nil)
                                 (svarlist-filter-override x :val)
                                 (svarlist-filter-override x :test))
                         (svarlist-fix x)))
     :hints(("Goal" :in-theory (enable svarlist-override-okp
                                       svarlist-filter-override
                                       svarlist-fix
                                       svar-override-okp))))


   (defcong set-equiv svex-envlists-equivalent
     (svex-envlist-reduce vars x) 1
     :hints(("Goal" :in-theory (enable svex-envlist-reduce))))

   
   
   (local (defthm svex-envlist-<<=-of-svex-envlist-reduce-both
            (equal (svex-envlist-<<= (svex-envlist-reduce vars envs1)
                                     (svex-envlist-reduce vars envs2))
                   (svex-envlist-<<= (svex-envlist-reduce vars envs1) envs2))
            :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                              svex-envlist-reduce)
                    :induct (acl2::cdr-cdr-induct envs1 envs2)
                    :expand ((svex-envlist-reduce vars envs1)
                             (svex-envlist-reduce vars envs2))))))

   (defthm svex-env-<<=-of-reduce-append
     (equal (svex-env-<<= (svex-env-reduce (append keys1 keys2) x) y)
            (and (svex-env-<<= (svex-env-reduce keys1 x) y)
                 (svex-env-<<= (svex-env-reduce keys2 x) y)))
     :hints (("goal" :in-theory (e/d (svex-env-<<=)
                                     (svex-env-<<=-necc
                                      member-equal
                                      append
                                      svex-env-reduce-when-alist-keys-equal
                                      4vec-<<=-2vec
                                      acl2::subsetp-append1
                                      acl2::subsetp-member
                                      ))
              :use ((:instance svex-env-<<=-necc
                     (x (svex-env-reduce keys1 x)) (y y)
                     (var (svex-env-<<=-witness (svex-env-reduce (append keys1 keys2) x) y)))
                    (:instance svex-env-<<=-necc
                     (x (svex-env-reduce keys2 x)) (y y)
                     (var (svex-env-<<=-witness (svex-env-reduce (append keys1 keys2) x) y)))
                    (:instance svex-env-<<=-necc
                     (x (svex-env-reduce (append keys1 keys2) x)) (y y)
                     (var (svex-env-<<=-witness (svex-env-reduce keys1 x) y)))
                    (:instance svex-env-<<=-necc
                     (x (svex-env-reduce (append keys1 keys2) x)) (y y)
                     (var (svex-env-<<=-witness (svex-env-reduce keys2 x) y))))
              :do-not-induct t))
     :otf-flg t)

   (defthm svex-envlist-<<=-of-reduce-append
     (equal (svex-envlist-<<= (svex-envlist-reduce (append keys1 keys2) x) y)
            (and (svex-envlist-<<= (svex-envlist-reduce keys1 x) y)
                 (svex-envlist-<<= (svex-envlist-reduce keys2 x) y)))
     :hints(("Goal" :in-theory (enable svex-envlist-<<= svex-envlist-reduce)
             :induct (acl2::cdr-cdr-induct x y))))
   

   (defthmd svex-envlist-<<=-of-reduce-divide-by-override
     (implies (svarlist-override-okp keys)
              (equal (svex-envlist-<<= (svex-envlist-reduce keys x) y)
                     (and (svex-envlist-<<= (svex-envlist-reduce (svarlist-filter-override keys nil) x)
                                            (svex-envlist-reduce (svarlist-filter-override keys nil) y))
                          (svex-envlist-<<= (svex-envlist-reduce (svarlist-filter-override keys :test) x)
                                            (svex-envlist-reduce (svarlist-filter-override keys :test) y))
                          (svex-envlist-<<= (svex-envlist-reduce (svarlist-filter-override keys :val) x)
                                            (svex-envlist-reduce (svarlist-filter-override keys :val) y)))))
     :hints (("goal" :use ((:instance set-equiv-implies-svex-envlists-equivalent-svex-envlist-reduce-1
                            (vars (append (svarlist-filter-override keys nil)
                                          (svarlist-filter-override keys :val)
                                          (svarlist-filter-override keys :test)))
                            (vars-equiv (svarlist-fix keys)))
                           (:instance append-of-filter-overrides-set-equiv-when-svarlist-override-okp
                            (x keys)))
              :in-theory (disable set-equiv-implies-svex-envlists-equivalent-svex-envlist-reduce-1
                                  append-of-filter-overrides-set-equiv-when-svarlist-override-okp))))


   (defthm svarlist-filter-override-of-set-diff
     (implies (and (svarlist-p x)
                   (svarlist-p y))
              (equal (svarlist-filter-override (set-difference-equal x y) type)
                     (set-difference-equal (svarlist-filter-override x type)
                                           (svarlist-filter-override y type))))
     :hints(("Goal" :in-theory (enable svarlist-filter-override set-difference-equal))))

   (defthm svarlist-filter-override-of-append
     (equal (svarlist-filter-override (append x y) type)
            (append (svarlist-filter-override x type)
                    (svarlist-filter-override y type)))
     :hints(("Goal" :in-theory (enable svarlist-filter-override))))

   (defthm svarlist-filter-override-when-override-p
     (implies (svarlist-override-p x type1)
              (equal (svarlist-filter-override x type)
                     (and (equal (svar-overridetype-fix type)
                                 (svar-overridetype-fix type1))
                          (svarlist-fix x))))
     :hints(("Goal" :in-theory (enable svarlist-filter-override
                                       svarlist-override-p
                                       svar-override-p))))


   (local (defthm svex-env-reduce-of-svex-env-filter-overrides
           (implies (svarlist-override-p vars type)
                    (equal (svex-env-reduce vars (svex-env-filter-override env type))
                           (svex-env-reduce vars env)))
           :hints(("Goal" :in-theory (enable svex-env-reduce-redef
                                             svarlist-override-p)
                   :induct (len vars)))))
  
   (local (defthm svex-envlist-reduce-of-svex-envlist-filter-overrides
            (implies (svarlist-override-p vars type)
                     (equal (svex-envlist-reduce vars (svex-envlist-filter-override envs type))
                            (svex-envlist-reduce vars envs)))
            :hints(("Goal" :in-theory (enable svex-envlist-reduce
                                              svex-envlist-filter-override)))))
   
   (local (defthm svex-envlist-reduce-non-override-vars-of-svtv-spec-pipe-env->phase-envs
           (implies (and (svarlist-override-p vars nil)
                         (equal override-tests (svtv-spec->override-test-alists x))
                         (equal override-vals (svtv-spec->override-val-alists x))
                         (syntaxp (not (and (equal override-vals ''nil)
                                            (equal override-tests ''nil))))
                         (svarlist-override-p (svtv-cyclephaselist-keys (svtv-spec->cycle-phases x)) nil))
                    (equal (svex-envlist-reduce vars (svtv-spec-pipe-env->phase-envs x env))
                           (svex-envlist-reduce vars
                                                (svtv-spec-pipe-env->phase-envs
                                                 (change-svtv-spec x :override-test-alists nil :override-val-alists nil)
                                                 env))))
           :hints (("goal" :use ((:instance svex-envlist-reduce-of-svex-envlist-filter-overrides
                                  (envs (svtv-spec-pipe-env->phase-envs x env))
                                  (type nil)))
                    :in-theory (disable svex-envlist-reduce-of-svex-envlist-filter-overrides)))))

   (local (defthm svex-envlist-reduce-override-test-vars-of-svtv-spec-pipe-env->phase-envs
            (implies (and (svarlist-override-p vars :test)
                          (equal override-vals (svtv-spec->override-val-alists x))
                          (equal in-alists (svtv-spec->in-alists x))
                          (syntaxp (not (and (equal override-vals ''nil)
                                             (equal in-alists ''nil)))))
                    (equal (svex-envlist-reduce vars (svtv-spec-pipe-env->phase-envs x env))
                           (svex-envlist-reduce vars
                                                (svtv-spec-pipe-env->phase-envs
                                                 (change-svtv-spec x :in-alists nil :override-val-alists nil)
                                                 env))))
           :hints (("goal" :use ((:instance svex-envlist-reduce-of-svex-envlist-filter-overrides
                                  (envs (svtv-spec-pipe-env->phase-envs x env))
                                  (type :test))
                                 (:instance svex-envlist-reduce-of-svex-envlist-filter-overrides
                                  (envs (svtv-spec-pipe-env->phase-envs
                                                 (change-svtv-spec x :in-alists nil :override-val-alists nil)
                                                 env))
                                  (type :test)))
                    :in-theory (disable svex-envlist-reduce-of-svex-envlist-filter-overrides)))))

   (local (defthm svex-envlist-reduce-override-val-vars-of-svtv-spec-pipe-env->phase-envs
            (implies (and (svarlist-override-p vars :val)
                          (equal override-tests (svtv-spec->override-test-alists x))
                          (equal in-alists (svtv-spec->in-alists x))
                          (syntaxp (not (and (equal override-tests ''nil)
                                             (equal in-alists ''nil)))))
                    (equal (svex-envlist-reduce vars (svtv-spec-pipe-env->phase-envs x env))
                           (svex-envlist-reduce vars
                                                (svtv-spec-pipe-env->phase-envs
                                                 (change-svtv-spec x :in-alists nil :override-test-alists nil)
                                                 env))))
           :hints (("goal" :use ((:instance svex-envlist-reduce-of-svex-envlist-filter-overrides
                                  (envs (svtv-spec-pipe-env->phase-envs x env))
                                  (type :val))
                                 (:instance svex-envlist-reduce-of-svex-envlist-filter-overrides
                                  (envs (svtv-spec-pipe-env->phase-envs
                                                 (change-svtv-spec x :in-alists nil :override-test-alists nil)
                                                 env))
                                  (type :val)))
                    :in-theory (disable svex-envlist-reduce-of-svex-envlist-filter-overrides)))))

   (defthm svarlist-override-p-of-set-diff
     (implies (svarlist-override-p x type)
              (svarlist-override-p (set-difference-equal x y) type))
     :hints(("Goal" :in-theory (enable svarlist-override-p set-difference-equal))))

   (defthm svarlist-override-okp-of-set-diff
     (implies (svarlist-override-okp x)
              (svarlist-override-okp (set-difference-equal x y)))
     :hints(("Goal" :in-theory (enable svarlist-override-okp))))

   
   (local (defthm svex-envlist-<<=-of-reduce-pipe-env->phase-envs
            (b* (((svtv-spec spec)))
              (implies (and (svarlist-p fsm-vars)
                            (svarlist-p override-test-vars)
                            (svarlist-p override-val-vars)
                            (svarlist-override-okp fsm-vars)
                            (svarlist-override-p override-val-vars :val)
                            (svarlist-override-p override-test-vars :test)
                            (svarlist-override-p
                             (svtv-cyclephaselist-keys spec.cycle-phases) nil)
                            (SVEX-ENV-<<=
                             (SVEX-ENV-REDUCE
                              (APPEND (SVEX-ALIST-VARS spec.initst-alist)
                                      (SVEX-ALISTLIST-VARS spec.in-alists))
                              PIPE-ENV)
                             SPEC-PIPE-ENV)
                            (equal (svex-env-extract
                                    (svex-alistlist-vars
                                     (svex-alistlist-removekeys override-val-vars spec.override-vals))
                                    spec-pipe-env)
                                   (svex-env-extract
                                    (svex-alistlist-vars
                                     (svex-alistlist-removekeys override-val-vars spec.override-vals))
                                    pipe-env))
                            (equal (svex-env-extract
                                    (svex-alistlist-vars
                                     (svex-alistlist-removekeys override-test-vars spec.override-tests))
                                    spec-pipe-env)
                                   (svex-env-extract
                                    (svex-alistlist-vars
                                     (svex-alistlist-removekeys override-test-vars spec.override-tests))
                                    pipe-env)))
                       (SVEX-ENVLIST-<<=
                        (SVEX-ENVLIST-REDUCE
                         (SET-DIFFERENCE-EQUAL
                          fsm-vars
                          (APPEND override-val-vars override-test-vars))
                         (SVTV-SPEC-PIPE-ENV->PHASE-ENVS spec PIPE-ENV))
                        (SVTV-SPEC-PIPE-ENV->PHASE-ENVS spec SPEC-PIPE-ENV))))
            :hints(("Goal" :in-theory (e/d (svex-envlist-<<=-of-reduce-divide-by-override)
                                           (svex-envlist-<<=-of-svex-envlist-reduce-both))
                    :restrict ((svex-envlist-<<=-of-reduce-divide-by-override
                                ((keys (SET-DIFFERENCE-EQUAL
                                        fsm-vars
                                        (APPEND override-val-vars override-test-vars))))
                                ((keys (SET-DIFFERENCE-EQUAL
                                        fsm-vars
                                        (APPEND override-test-vars override-val-vars))))))
                    :do-not-induct t))))
))
   

   
   (defthm svex-envlist-filter-override-of-svtv-spec-pipe-env->phase-envs-test
     (implies (svarlist-override-p (svtv-cyclephaselist-keys (svtv-spec->cycle-phases x)) nil)
              (equal (svex-envlist-filter-override (svtv-spec-pipe-env->phase-envs x env)
                                                   :test)
                     (svtv-spec-pipe-env->phase-envs
                      (change-svtv-spec x :in-alists nil
                                        :override-val-alists nil)
                      env)))
     :hints(("Goal" :in-theory (enable svtv-spec-pipe-env->phase-envs))))
   
  
   
     
   (defthm svex-envlist-<<=-of-reduce-divide


(defsection svtv-data-obj->spec



  
  (local (in-theory (disable SVAR-OVERRIDE-TRIPLELIST-ENVLISTS-MUXES-<<=-IN-TERMS-OF-RENAMED-KEYS)))
  (local (std::set-define-current-function svtv-data-obj->spec))
  (local (in-theory (enable svtv-data-obj->spec)))

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

  ;; (defthm design-flatten-okp-when-flatten-validp
  ;;   (b* (((svtv-data-obj x)))
  ;;     (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
  ;;                   x.flatten-validp)
  ;;              (design-flatten-okp x.design)))
  ;;   :hints(("Goal" :in-theory (enable design-flatten-okp))))

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

  (local (defthm svarlist-override-p-of-set-diff
           (implies (svarlist-override-p x type)
                    (svarlist-override-p (set-difference-equal x y) type))
           :hints(("Goal" :in-theory (enable svarlist-override-p set-difference-equal)))))

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
                         (syntaxp (not (cw "envs3: ~x0~%envs4: ~x1~%" envs3 envs4)))
                         (syntaxp (not (equal envs2 envs4)))
                         (equal (svex-envlist-reduce vars envs4) envs3))
                    (equal (svex-envlist-<<= (svex-envlist-reduce vars envs1) envs2)
                           (svex-envlist-<<= (svex-envlist-reduce vars envs1) envs4)))
           :hints (("goal" :use ((:instance svex-envlist-<<=-of-svex-envlist-reduce-both)
                                 (:instance svex-envlist-<<=-of-svex-envlist-reduce-both
                                  (envs2 envs4)))
                    :in-theory (disable svex-envlist-<<=-of-svex-envlist-reduce-both)))))
 
  (local
   (defret <fn>-run-of-overrides-when-triples-checked
    (b* (((svtv-spec spec))
         ((svtv-data-obj x))
         ((base-fsm fsm) x.phase-fsm)
         ((pipeline-setup x.pipeline-setup))
         (spec-run (svtv-spec-run spec spec-pipe-env))
         (impl-run (svtv-spec-run spec pipe-env))
         ;; (full-override-keys (svtv-assigns-override-vars (flatnorm-res->assigns x.flatnorm)
         ;;                                                 (phase-fsm-config->override-config
         ;;                                                  x.phase-fsm-setup)))
         ;; (full-override-tests (svarlist-change-override full-override-keys :test))
         (svex-triples (svar->svex-override-triplelist
                        (svarlist-to-override-triples override-keys)
                        fsm.values))
         (unchecked-override-tests
          (svex-alistlist-vars
           (svex-alistlist-removekeys
            (svarlist-change-override override-keys :test)
            x.pipeline-setup.override-tests)))
         (unchecked-override-vals
          (svex-alistlist-vars
           (svex-alistlist-removekeys
            (svarlist-change-override override-keys :val)
            x.pipeline-setup.override-vals))))
      (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                    x.flatten-validp
                    x.flatnorm-validp
                    x.phase-fsm-validp
                    x.cycle-fsm-validp
                    x.pipeline-validp
                    (flatnorm-setup->monotonify x.flatnorm-setup)

                    (svarlist-override-p override-keys nil)
                    (no-duplicatesp-equal (svarlist-fix override-keys))
                    
                    (not (svexlist-check-overridetriples (svex-alist-vals fsm.values) svex-triples))
                    (not (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) svex-triples))

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

                    (equal (svex-env-extract unchecked-override-vals spec-pipe-env)
                           (svex-env-extract unchecked-override-vals pipe-env))
                    (equal (svex-env-extract unchecked-override-tests spec-pipe-env)
                           (svex-env-extract unchecked-override-tests pipe-env))
                    
                    (svex-alistlist-check-monotonic x.pipeline-setup.inputs)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-vals)
                    (svex-alistlist-check-monotonic x.pipeline-setup.override-tests)
                    (svex-alist-check-monotonic x.pipeline-setup.initst)
                    )
               (svex-env-<<= impl-run spec-run)))
    :hints(("Goal" :in-theory (e/d (svtv-spec-run
                                    svtv-data-obj->spec
                                    svar-override-triplelist-override-vars-of-triples-when-svarlist-override-p)
                                   (base-fsm-eval-refines-overridden-approximation-when-check-overridetriples-gen))
            :restrict ((svtv-override-triplemaplist-muxes-<<=-of-spec-outs-implies-svar-override-keys-check-separate-override-envlists-of-spec-ins
                        ((triplemaps triplemaps)))
                       (svtv-override-triplemaplist-muxtests-subsetp-of-spec-outs-implies-svex-envlists-muxtests-subsetp
                        ((triplemaps triplemaps))))
            :use ((:instance base-fsm-eval-refines-overridden-approximation-when-check-overridetriples-gen
                   (fsm (svtv-data-obj->phase-fsm x))
                   (ov-vars override-keys)
                   (params (b* (((svtv-data-obj x))
                                (full-override-keys (svtv-assigns-override-vars (flatnorm-res->assigns x.flatnorm)
                                                                                (phase-fsm-config->override-config
                                                                                 x.phase-fsm-setup))))
                             (svarlist-change-override full-override-keys :test)))
                   (ref-inputs (b* (((svtv-data-obj x))
                                    ((pipeline-setup x.pipeline-setup)))
                                 (svtv-spec-pipe-env->phase-envs
                                  (make-svtv-spec :fsm x.phase-fsm
                                                  :cycle-phases x.cycle-phases
                                                  :namemap x.namemap
                                                  :probes x.pipeline-setup.probes
                                                  :in-alists x.pipeline-setup.inputs
                                                  :override-test-alists x.pipeline-setup.override-tests
                                                  :override-val-alists x.pipeline-setup.override-vals
                                                  :initst-alist x.pipeline-setup.initst)
                                  spec-pipe-env)))
                   (input-vars (b* (((svtv-data-obj x))
                                    ((base-fsm fsm) x.phase-fsm))
                                 (append (svex-alist-vars fsm.nextstate)
                                         (svex-alist-vars fsm.values))))
                   (ref-initst (b* (((svtv-data-obj x))
                                    ((pipeline-setup x.pipeline-setup)))
                                 (svex-alist-eval x.pipeline-setup.initst spec-pipe-env)))
                   (override-inputs (svtv-spec-pipe-env->phase-envs
                                     (svtv-data-obj->spec x)
                                     pipe-env))
                   (override-initst (b* (((svtv-data-obj x))
                                         ((pipeline-setup x.pipeline-setup)))
                                      (svex-alist-eval x.pipeline-setup.initst pipe-env)))))
            :do-not-induct t))
    :otf-flg t)))


  
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
