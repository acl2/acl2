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

(include-book "fsm-base")
(include-book "override-envlist-defs")
(include-book "../svex/override")
(local (include-book "std/util/termhints" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "../svex/alist-thms"))

(defsection override-syntax-checked-fsm-transparent-override-property
  ;; We want to prove that when we evaluate an FSM on some environment with
  ;; overrides and Xes, the non-X results hold for an evaluation of the FSM on
  ;; an "agreeable" environment with fewer overrides, provided all overridden
  ;; signals satisfy the syntactic check (check-overridetriples) on the values
  ;; and nextstate of the FSM.
  (local (defthm svex-env-<<=-of-svex-env-extract
           (implies (svex-env-<<= env1 env2)
                    (svex-env-<<= (svex-env-extract vars env1)
                                  (svex-env-extract vars env2)))
           :hints(("Goal" :expand ((svex-env-<<= (svex-env-extract vars env1)
                                                 (svex-env-extract vars env2)))))))

  (local (defthm svex-env-muxtests-subsetp-of-append-spec-env-non-testvars
           (implies (not (intersectp-equal (svarlist-fix vars) (alist-keys (svex-env-fix a))))
                    (equal (svex-env-muxtests-subsetp vars (append a spec-env) impl-env)
                           (svex-env-muxtests-subsetp vars spec-env impl-env)))
           :hints(("Goal" :in-theory (enable svex-env-muxtests-subsetp
                                             svarlist-fix
                                             svex-env-boundp-iff-member-alist-keys)))))

  (local (defthm svex-env-muxtests-subsetp-of-append-impl-env-non-testvars
           (implies (not (intersectp-equal (svarlist-fix vars) (alist-keys (svex-env-fix a))))
                    (equal (svex-env-muxtests-subsetp vars spec-env (append a impl-env))
                           (svex-env-muxtests-subsetp vars spec-env impl-env)))
           :hints(("Goal" :in-theory (enable svex-env-muxtests-subsetp
                                             svarlist-fix
                                             svex-env-boundp-iff-member-alist-keys)))))
  
  (local (defthm svex-env-removekeys-when-not-intersecting
           (implies (not (intersectp-equal (double-rewrite (alist-keys (svex-env-fix x))) (svarlist-fix vars)))
                    (equal (svex-env-removekeys vars x)
                           (svex-env-fix x)))
           :hints(("Goal" :in-theory (enable svex-env-removekeys
                                             svex-env-fix
                                             alist-keys)))))
  
  (local (in-theory (enable 4veclist-nth-safe)))

  (local (defthm open-nth
           (implies (syntaxp (quotep n))
                    (equal (nth n x)
                           (if (zp n)
                               (car x)
                             (nth (1- n) (cdr x)))))))

  (local (defthm svex-eval-when-var
           (implies (svex-case x :var)
                    (equal (svex-eval x env)
                           (svex-env-lookup (svex-var->name x) env)))
           :hints(("Goal" :in-theory (enable svex-eval)))))

  (local (defthm member-vars-when-not-lookups
           (implies (and (not (svex-override-triplelist-lookup var x))
                         (not (svex-override-triplelist-lookup-valvar var x)))
                    (not (member-equal var (svex-override-triplelist-vars x))))
           :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                             svex-override-triplelist-lookup-valvar
                                             svex-override-triplelist-lookup)))))

  (local (defthm member-vars-when-not-lookups-svar
           (implies (and (not (svex-override-triplelist-lookup var (svar->svex-override-triplelist x values)))
                         (not (svex-override-triplelist-lookup-valvar var (svar->svex-override-triplelist x values))))
                    (not (member-equal var (svar-override-triplelist-override-vars x))))
           :hints(("Goal" :use ((:instance member-vars-when-not-lookups
                                 (x (svar->svex-override-triplelist x values))))))))

  (local (defthm lookup-when-svex-envs-agree-except
           (implies (and (svex-envs-agree-except vars y x)
                         (not (member-equal (svar-fix v) (svarlist-fix vars))))
                    (equal (equal (svex-env-lookup v x) (svex-env-lookup v y)) t))
           :hints(("Goal" :in-theory (enable SVEX-ENVS-AGREE-EXCEPT-IMPLIES)))))

  (defthm 4vec-override-mux-agrees-implies-muxes-agree-simple-rev
    (implies (and (4vec-override-mux-agrees impl-test impl-val spec-test spec-val spec-ref)
                  (4vec-muxtest-subsetp spec-test impl-test))
             (equal (equal (4vec-bit?! spec-test spec-val spec-ref)
                           (4vec-bit?! impl-test impl-val spec-ref))
                    t))
    :hints (("goal" :use 4vec-override-mux-agrees-implies-muxes-agree-simple
             :in-theory (disable 4vec-override-mux-agrees-implies-muxes-agree-simple))))
  
  (defthm eval-when-muxes-agree-and-svex-check-override-triple-check-lemma
    (b* ((triples (svar->svex-override-triplelist svar-triples values))
         (lookup (svex-override-triplelist-lookup test triples)))
      (implies (and (svex-env-muxtests-subsetp (SVAR-OVERRIDE-TRIPLELIST->TESTVARS SVAR-TRIPLES)
                                               spec-env override-env)
                    (svar-override-triplelist-muxes-agree
                     svar-triples override-env spec-env (svex-alist-eval values spec-env))
                    lookup)
               (equal (equal (4vec-bit?! (svex-env-lookup test spec-env)
                                         (svex-env-lookup
                                          (svex-override-triple->valvar lookup)
                                          spec-env)
                                         (svex-eval (svex-override-triple->valexpr lookup) spec-env))
                             (4vec-bit?! (svex-env-lookup test override-env)
                                         (svex-env-lookup
                                          (svex-override-triple->valvar lookup)
                                          override-env)
                                         (svex-eval (svex-override-triple->valexpr lookup) spec-env)))
                      t)))
    :hints(("Goal" :in-theory (enable svex-env-muxtests-subsetp
                                      svar-override-triplelist->testvars
                                      svar-override-triplelist-muxes-agree
                                      svar->svex-override-triplelist
                                      svex-override-triplelist-lookup
                                      SVAR-OVERRIDE-TRIPLE-MUX-AGREES
                                      ;; 4vec-override-mux-agrees
                                      ))))
  
  (defthm eval-when-muxes-agree-and-svex-check-override-triple-check
    (implies (and (equal (svex-override-triple-check test then else (svar->svex-override-triplelist svar-triples values))
                         t)
                  (svex-env-muxtests-subsetp (SVAR-OVERRIDE-TRIPLELIST->TESTVARS SVAR-TRIPLES)
                                             spec-env override-env)
                  (svar-override-triplelist-muxes-agree
                   svar-triples override-env spec-env (svex-alist-eval values spec-env))
                  (equal ref-val (svex-eval else spec-env)))
             (equal (equal (4vec-bit?! (svex-eval test spec-env)
                                       (svex-eval then spec-env)
                                       ref-val)
                           (4vec-bit?! (svex-eval test override-env)
                                       (svex-eval then override-env)
                                       ref-val))
                    t))
    :hints(("Goal" :in-theory (e/d (svex-override-triple-check)
                                   (eval-when-muxes-agree-and-svex-check-override-triple-check-lemma))
            :use ((:instance eval-when-muxes-agree-and-svex-check-override-triple-check-lemma
                   (test (svex-var->name test)))))))
                  
  
  ;; Step 1: evaluation of some svexes agrees when muxes-agree and overridetriple check ok
  (std::defret-mutual evals-agree-when-override-muxes-agree-and-check-overridetriples
    (defret eval-when-muxes-agree-and-<fn>
      :pre-bind ((triples (svar->svex-override-triplelist svar-triples values)))
      (b* ((override-vars (svar-override-triplelist-override-vars svar-triples))
           (test-vars (svar-override-triplelist->testvars svar-triples))
           (spec-values (svex-alist-eval values spec-env))
           (spec-eval (svex-eval x spec-env))
           (impl-eval (svex-eval x override-env)))
        (implies (and (not bad)
                      (svar-override-triplelist-muxes-agree svar-triples override-env spec-env spec-values)
                      (svex-envs-agree-except override-vars override-env spec-env)
                      (svex-env-muxtests-subsetp test-vars spec-env override-env))
                 (equal spec-eval impl-eval)))
      :hints ('(:expand ((:free (triples) <call>)
                         (:free (env) (svex-eval x env)))))
      :fn svex-check-overridetriples)

    (defret eval-when-muxes-agree-and-<fn>
      :pre-bind ((triples (svar->svex-override-triplelist svar-triples values)))
      (b* ((override-vars (svar-override-triplelist-override-vars svar-triples))
           (test-vars (svar-override-triplelist->testvars svar-triples))
           (spec-values (svex-alist-eval values spec-env))
           (spec-eval (svex-eval x spec-env))
           (impl-eval (svex-eval x override-env)))
        (implies (and (not bad)
                      (svex-case x :call)
                      (svar-override-triplelist-muxes-agree svar-triples override-env spec-env spec-values)
                      (svex-envs-agree-except override-vars override-env spec-env)
                      (svex-env-muxtests-subsetp test-vars spec-env override-env))
                 (equal spec-eval impl-eval)))
      :hints ('(:expand ((:free (triples) <call>)
                         (:free (env) (svex-eval x env)))
                :in-theory (enable svex-apply)))
      :fn svex-check-overridetriples-call)

    (defret eval-when-muxes-agree-and-<fn>
      :pre-bind ((triples (svar->svex-override-triplelist svar-triples values)))
      (b* ((override-vars (svar-override-triplelist-override-vars svar-triples))
           (test-vars (svar-override-triplelist->testvars svar-triples))
           (spec-values (svex-alist-eval values spec-env))
           (spec-eval (svexlist-eval x spec-env))
           (impl-eval (svexlist-eval x override-env)))
        (implies (and (not bad)
                      (svar-override-triplelist-muxes-agree svar-triples override-env spec-env spec-values)
                      (svex-envs-agree-except override-vars override-env spec-env)
                      (svex-env-muxtests-subsetp test-vars spec-env override-env))
                 (equal spec-eval impl-eval)))
      :hints ('(:expand ((:free (triples) <call>)
                         (:free (env) (svexlist-eval x env)))))
      :fn svex-args-check-overridetriples)

    (defret eval-when-muxes-agree-and-<fn>
      :pre-bind ((triples (svar->svex-override-triplelist svar-triples values)))
      (b* ((override-vars (svar-override-triplelist-override-vars svar-triples))
           (test-vars (svar-override-triplelist->testvars svar-triples))
           (spec-values (svex-alist-eval values spec-env))
           (spec-eval (svexlist-eval x spec-env))
           (impl-eval (svexlist-eval x override-env)))
        (implies (and (not bad)
                      (svar-override-triplelist-muxes-agree svar-triples override-env spec-env spec-values)
                      (svex-envs-agree-except override-vars override-env spec-env)
                      (svex-env-muxtests-subsetp test-vars spec-env override-env))
                 (equal spec-eval impl-eval)))
      :hints ('(:expand ((:free (triples) <call>)
                         (:free (env) (svexlist-eval x env)))))
      :fn svexlist-check-overridetriples)
    :hints (("goal" :induct (SVEX-CHECK-OVERRIDETRIPLES-FLAG
                             flag n x (svar->svex-override-triplelist svar-triples values))
             :do-not-induct t))
    :otf-flg t
    :mutual-recursion svex-check-overridetriples)

  (local (defthmd svex-alist-eval-is-pairlis$
           (equal (svex-alist-eval x env)
                  (pairlis$ (svex-alist-keys x)
                            (svexlist-eval (svex-alist-vals x) env)))
           :hints(("Goal" :in-theory (enable svex-alist-vals
                                             svex-alist-keys
                                             svexlist-eval
                                             svex-alist-eval
                                             pairlis$)))))
  
  (defret svex-alist-eval-when-muxes-agree-and-<fn>
    :pre-bind ((triples (svar->svex-override-triplelist svar-triples values))
               (x (svex-alist-vals alist)))
    (b* ((override-vars (svar-override-triplelist-override-vars svar-triples))
         (test-vars (svar-override-triplelist->testvars svar-triples))
         (spec-values (svex-alist-eval values spec-env))
         (spec-eval (svex-alist-eval alist spec-env))
         (impl-eval (svex-alist-eval alist override-env)))
      (implies (and (not bad)
                    (svar-override-triplelist-muxes-agree svar-triples override-env spec-env spec-values)
                    (svex-envs-agree-except override-vars override-env spec-env)
                    (svex-env-muxtests-subsetp test-vars spec-env override-env))
               (equal spec-eval impl-eval)))
    :hints(("Goal" :in-theory (enable svex-alist-eval-is-pairlis$)
            :restrict ((svex-alist-eval-is-pairlis$ ((x alist))))))
    :fn svexlist-check-overridetriples)

  (local (defthm svex-env-extract-of-append-extract-superset
           (implies (subsetp-equal (Svarlist-fix keys1) (svarlist-fix keys2))
                    (equal (svex-env-extract keys1 (append (svex-env-extract keys2 x) rest))
                           (svex-env-extract keys1 x)))
           :hints(("Goal" :induct (svex-env-extract keys1 x)
                   :expand ((svarlist-fix keys1)
                            (:free (x) (svex-env-extract keys1 x)))
                   :in-theory (enable subsetp-equal (:i svex-env-extract))))))
  
  (local (defthm svex-env-extract-of-append-non-intersect
           (implies (not (intersectp-equal (alist-keys (svex-env-fix env1)) (svarlist-fix keys1)))
                    (equal (svex-env-extract keys1 (append env1 rest))
                           (svex-env-extract keys1 rest)))
           :hints(("Goal" :induct (svex-env-extract keys1 x)
                   :expand ((svarlist-fix keys1)
                            (:free (x) (svex-env-extract keys1 x)))
                   :in-theory (enable intersectp-equal (:i svex-env-extract)
                                      svex-env-boundp-iff-member-alist-keys)))))

  (local (defthm svex-env-extract-of-append-when-agree-special
           (b* ((non-test-params
                 (set-difference-equal (svarlist-fix params) (svarlist-fix test-vars))))
             (implies (equal (svex-env-extract non-test-params spec-env)
                             (svex-env-extract non-test-params override-env))
                      (equal (svex-env-extract params (append (svex-env-extract test-vars override-env)
                                                              spec-env))
                             (svex-env-extract params override-env))))
           :hints(("Goal" :in-theory (enable svex-env-extract set-difference-equal svarlist-fix)))))

  (local (defthm not-intersect-intermediate-env-keys-when-not-intersect-val-vars
           (implies (not (intersectp-equal (svar-override-triplelist->valvars svar-triples)
                                           (svarlist-fix params)))
                    (not (intersectp-equal (svarlist-fix params)
                                           (alist-keys
                                            (svar-override-triplelist-mux-override-intermediate-env
                                             svar-triples override-env spec-env ref-env)))))
           :hints(("Goal" :in-theory (enable svar-override-triplelist-mux-override-intermediate-env
                                             svar-override-triplelist->valvars
                                             alist-keys)))))

  (local (defthm svar-override-triple->valvar-of-lookup-valvar
           (implies (member-equal (svar-fix key) (svar-override-triplelist->valvars x))
                    (equal (svar-override-triple->valvar (svar-override-triplelist-lookup-valvar key x))
                           (svar-fix key)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist-lookup-valvar
                                             svar-override-triplelist->valvars)))))

  (local (defthmd svar-override-triplelist-override-vars-under-set-equiv
           (set-equiv (svar-override-triplelist-override-vars x)
                      (append (svar-override-triplelist->testvars x)
                              (svar-override-triplelist->valvars x)))
           :hints(("Goal" :in-theory (enable svar-override-triplelist->valvars
                                             svar-override-triplelist->testvars
                                             svar-override-triplelist-override-vars
                                             acl2::set-unequal-witness-rw)))))
  
  ;; (local (defthm override-env-<<=-intermediate-env-special
  ;;          (implies (and (subsetp-equal (svar-override-triplelist->testvars triples)
  ;;                                       (svarlist-fix params))
  ;;                        (svex-env-<<= (svex-env-removekeys (svar-override-triplelist-override-vars triples)
  ;;                                                           impl-env)
  ;;                                      spec-env)
  ;;                        (not (intersectp-equal (svar-override-triplelist->testvars triples)
  ;;                                               (svar-override-triplelist->valvars triples))))
  ;;                   (svex-env-<<= impl-env (append
  ;;                                           (svar-override-triplelist-mux-override-intermediate-env
  ;;                                            triples impl-env spec-env ref-env)
  ;;                                           (svex-env-extract params impl-env)
  ;;                                           spec-env)))
  ;;          :hints (;; ("goal" :in-theory (enable svar-override-triplelist-override-vars-under-set-equiv))
  ;;                  (and stable-under-simplificationp
  ;;                       (let* ((lit (car (last clause)))
  ;;                              (w `(svex-env-<<=-witness . ,(cdr lit))))
  ;;                         `(:expand (,lit)
  ;;                           :use ((:instance svex-env-<<=-necc
  ;;                                  (x (svex-env-removekeys (svar-override-triplelist-override-vars triples) impl-env))
  ;;                                  (y spec-env)
  ;;                                  (var ,w)))
  ;;                           :in-theory (e/d (svar-override-triplelist-override-vars-under-set-equiv)
  ;;                                           (svex-env-<<=-necc))))))))

  ;; (local (defthm muxes-agree-of-intermediate-env-special
  ;;          (implies (and (subsetp-equal (svar-override-triplelist->testvars triples)
  ;;                                       (svarlist-fix params))
  ;;                        (svex-env-<<= (svex-env-removekeys (svar-override-triplelist-override-vars triples)
  ;;                                                           impl-env)
  ;;                                      spec-env)
  ;;                        (not (intersectp-equal (svar-override-triplelist->testvars triples)
  ;;                                               (svar-override-triplelist->valvars triples))))
  ;;                   (svex-env-<<= impl-env (append
  ;;                                           (svar-override-triplelist-mux-override-intermediate-env
  ;;                                            triples impl-env spec-env ref-env)
  ;;                                           (svex-env-extract params impl-env)
  ;;                                           spec-env)))
  ;;          :hints (;; ("goal" :in-theory (enable svar-override-triplelist-override-vars-under-set-equiv))
  ;;                  (and stable-under-simplificationp
  ;;                       (let* ((lit (car (last clause)))
  ;;                              (w `(svex-env-<<=-witness . ,(cdr lit))))
  ;;                         `(:expand (,lit)
  ;;                           :use ((:instance svex-env-<<=-necc
  ;;                                  (x (svex-env-removekeys (svar-override-triplelist-override-vars triples) impl-env))
  ;;                                  (y spec-env)
  ;;                                  (var ,w)))
  ;;                           :in-theory (e/d (svar-override-triplelist-override-vars-under-set-equiv)
  ;;                                           (svex-env-<<=-necc))))))))

  
  ;; We need an intermediate env that satisfies the requirements of the
  ;; override-env in svex-alist-eval-when-muxes-agree-and-<fn> and also is >>=
  ;; the override-env we actually want here.
  


  
  (defret svex-alist-eval-when-muxes-<<=-and-<fn>
    :pre-bind (;; (svar-triples (svarlist-to-override-triples ov-vars))
               (triples (svar->svex-override-triplelist svar-triples values))
               (x (svex-alist-vals alist)))
      (b* ((override-vars (svar-override-triplelist-override-vars svar-triples))
           (test-vars (svar-override-triplelist->testvars svar-triples))
           (val-vars (svar-override-triplelist->valvars svar-triples))
           (spec-values (svex-alist-eval values spec-env))
           (spec-eval (svex-alist-eval alist spec-env))
           (impl-eval (svex-alist-eval alist override-env))
           (non-test-params (set-difference-equal (svarlist-fix params) test-vars)))
        (implies (and (not bad)
                      ;; (no-duplicatesp-equal (svarlist-fix ov-vars))
                      ;; (svarlist-override-p ov-vars nil)
                      (no-duplicatesp-equal val-vars)
                      (not (intersectp-equal val-vars test-vars))
                      (svex-alist-partial-monotonic params ;; test-vars
                                                    alist)
                      ;; (subsetp-equal test-vars (svarlist-fix params))
                      (not (intersectp-equal val-vars (svarlist-fix params)))
                      (equal (svex-env-extract non-test-params spec-env)
                             (svex-env-extract non-test-params override-env))
                      (svar-override-triplelist-muxes-<<= svar-triples override-env spec-env spec-values)
                      (svex-env-<<= (svex-env-removekeys override-vars override-env) spec-env)
                      (svex-env-muxtests-subsetp test-vars spec-env override-env))
                 (svex-env-<<= impl-eval spec-eval)))
      :hints ((acl2::use-termhint
               (b* (;; (svar-triples (svarlist-to-override-triples ov-vars))
                    (test-vars (svar-override-triplelist->testvars svar-triples))
                    (spec-values (svex-alist-eval values spec-env))
                    (intermediate-env (append (svar-override-triplelist-mux-override-intermediate-env
                                               svar-triples override-env spec-env spec-values)
                                              (svex-env-extract test-vars override-env)
                                              spec-env)))
                 `(:use ((:instance eval-when-svex-alist-partial-monotonic
                          (param-keys ,(acl2::hq params))
                          (x alist)
                          (env1 override-env)
                          (env2 ,(acl2::hq intermediate-env)))
                         (:instance svex-alist-eval-when-muxes-agree-and-<fn>
                          (svar-triples ,(acl2::hq svar-triples))
                          (override-env ,(acl2::hq intermediate-env))))
                   :in-theory (disable eval-when-svex-alist-partial-monotonic
                                       svex-alist-eval-when-muxes-agree-and-<fn>)))))
      :fn svexlist-check-overridetriples)
  

  (local (defun ind (ref-inputs ref-initst override-inputs override-initst fsm)
           (if (atom ref-inputs)
               (list ref-initst override-initst)
             (ind (cdr ref-inputs)
                  (base-fsm-step (car ref-inputs) ref-initst (base-fsm->nextstate fsm))
                  (cdr override-inputs)
                  (base-fsm-step (car override-inputs) override-initst (base-fsm->nextstate fsm))
                  fsm))))

  (local (defthm not-intersectp-of-set-diff
           (implies (not (intersectp-equal x y))
                    (not (intersectp-equal x (set-difference-equal y z))))))

  (local (defthmd member-by-svarlist-override-p
           (implies (and (svar-override-p x xtype)
                         (svarlist-override-p y ytype)
                         (not (equal (svar-overridetype-fix xtype)
                                     (svar-overridetype-fix ytype))))
                    (not (member-equal (svar-fix x) y)))
           :hints(("Goal" :in-theory (enable svarlist-override-p)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable svar-override-p))))))
  
  (local (defthm intersectp-by-svarlist-override-p
           (implies (and (svarlist-override-p x xtype)
                         (svarlist-override-p y ytype)
                         (not (equal (svar-overridetype-fix xtype)
                                     (svar-overridetype-fix ytype))))
                    (not (intersectp-equal (svarlist-fix x) y)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svarlist-fix
                                             member-by-svarlist-override-p)))))

  (local (defthm intersectp-by-svarlist-override-p-2
           (implies (and (svarlist-override-p x xtype)
                         (not (equal (svar-overridetype-fix xtype) :val)))
                    (not (intersectp-equal (svarlist-fix x)
                                           (svar-override-triplelist->valvars
                                            (svarlist-to-override-triples ov-vars)))))
           :hints (("goal" :use ((:instance intersectp-by-svarlist-override-p
                                  (y (svar-override-triplelist->valvars
                                      (svarlist-to-override-triples ov-vars)))
                                  (ytype :val)))
                    :in-theory (enable valvars-of-svarlist-to-override-triples)))))
  

  (defthm fsm-eval-with-overrides-matches-spec-when-svexlist-check-overridetriples
    (b* (((base-fsm fsm))
         (svar-triples (svarlist-to-override-triples ov-vars))
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
                    (svar-override-triplelist-envlists-muxes-<<= svar-triples override-inputs ref-inputs spec-values)
                    (svex-envlist-<<= (svex-envlist-removekeys override-vars override-inputs)  ref-inputs)
                    (svex-envlists-muxtests-subsetp test-vars ref-inputs override-inputs)
                    (svex-env-<<= override-initst ref-initst))
               (svex-envlist-<<= impl-values spec-values)))
    :hints (("goal" :induct (ind ref-inputs ref-initst override-inputs override-initst fsm)
             :expand ((:free (vars) (svex-envlist-removekeys vars override-inputs))
                      (:free (keys) (svex-envlist-extract-keys keys ref-inputs))
                      (:free (keys) (svex-envlist-extract-keys keys override-inputs))
                      (:free (vars) (svex-envlists-muxtests-subsetp vars ref-inputs override-inputs))
                      (:free (envs1) (svex-envlist-<<= envs1 ref-inputs))
                      (:free (svar-triples vals) (svar-override-triplelist-envlists-muxes-<<=
                                     svar-triples override-inputs ref-inputs vals))
                      (base-fsm-eval override-inputs override-initst fsm)
                      (base-fsm-eval ref-inputs ref-initst fsm)
                      (:free (a b c d) (svex-envlist-<<= (cons a b) (cons c d))))
             :in-theory (e/d (base-fsm-step
                              base-fsm-step-env
                              base-fsm-step-outs)
                             ()))))

  (defthm fsm-final-state-with-overrides-matches-spec-when-svexlist-check-overridetriples
    (b* (((base-fsm fsm))
         (svar-triples (svarlist-to-override-triples ov-vars))
         (triples (svar->svex-override-triplelist svar-triples fsm.values))
         (override-vars (svar-override-triplelist-override-vars svar-triples))
         (test-vars (svar-override-triplelist->testvars svar-triples))
         (spec-values (base-fsm-eval ref-inputs ref-initst fsm))
         (spec-final-st (base-fsm-final-state ref-inputs ref-initst fsm.nextstate))
         (impl-final-st (base-fsm-final-state override-inputs override-initst fsm.nextstate))
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
                    (svar-override-triplelist-envlists-muxes-<<= svar-triples override-inputs ref-inputs spec-values)
                    (svex-envlist-<<= (svex-envlist-removekeys override-vars override-inputs)  ref-inputs)
                    (svex-envlists-muxtests-subsetp test-vars ref-inputs override-inputs)
                    (svex-env-<<= override-initst ref-initst))
               (svex-env-<<= impl-final-st spec-final-st)))
    :hints (("goal" :induct (ind ref-inputs ref-initst override-inputs override-initst fsm)
             :expand ((:free (vars) (svex-envlist-removekeys vars override-inputs))
                      (:free (keys) (svex-envlist-extract-keys keys ref-inputs))
                      (:free (keys) (svex-envlist-extract-keys keys override-inputs))
                      (:free (vars) (svex-envlists-muxtests-subsetp vars ref-inputs override-inputs))
                      (:free (envs1) (svex-envlist-<<= envs1 ref-inputs))
                      (:free (svar-triples vals) (svar-override-triplelist-envlists-muxes-<<=
                                     svar-triples override-inputs ref-inputs vals))
                      (:free (fsm) (base-fsm-final-state override-inputs override-initst fsm))
                      (:free (fsm) (base-fsm-final-state ref-inputs ref-initst fsm))
                      (:free (a b c d) (svex-envlist-<<= (cons a b) (cons c d))))
             :in-theory (e/d (base-fsm-step
                              base-fsm-step-env
                              base-fsm-step-outs)
                             ()))))
  )
