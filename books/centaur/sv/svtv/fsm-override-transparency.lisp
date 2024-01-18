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

(include-book "fsm-override-defs")

(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "../svex/alist-thms"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :System))
(local (include-book "clause-processors/find-subterms" :dir :system))

(local (std::add-default-post-define-hook :fix))


;; (define base-fsm-partial-monotonic ((params svarlist-p)
;;                                     (x base-fsm-p))
;;   (b* (((base-fsm x)))
;;     (and (ec-call (svex-alist-partial-monotonic params x.values))
;;          (ec-call (svex-alist-partial-monotonic params x.nextstate))))
;;   ///
;;   (defcong set-equiv equal (base-fsm-partial-monotonic params x) 1))


(local (defthm svex-env-<<=-of-svex-env-extract
         (implies (svex-env-<<= env1 env2)
                  (svex-env-<<= (svex-env-extract vars env1)
                                (svex-env-extract vars env2)))
         :hints(("Goal" :expand ((svex-env-<<= (svex-env-extract vars env1)
                                               (svex-env-extract vars env2)))))))



(local (defthm svex-env-extract-of-append-not-intersecting
         (implies (not (intersectp-equal (alist-keys (svex-env-fix xenv)) (svarlist-fix params)))
                  (equal (svex-env-extract params (append xenv env))
                         (svex-env-extract params env)))
         :hints(("Goal" :in-theory (e/d (svex-env-extract
                                         svarlist-fix
                                         svex-env-boundp-iff-member-alist-keys)
                                        (acl2::alist-keys-member-hons-assoc-equal))))))





(local
 (defsection svex-alist-<<=-of-eval-<<=-ovmonotonic
   (local (defthm member-when-wrong-override
            (implies (and (svarlist-override-p x type1)
                          (svar-override-p v type2)
                          (not (svar-overridetype-equiv type1 type2)))
                     (not (member-equal (svar-fix v) x)))
            :hints(("Goal" :in-theory (enable svarlist-override-p
                                              svar-override-p-when-other)))))
  
   (local (defthm svex-env-ov<<=-of-append-lemma
            (implies (and (svex-env-<<= xenv yenv)
                          (svarlist-override-p (alist-keys (svex-env-fix xenv)) nil)
                          (equal (alist-keys (svex-env-fix xenv)) (alist-keys (svex-env-fix yenv))))
                     (svex-env-ov<<= (append xenv env) (append yenv env)))
            :hints (("goal" :do-not-induct t
                     :in-theory (e/d (svex-env-boundp-iff-member-alist-keys)
                                     (acl2::alist-keys-member-hons-assoc-equal)))
                    (and stable-under-simplificationp
                         `(:expand (,(car (last clause))))))))

   (defthm svex-alist-<<=-of-eval-<<=-ovmonotonic
     (implies (and (svex-alist-<<= x y)
                   (svex-env-<<= xenv yenv)
                   (svex-alist-ovmonotonic x)
                   (svarlist-override-p (alist-keys (svex-env-fix xenv)) nil)
                   (equal (alist-keys (svex-env-fix xenv)) (alist-keys (svex-env-fix yenv))))
              (svex-env-<<= (svex-alist-eval x (append xenv env))
                            (svex-alist-eval y (append yenv env))))
     :hints (("goal" :use ((:instance svex-alist-ovmonotonic-necc
                            (env1 (append xenv env))
                            (env2 (append yenv env))))
              :in-theory (e/d (svex-env-<<=-transitive-1
                               svex-env-<<=-transitive-2)
                              (svex-alist-ovmonotonic-necc))
              :do-not-induct t)))))

(defsection fsm-final-state-when-<<=-and-ovmonotonic
  (local (defun ind (ins x-initst y-initst x y)
           (if (atom ins)
               (list  x-initst y-initst x y)
             (ind (cdr ins)
                  (base-fsm-step (car ins) x-initst x)
                  (base-fsm-step (car ins) y-initst y)
                  x y))))
  
  (defthm fsm-final-state-when-<<=-and-ovmonotonic
    (implies (and (svex-alist-<<= x y)
                  (svex-alist-ovmonotonic x)
                  ;; (svex-alist-ovmonotonic y)
                  (equal (svex-alist-keys x) (svex-alist-keys y))
                  (svarlist-override-p (svex-alist-keys x) nil)
                  (svex-env-<<= x-initst y-initst))
             (svex-env-<<= (base-fsm-final-state ins x-initst x)
                           (base-fsm-final-state ins y-initst y)))
    :hints (("goal" :induct (ind ins x-initst y-initst x y)
             :in-theory (enable base-fsm-step
                                base-fsm-step-env
                                svex-envlist-<<=)
             :expand ((:free (initst x) (base-fsm-final-state ins initst x)))))))

(defsection base-fsm-<<=
  (local (in-theory (enable base-fsm-<<=)))
  (local (std::set-define-current-function base-fsm-<<=))

  (local (defun ind (ins x-initst y-initst x y)
           (if (atom ins)
               (list  x-initst y-initst x y)
             (ind (cdr ins)
                  (base-fsm-step (car ins) x-initst (base-fsm->nextstate x))
                  (base-fsm-step (car ins) y-initst (base-fsm->nextstate y))
                  x y))))
  
  (defthm fsm-eval-when-base-fsm-<<=-and-ovmonotonic
    (b* (((base-fsm x)) ((base-fsm y)))
      (implies (and (base-fsm-<<= x y)
                    (base-fsm-ovmonotonic x)
                    (base-fsm-ovmonotonic y)
                    (equal (svex-alist-keys x.nextstate) (svex-alist-keys y.nextstate))
                    (svarlist-override-p (svex-alist-keys x.nextstate) nil)
                    (svex-env-<<= x-initst y-initst))
               (svex-envlist-<<= (base-fsm-eval ins x-initst x)
                                 (base-fsm-eval ins y-initst y))))
    :hints (("goal" :induct (ind ins x-initst y-initst x y)
             :in-theory (enable base-fsm-step
                                base-fsm-step-outs
                                base-fsm-step-env
                                svex-envlist-<<=
                                base-fsm-ovmonotonic)
             :expand ((:free (initst x) (base-fsm-eval ins initst x)))))))
  
       
                                            

(defsection overridekeys-envlists-ok
  ;; :extension overridekeys-envlists-ok
  (local (in-theory (enable overridekeys-envlists-ok)))
  (local (std::set-define-current-function overridekeys-envlists-ok))

  (local (defthmd not-member-by-svar-override-p
           (implies (and (svarlist-equiv x-equiv (double-rewrite x))
                         (svarlist-override-p x-equiv type1)
                         (svar-equiv v-equiv (double-rewrite v))
                         (svar-override-p v-equiv type2)
                         (not (svar-overridetype-equiv type1 type2)))
                    (not (member-equal v x)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svar-override-p-when-other)))))

  (local (defthmd not-member-by-svar-change-override
           (implies (and (svarlist-equiv x-equiv (double-rewrite x))
                         (svarlist-override-p x-equiv type1)
                         (not (svar-overridetype-equiv type1 type2)))
                    (not (member-equal (svar-change-override v type2) x)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svar-override-p-when-other
                                             equal-of-svar-change-override)))))
  
  (local (defthm overridekeys-envs-ok-of-append-nonoverride-nonparam
           (implies (and (overridekeys-envs-ok overridekeys impl-env spec-env spec-outs)
                         (svarlist-override-p (alist-keys (svex-env-fix x1)) nil)
                         (equal (alist-keys (svex-env-fix x1)) (alist-keys (svex-env-fix x2)))
                         (svex-env-<<= x1 x2))
                    (overridekeys-envs-ok overridekeys
                                          (append x1 impl-env)
                                          (append x2 spec-env)
                                          spec-outs))
           :hints (("goal" :do-not-induct t)
                   (and stable-under-simplificationp
                        (let ((lit (car (last clause))))
                          `(:expand (,lit)
                            :use ((:instance overridekeys-envs-ok-implies
                                   (v (overridekeys-envs-ok-badguy . ,(cdr lit)))))
                            :in-theory (disable overridekeys-envs-ok-implies))))
                   (and stable-under-simplificationp
                        '(:in-theory (e/d (svar-overridekeys-envs-ok
                                           svex-env-boundp-iff-member-alist-keys
                                           not-member-by-svar-override-p
                                           not-member-by-svar-change-override)
                                          (overridekeys-envs-ok-implies
                                           acl2::alist-keys-member-hons-assoc-equal)))))))


  (local
   (defthm svex-alist-eval-when-overridekeys-envs-ok/transparent/ovmonotonic-special
     ;; this is the same as
     ;; svex-alist-eval-when-overridekeys-envs-ok/transparent/partial-monotonic
     ;; but it binds free variables params/overridekeys/subst explicitly for the theorem below.
     (implies (and ;; (overridekeys-envs-ok params overridekeys some-impl-env some-spec-env
               ;;                       (svex-alist-eval subst spec-env))
               (bind-free '((subst . (base-fsm->values$inline x))
                            (overridekeys . overridekeys))
                          (subst overridekeys))
               (overridekeys-envs-ok overridekeys impl-env spec-env
                                     (svex-alist-eval subst spec-env))
               (svex-alist-overridekey-transparent-p x overridekeys subst)
               (svex-alist-ovmonotonic x)
               (svex-alist-ovcongruent x))
              (svex-env-<<= (svex-alist-eval x impl-env)
                            (svex-alist-eval x spec-env)))
     :hints(("Goal" :in-theory (enable svex-alist-eval-when-overridekeys-envs-ok/transparent/ovmonotonic)))))


  
  (local (defun ind (x impl-envs impl-initst spec-envs spec-initst)
           (if (atom spec-envs)
               (list x impl-envs impl-initst spec-envs spec-initst)
             (ind x
                  (cdr impl-envs)
                  (base-fsm-step (car impl-envs) impl-initst (base-fsm->nextstate x))
                  (cdr spec-envs)
                  (base-fsm-step (car spec-envs) spec-initst (base-fsm->nextstate x))))))
                    
  (defthm fsm-eval-when-overridekeys-envlists-ok
    (b* ((impl-outs (base-fsm-eval impl-envs impl-initst x))
         (spec-outs (base-fsm-eval spec-envs spec-initst x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
                    (base-fsm-ovmonotonic x)
                    (base-fsm-ovcongruent x)
                    (overridekeys-envlists-ok overridekeys impl-envs spec-envs spec-outs)
                    (svex-env-<<= impl-initst spec-initst)
                    (svarlist-override-p (svex-alist-keys (base-fsm->nextstate x)) nil))
               (svex-envlist-<<= impl-outs spec-outs)))
    :hints(("Goal" :in-theory (enable base-fsm-overridekey-transparent-p
                                      base-fsm-ovmonotonic
                                      base-fsm-ovcongruent
                                      svex-envlist-<<=
                                      base-fsm-step
                                      base-fsm-step-outs
                                      base-fsm-step-env)
            :expand ((base-fsm-eval impl-envs impl-initst x)
                     (base-fsm-eval spec-envs spec-initst x)
                     (:free (spec-outs)
                      (overridekeys-envlists-ok overridekeys impl-envs spec-envs spec-outs)))
            :induct (ind x impl-envs impl-initst spec-envs spec-initst))))

  (defthm fsm-final-state-when-overridekeys-envlists-ok
    (b* ((impl-final (base-fsm-final-state impl-envs impl-initst (base-fsm->nextstate x)))
         (spec-final (base-fsm-final-state spec-envs spec-initst (base-fsm->nextstate x)))
         (spec-outs (base-fsm-eval spec-envs spec-initst x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
                    (base-fsm-ovmonotonic x)
                    (base-fsm-ovcongruent x)
                    (overridekeys-envlists-ok overridekeys impl-envs spec-envs spec-outs)
                    (svex-env-<<= impl-initst spec-initst)
                    (svarlist-override-p (svex-alist-keys (base-fsm->nextstate x)) nil)
                    (equal (len impl-envs) (len spec-envs)))
               (svex-env-<<= impl-final spec-final)))
    :hints(("Goal" :in-theory (enable base-fsm-overridekey-transparent-p
                                      base-fsm-ovmonotonic
                                      base-fsm-ovcongruent
                                      svex-envlist-<<=
                                      base-fsm-step
                                      base-fsm-step-outs
                                      base-fsm-step-env)
            :expand ((base-fsm-eval spec-envs spec-initst x)
                     (:free (x) (base-fsm-final-state spec-envs spec-initst x))
                     (:free (x) (base-fsm-final-state impl-envs impl-initst x))
                     (:free (spec-outs)
                      (overridekeys-envlists-ok overridekeys impl-envs spec-envs spec-outs)))
            :induct (ind x impl-envs impl-initst spec-envs spec-initst))))


  (local (defthm svex-envlist-<<=-transitive-1
           (implies (and (svex-envlist-<<= x y)
                         (svex-envlist-<<= y z))
                    (svex-envlist-<<= x z))
           :hints(("Goal" :in-theory (enable svex-envlist-<<=
                                             svex-env-<<=-transitive-1
                                             svex-env-<<=-transitive-2)))))

  (defthm fsm-eval-with-conservative-fsm-when-overridekeys-envlists-ok
    (b* ((impl-outs (base-fsm-eval impl-envs impl-initst x-approx))
         (spec-outs (base-fsm-eval spec-envs spec-initst x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
                    (base-fsm-ovmonotonic x)
                    (base-fsm-ovmonotonic x-approx)
                    (base-fsm-ovcongruent x)
                    ;; (base-fsm-ovcongruent x-approx)
                    (overridekeys-envlists-ok overridekeys impl-envs spec-envs spec-outs)
                    (svex-env-<<= impl-initst spec-initst)
                    (svarlist-override-p (svex-alist-keys (base-fsm->nextstate x)) nil)
                    (base-fsm-<<= x-approx x)
                    (equal (svex-alist-keys (base-fsm->nextstate x-approx))
                           (svex-alist-keys (base-fsm->nextstate x))))
               (svex-envlist-<<= impl-outs spec-outs)))
    :hints (("goal" :use ((:instance fsm-eval-when-base-fsm-<<=-and-ovmonotonic
                           (x x-approx) (y x)
                           (x-initst impl-initst) (y-initst impl-initst)
                           (ins impl-envs)))
             :in-theory (e/d () (fsm-eval-when-base-fsm-<<=-and-ovmonotonic)))))

  (defthm fsm-final-state-with-conservative-fsm-when-overridekeys-envlists-ok
    (b* ((impl-final (base-fsm-final-state impl-envs impl-initst (base-fsm->nextstate x-approx)))
         (spec-final (base-fsm-final-state spec-envs spec-initst (base-fsm->nextstate x)))
         (spec-outs (base-fsm-eval spec-envs spec-initst x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
                    (base-fsm-ovmonotonic x)
                    (base-fsm-ovcongruent x)
                    (base-fsm-ovmonotonic x-approx)
                    (overridekeys-envlists-ok overridekeys impl-envs spec-envs spec-outs)
                    (svex-env-<<= impl-initst spec-initst)
                    (svarlist-override-p (svex-alist-keys (base-fsm->nextstate x)) nil)
                    (equal (len impl-envs) (len spec-envs))
                    (base-fsm-<<= x-approx x)
                    (equal (svex-alist-keys (base-fsm->nextstate x-approx))
                           (svex-alist-keys (base-fsm->nextstate x))))
               (svex-env-<<= impl-final spec-final)))
    :hints (("goal" :use ((:instance fsm-final-state-when-<<=-and-ovmonotonic
                           (x (base-fsm->nextstate x-approx))
                           (y (base-fsm->nextstate x))
                           (x-initst impl-initst) (y-initst impl-initst)
                           (ins impl-envs)))
             :in-theory (e/d (svex-env-<<=-transitive-1
                              svex-env-<<=-transitive-2)
                             (fsm-final-state-when-<<=-and-ovmonotonic)))
            (and stable-under-simplificationp
                 '(:in-theory (enable base-fsm-<<=
                                      base-fsm-ovmonotonic))))))


(defsection overridekeys-envlists-agree*
  ;; :extension overridekeys-envlists-agree*
  (local (in-theory (enable overridekeys-envlists-agree*)))
  (local (std::set-define-current-function overridekeys-envlists-agree*))
  
  (local (defthmd not-member-by-svar-override-p
           (implies (and (svarlist-equiv x-equiv (double-rewrite x))
                         (svarlist-override-p x-equiv type1)
                         (svar-equiv v-equiv (double-rewrite v))
                         (svar-override-p v-equiv type2)
                         (not (svar-overridetype-equiv type1 type2)))
                    (not (member-equal v x)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svar-override-p-when-other)))))

  (local (defthmd not-member-by-svar-change-override
           (implies (and (svarlist-equiv x-equiv (double-rewrite x))
                         (svarlist-override-p x-equiv type1)
                         (not (svar-overridetype-equiv type1 type2)))
                    (not (member-equal (svar-change-override v type2) x)))
           :hints(("Goal" :in-theory (enable svarlist-override-p
                                             svar-override-p-when-other
                                             equal-of-svar-change-override)))))


  (local (defthm overridekeys-envs-agree*-of-append-nonoverride
           (implies (and (overridekeys-envs-agree* overridekeys impl-env spec-env spec-outs)
                         (svarlist-override-p (alist-keys (svex-env-fix x)) nil))
                    (overridekeys-envs-agree* overridekeys
                                              (append x impl-env)
                                              (append x spec-env)
                                              spec-outs))
           :hints (("goal" :do-not-induct t)
                   (and stable-under-simplificationp
                        (let ((lit (car (last clause))))
                          `(:expand (,lit)
                            :use ((:instance overridekeys-envs-agree*-implies
                                   (v (overridekeys-envs-agree*-badguy . ,(cdr lit)))))
                            :in-theory (disable overridekeys-envs-agree*-implies))))
                   (and stable-under-simplificationp
                        (let ((call (acl2::find-call-lst 'overridekeys-envs-agree*-badguy clause)))
                          (and call
                               `(:clause-processor (acl2::generalize-with-alist-cp clause '((,call . badkey)))))))
                   (and stable-under-simplificationp
                        '(:in-theory (e/d (svar-overridekeys-envs-agree*
                                           svex-env-lookup-when-not-boundp
                                           svex-env-boundp-iff-member-alist-keys
                                           not-member-by-svar-override-p
                                           not-member-by-svar-change-override)
                                          (overridekeys-envs-agree*-implies
                                           acl2::alist-keys-member-hons-assoc-equal)))))))

  (local (defun ind (x impl-envs spec-envs initst)
           (if (atom spec-envs)
               (list x impl-envs spec-envs initst)
             (ind x
                  (cdr impl-envs)
                  (cdr spec-envs)
                  (base-fsm-step (car spec-envs) initst (base-fsm->nextstate x))))))
                    
  
  (local (defthm svex-alist-eval-ovtransparent-special
           (implies (and (overridekeys-envs-agree* overridekeys impl-env spec-env
                                                   (svex-alist-eval subst
                                                                    (append pre spec-env)))
                         (svarlist-override-p (alist-keys (svex-env-fix pre)) nil)
                         (svex-alist-ovcongruent x)
                         (svex-alist-overridekey-transparent-p x overridekeys subst))
                    (svex-envs-equivalent (svex-alist-eval x (append pre impl-env))
                                          (svex-alist-eval x (append pre spec-env))))
           :hints (("goal" :use ((:instance svex-alist-eval-when-overridekeys-envs-agree*
                                  (impl-env (append pre impl-env))
                                  (spec-env (append pre spec-env))))
                    :in-theory (disable svex-alist-eval-when-overridekeys-envs-agree*)))))
                                  
  (defthm fsm-eval-when-overridekeys-envlists-agree*
    (b* ((impl-outs (base-fsm-eval impl-envs initst x))
         (spec-outs (base-fsm-eval spec-envs initst x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
                    (base-fsm-ovcongruent x)
                    (overridekeys-envlists-agree* overridekeys impl-envs spec-envs spec-outs)
                    (svarlist-override-p (svex-alist-keys (base-fsm->nextstate x)) nil))
               (svex-envlists-equivalent impl-outs spec-outs)))
    :hints(("Goal" :in-theory (enable base-fsm-overridekey-transparent-p
                                      base-fsm-ovcongruent
                                      svex-envlist-<<=
                                      base-fsm-step
                                      base-fsm-step-outs
                                      base-fsm-step-env
                                      svex-envlists-equivalent-redef)
            :expand ((base-fsm-eval impl-envs initst x)
                     (base-fsm-eval spec-envs initst x)
                     (:free (spec-outs)
                      (overridekeys-envlists-agree* overridekeys impl-envs spec-envs spec-outs)))
            :induct (ind x impl-envs spec-envs initst)))))
  


