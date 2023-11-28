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

(include-book "../svex/override-transparency-and-monotonicity")
(include-book "../svex/override-transparency-and-ovmonotonicity")
(include-book "fsm-base")

(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "../svex/alist-thms"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :System))
(local (include-book "clause-processors/find-subterms" :dir :system))

(local (std::add-default-post-define-hook :fix))

(define base-fsm-overridekey-transparent-p ((x base-fsm-p)
                                            (overridekeys svarlist-p))
  (b* (((base-fsm x)))
    (and (ec-call (svex-alist-overridekey-transparent-p x.values overridekeys x.values))
         (ec-call (svex-alist-overridekey-transparent-p x.nextstate overridekeys x.values))))
  ///
  (defcong set-equiv equal (base-fsm-overridekey-transparent-p x overridekeys) 2)

  (defthm base-fsm-overridekey-transparent-p-of-svarlist-change-override
    (equal (base-fsm-overridekey-transparent-p x (svarlist-change-override overridekeys type))
           (base-fsm-overridekey-transparent-p x overridekeys))))

(define base-fsm-partial-monotonic ((params svarlist-p)
                                    (x base-fsm-p))
  (b* (((base-fsm x)))
    (and (ec-call (svex-alist-partial-monotonic params x.values))
         (ec-call (svex-alist-partial-monotonic params x.nextstate))))
  ///
  (defcong set-equiv equal (base-fsm-partial-monotonic params x) 1))


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


(local (defthm svex-alist-<<=-of-eval-<<=-partial-monotonic
         (implies (and (svex-alist-<<= x y)
                       (svex-env-<<= xenv yenv)
                       (svex-alist-partial-monotonic params x)
                       (not (intersectp-equal (alist-keys (svex-env-fix xenv)) (svarlist-fix params)))
                       (equal (alist-keys (svex-env-fix xenv)) (alist-keys (svex-env-fix yenv))))
                  (svex-env-<<= (svex-alist-eval x (append xenv env))
                                (svex-alist-eval y (append yenv env))))
         :hints (("goal" :use ((:instance eval-when-svex-alist-partial-monotonic
                                (param-keys params)
                                (env1 (append xenv env))
                                (env2 (append yenv env))))
                  :in-theory (e/d (svex-env-<<=-transitive-1
                                   svex-env-<<=-transitive-2)
                                  (eval-when-svex-alist-partial-monotonic))
                  :do-not-induct t))))

(defsection fsm-final-state-when-<<=-and-partial-monotonic
  

  (local (defun ind (ins x-initst y-initst x y)
           (if (atom ins)
               (list  x-initst y-initst x y)
             (ind (cdr ins)
                  (base-fsm-step (car ins) x-initst x)
                  (base-fsm-step (car ins) y-initst y)
                  x y))))
  
  (defthm fsm-final-state-when-<<=-and-partial-monotonic
    (implies (and (svex-alist-<<= x y)
                  (svex-alist-partial-monotonic params x)
                  (svex-alist-partial-monotonic params y)
                  (equal (svex-alist-keys x) (svex-alist-keys y))
                  (not (intersectp-equal (svex-alist-keys x) (svarlist-fix params)))
                  (svex-env-<<= x-initst y-initst))
             (svex-env-<<= (base-fsm-final-state ins x-initst x)
                           (base-fsm-final-state ins y-initst y)))
    :hints (("goal" :induct (ind ins x-initst y-initst x y)
             :in-theory (enable base-fsm-step
                                base-fsm-step-env
                                svex-envlist-<<=
                                base-fsm-partial-monotonic)
             :expand ((:free (initst x) (base-fsm-final-state ins initst x)))))))

(define base-fsm-<<= ((x base-fsm-p) (y base-fsm-p))
  (b* (((base-fsm x)) ((base-fsm y)))
    (and (ec-call (svex-alist-<<= x.values y.values))
         (ec-call (svex-alist-<<= x.nextstate y.nextstate))))
  ///

  (local (defun ind (ins x-initst y-initst x y)
           (if (atom ins)
               (list  x-initst y-initst x y)
             (ind (cdr ins)
                  (base-fsm-step (car ins) x-initst (base-fsm->nextstate x))
                  (base-fsm-step (car ins) y-initst (base-fsm->nextstate y))
                  x y))))
  
  (defthm fsm-eval-when-base-fsm-<<=-and-partial-monotonic
    (b* (((base-fsm x)) ((base-fsm y)))
      (implies (and (base-fsm-<<= x y)
                    (base-fsm-partial-monotonic params x)
                    (base-fsm-partial-monotonic params y)
                    (equal (svex-alist-keys x.nextstate) (svex-alist-keys y.nextstate))
                    (not (intersectp-equal (svex-alist-keys x.nextstate) (svarlist-fix params)))
                    (svex-env-<<= x-initst y-initst))
               (svex-envlist-<<= (base-fsm-eval ins x-initst x)
                                 (base-fsm-eval ins y-initst y))))
    :hints (("goal" :induct (ind ins x-initst y-initst x y)
             :in-theory (enable base-fsm-step
                                base-fsm-step-outs
                                base-fsm-step-env
                                svex-envlist-<<=
                                base-fsm-partial-monotonic)
             :expand ((:free (initst x) (base-fsm-eval ins initst x)))))))
  
       
                                            

(define overridekeys-envlists-ok ((params svarlist-p)
                                  (overridekeys svarlist-p)
                                  (impl-envs svex-envlist-p)
                                  (spec-envs svex-envlist-p)
                                  (spec-outs svex-envlist-p))
  :guard (eql (len spec-envs) (len spec-outs))
  :returns (ok)
  :measure (len spec-envs)
  (if (atom spec-envs)
      (atom impl-envs)
    (and (overridekeys-envs-ok params overridekeys (car impl-envs) (car spec-envs) (car spec-outs))
         (overridekeys-envlists-ok params overridekeys (cdr impl-envs) (cdr spec-envs) (cdr spec-outs))))
  ///

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
           (implies (and (overridekeys-envs-ok params overridekeys impl-env spec-env spec-outs)
                         (not (intersectp-equal (svarlist-fix params) (alist-keys (svex-env-fix x1))))
                         (svarlist-override-p (alist-keys (svex-env-fix x1)) nil)
                         (equal (alist-keys (svex-env-fix x1)) (alist-keys (svex-env-fix x2)))
                         (svex-env-<<= x1 x2))
                    (overridekeys-envs-ok params overridekeys
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
   (defthm svex-alist-eval-when-overridekeys-envs-ok/transparent/partial-monotonic-special
     ;; this is the same as
     ;; svex-alist-eval-when-overridekeys-envs-ok/transparent/partial-monotonic
     ;; but it binds free variables params/overridekeys/subst explicitly for the theorem below.
     (implies (and ;; (overridekeys-envs-ok params overridekeys some-impl-env some-spec-env
               ;;                       (svex-alist-eval subst spec-env))
               (bind-free '((subst . (base-fsm->values$inline x))
                            (params . params)
                            (overridekeys . overridekeys))
                          (subst params overridekeys))
               (overridekeys-envs-ok params overridekeys impl-env spec-env
                                     (svex-alist-eval subst spec-env))
               (svex-alist-overridekey-transparent-p x overridekeys subst)
               (svex-alist-partial-monotonic params x)
               (not (intersectp-equal (svarlist-fix params)
                                      (svarlist-change-override overridekeys :val))))
              (svex-env-<<= (svex-alist-eval x impl-env)
                            (svex-alist-eval x spec-env)))))


  
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
                    (base-fsm-partial-monotonic params x)
                    (overridekeys-envlists-ok params overridekeys impl-envs spec-envs spec-outs)
                    (not (intersectp-equal (svarlist-fix params)
                                           (svarlist-change-override overridekeys :val)))
                    (svex-env-<<= impl-initst spec-initst)
                    (not (intersectp-equal (svarlist-fix params)
                                           (svex-alist-keys (base-fsm->nextstate x))))
                    (svarlist-override-p (svex-alist-keys (base-fsm->nextstate x)) nil))
               (svex-envlist-<<= impl-outs spec-outs)))
    :hints(("Goal" :in-theory (enable base-fsm-overridekey-transparent-p
                                      base-fsm-partial-monotonic
                                      svex-envlist-<<=
                                      base-fsm-step
                                      base-fsm-step-outs
                                      base-fsm-step-env)
            :expand ((base-fsm-eval impl-envs impl-initst x)
                     (base-fsm-eval spec-envs spec-initst x)
                     (:free (spec-outs)
                      (overridekeys-envlists-ok params overridekeys impl-envs spec-envs spec-outs)))
            :induct (ind x impl-envs impl-initst spec-envs spec-initst))))

  (defthm fsm-final-state-when-overridekeys-envlists-ok
    (b* ((impl-final (base-fsm-final-state impl-envs impl-initst (base-fsm->nextstate x)))
         (spec-final (base-fsm-final-state spec-envs spec-initst (base-fsm->nextstate x)))
         (spec-outs (base-fsm-eval spec-envs spec-initst x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
                    (base-fsm-partial-monotonic params x)
                    (overridekeys-envlists-ok params overridekeys impl-envs spec-envs spec-outs)
                    (not (intersectp-equal (svarlist-fix params)
                                           (svarlist-change-override overridekeys :val)))
                    (svex-env-<<= impl-initst spec-initst)
                    (not (intersectp-equal (svarlist-fix params)
                                           (svex-alist-keys (base-fsm->nextstate x))))
                    (svarlist-override-p (svex-alist-keys (base-fsm->nextstate x)) nil)
                    (equal (len impl-envs) (len spec-envs)))
               (svex-env-<<= impl-final spec-final)))
    :hints(("Goal" :in-theory (enable base-fsm-overridekey-transparent-p
                                      base-fsm-partial-monotonic
                                      svex-envlist-<<=
                                      base-fsm-step
                                      base-fsm-step-outs
                                      base-fsm-step-env)
            :expand ((base-fsm-eval spec-envs spec-initst x)
                     (:free (x) (base-fsm-final-state spec-envs spec-initst x))
                     (:free (x) (base-fsm-final-state impl-envs impl-initst x))
                     (:free (spec-outs)
                      (overridekeys-envlists-ok params overridekeys impl-envs spec-envs spec-outs)))
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
                    (base-fsm-partial-monotonic params x)
                    (base-fsm-partial-monotonic params x-approx)
                    (overridekeys-envlists-ok params overridekeys impl-envs spec-envs spec-outs)
                    (not (intersectp-equal (svarlist-fix params)
                                           (svarlist-change-override overridekeys :val)))
                    (svex-env-<<= impl-initst spec-initst)
                    (not (intersectp-equal (svarlist-fix params)
                                           (svex-alist-keys (base-fsm->nextstate x))))
                    (svarlist-override-p (svex-alist-keys (base-fsm->nextstate x)) nil)
                    (base-fsm-<<= x-approx x)
                    (equal (svex-alist-keys (base-fsm->nextstate x-approx))
                           (svex-alist-keys (base-fsm->nextstate x))))
               (svex-envlist-<<= impl-outs spec-outs)))
    :hints (("goal" :use ((:instance fsm-eval-when-base-fsm-<<=-and-partial-monotonic
                           (x x-approx) (y x)
                           (x-initst impl-initst) (y-initst impl-initst)
                           (ins impl-envs)))
             :in-theory (e/d () (fsm-eval-when-base-fsm-<<=-and-partial-monotonic)))))

  (defthm fsm-final-state-with-conservative-fsm-when-overridekeys-envlists-ok
    (b* ((impl-final (base-fsm-final-state impl-envs impl-initst (base-fsm->nextstate x-approx)))
         (spec-final (base-fsm-final-state spec-envs spec-initst (base-fsm->nextstate x)))
         (spec-outs (base-fsm-eval spec-envs spec-initst x)))
      (implies (and (base-fsm-overridekey-transparent-p x overridekeys)
                    (base-fsm-partial-monotonic params x)
                    (base-fsm-partial-monotonic params x-approx)
                    (overridekeys-envlists-ok params overridekeys impl-envs spec-envs spec-outs)
                    (not (intersectp-equal (svarlist-fix params)
                                           (svarlist-change-override overridekeys :val)))
                    (svex-env-<<= impl-initst spec-initst)
                    (not (intersectp-equal (svarlist-fix params)
                                           (svex-alist-keys (base-fsm->nextstate x))))
                    (svarlist-override-p (svex-alist-keys (base-fsm->nextstate x)) nil)
                    (equal (len impl-envs) (len spec-envs))
                    (base-fsm-<<= x-approx x)
                    (equal (svex-alist-keys (base-fsm->nextstate x-approx))
                           (svex-alist-keys (base-fsm->nextstate x))))
               (svex-env-<<= impl-final spec-final)))
    :hints (("goal" :use ((:instance fsm-final-state-when-<<=-and-partial-monotonic
                           (x (base-fsm->nextstate x-approx))
                           (y (base-fsm->nextstate x))
                           (x-initst impl-initst) (y-initst impl-initst)
                           (ins impl-envs)))
             :in-theory (e/d (svex-env-<<=-transitive-1
                              svex-env-<<=-transitive-2)
                             (fsm-final-state-when-<<=-and-partial-monotonic)))
            (and stable-under-simplificationp
                 '(:in-theory (enable base-fsm-<<=
                                      base-fsm-partial-monotonic))))))


(define base-fsm-ovcongruent ((x base-fsm-p))
  (b* (((base-fsm x)))
    (and (ec-call (svex-alist-ovcongruent x.values))
         (ec-call (svex-alist-ovcongruent x.nextstate)))))

(define overridekeys-envlists-agree* ((overridekeys svarlist-p)
                                      (impl-envs svex-envlist-p)
                                      (spec-envs svex-envlist-p)
                                      (spec-outs svex-envlist-p))
  :guard (eql (len spec-envs) (len spec-outs))
  :returns (ok)
  :measure (len spec-envs)
  (if (atom spec-envs)
      (atom impl-envs)
    (and (consp impl-envs)
         (overridekeys-envs-agree* overridekeys (car impl-envs) (car spec-envs) (car spec-outs))
         (overridekeys-envlists-agree* overridekeys (cdr impl-envs) (cdr spec-envs) (cdr spec-outs))))
  ///
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
  


