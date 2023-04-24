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

(include-book "fixpoint-eval")
(include-book "override-transparency")
(local (include-book "alist-thms"))
(local (include-book "std/alists/fast-alist-clean" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "std/basic/inductions" :dir :system))
(local (std::add-default-post-define-hook :fix))

;; We want to show that if we insert override muxes in a network and evaluate its
;; fixpoint under an env for which for every override test variable, the corresponding
;; override value variable matches the override-free fixpoint on the bits that
;; the override test is 1, THEN the evaluation of that fixpoint matches the
;; evaluation of the original, override-free fixpoint.

;; The argument for this is basically when computing the fixpoint iteration of
;; the override network, it is always <<= the final fixpoint of the original
;; network, but it is always >>= the corresponding fixpoint iteration of the
;; original network.  Conveniently for this proof, the bit width of each
;; expression is preserved by applying the overrides, so that means the
;; iteration takes the same number of steps.  This shows that the fixpoint
;; evaluation with overrides is bounded above and below by the original
;; fixpoint evaluation, so they are equivalent.





(local (defun count-down (n)
         (if (zp n)
             n
           (count-down (1- n)))))


(defthm svex-alist-eval-fixpoint-step-stays-below-fixpoint
  (implies (and (svex-alist-width x)
                (svex-alist-monotonic-on-vars (svex-alist-keys x) x)
                (no-duplicatesp-equal (svex-alist-keys x))
                (svex-env-<<= env (svex-alist-eval-least-fixpoint x in-env)))
           (svex-env-<<= (svex-alist-eval-fixpoint-step x env in-env)
                         (svex-alist-eval-least-fixpoint x in-env)))
  :hints (("goal" :use ((:instance svex-alist-eval-fixpoint-step-monotonic
                         (env1 env)
                         (env2 (svex-alist-eval-least-fixpoint x in-env))))
           :in-theory (disable svex-alist-eval-fixpoint-step-monotonic))))


(local (defthm alist-keys-of-append
         (equal (alist-keys (append x y))
                (append (alist-keys x) (alist-keys y)))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(local
 (defthm svex-env-extract-of-append-subset
   (implies (subsetp-equal (alist-keys (svex-env-fix subst)) (svarlist-fix keys))
            (svex-envs-equivalent (svex-env-extract keys (append subst rest))
                                  (append subst (svex-env-extract keys rest))))
   :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                     svex-env-boundp-iff-member-alist-keys)
           :do-not-induct t))))

(local
 (defthm svex-alist-eval-fixpoint-step-of-compose
   (implies (subsetp-equal (svex-alist-keys subst) (svex-alist-keys network))
            (equal (svex-alist-eval-fixpoint-step (svex-alist-compose network subst) env in-env)
                   (svex-alist-eval-fixpoint-step network
                                                  (append
                                                   (svex-alist-eval subst
                                                                    (append (svex-env-extract (svex-alist-keys network) env)
                                                                            in-env))
                                                   env)
                                                  in-env)))
   :hints(("Goal" :in-theory (enable svex-alist-eval-fixpoint-step)))))

(local
 (encapsulate nil
   (local (defthm equal-svex-env-lookup-when-agree-except
            (implies (and (svex-envs-agree-except irrel-vars in-env1 in-env2)
                          (not (member-equal (svar-fix v) (svarlist-fix irrel-vars))))
                     (equal (svex-env-lookup v in-env1)
                            (svex-env-lookup v in-env2)))
            :hints(("Goal" :in-theory (enable svex-envs-agree-except)))))
   (local (defthm svex-env-extract-when-agree-except-append
            (implies (and (svex-envs-agree-except irrel-vars in-env1 in-env2)
                          (not (intersectp-equal (svarlist-fix irrel-vars) (svarlist-fix extract-vars))))
                     (svex-envs-similar (svex-env-extract extract-vars (append env in-env1))
                                        (svex-env-extract extract-vars (append env in-env2))))
            :hints (("goal" :in-theory (enable svex-envs-similar)))))
   (defthm svex-alist-eval-fixpoint-step-when-svex-envs-agree-except
     (implies (and (svex-envs-agree-except irrel-vars in-env1 in-env2)
                   (not (intersectp-equal (svarlist-fix irrel-vars) (svex-alist-vars network))))
              (equal (svex-alist-eval-fixpoint-step network env in-env1)
                     (svex-alist-eval-fixpoint-step network env in-env2)))
     :hints(("Goal" :in-theory (enable svex-alist-eval-fixpoint-step
                                       svex-alist-eval-equal-when-extract-vars-similar))))))


;; ;; ;; (local
;; ;; ;;  (encapsulate nil
;; ;; ;;    (local (defthm svex-env-<<=-of-append-lemma
;; ;; ;;             (implies (and (svex-env-<<= x z)
;; ;; ;;                           (svex-env-<<= y z))
;; ;; ;;                      (svex-env-<<= (append x y) z))
;; ;; ;;             :hints (("goal" :expand ((svex-env-<<= (append x y) z))))))
   
;; ;; ;;    (defthm override-compose-<<=-fixpoint
;; ;; ;;      (implies (and (svex-env-<<= prev fixpoint)
;; ;; ;;                    (equal (alist-keys (svex-env-fix prev)) (alist-keys (svex-env-fix fixpoint)))
;; ;; ;;                    (svar-override-triplelist-env-ok triples override-env fixpoint)
;; ;; ;;                    (subsetp-equal (svar-override-triplelist->refvars triples) (alist-keys (svex-env-fix prev)))
;; ;; ;;                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (alist-keys (svex-env-fix prev)))))
;; ;; ;;               (svex-env-<<= (append (svex-alist-eval (svar-override-triplelist->override-alist triples)
;; ;; ;;                                                      (append prev override-env))
;; ;; ;;                                     prev)
;; ;; ;;                             fixpoint))
;; ;; ;;      :hints(("goal" :do-not-induct t
;; ;; ;;              :in-theory (enable svex-apply svex-eval))))))

;; ;; ;; (local
;; ;; ;;  (defthm svex-alist-eval-fixpoint-of-overrides
;; ;; ;;    (b* ((fixpoint (svex-alist-eval-least-fixpoint network ref-env))
;; ;; ;;         (override-network (svex-alist-compose network (svar-override-triplelist->override-alist triples)))
;; ;; ;;         (override-fixpoint (svex-alist-eval-fixpoint-iterate n override-network
;; ;; ;;                                                              (svarlist-x-env (svex-alist-keys network))
;; ;; ;;                                                              override-env)))
;; ;; ;;      (implies (and (svex-alist-width network)
;; ;; ;;                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
;; ;; ;;                    (no-duplicatesp-equal (svex-alist-keys network))
;; ;; ;;                    (svar-override-triplelist-env-ok triples override-env fixpoint)
;; ;; ;;                    (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
;; ;; ;;                                            override-env ref-env)
;; ;; ;;                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys network)))
;; ;; ;;                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars network)))
;; ;; ;;                    (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys network)))
;; ;; ;;               (svex-env-<<= override-fixpoint fixpoint)))
;; ;; ;;    :hints (("goal" :induct (count-down n)
;; ;; ;;             :expand ((:free (network env) (svex-alist-eval-fixpoint-iterate n network env override-env))
;; ;; ;;                      (:free (network env) (svex-alist-eval-fixpoint-iterate 0 network env override-env)))))))




(local (defthm member-svar-override-triplelist->testvars-when-testvar-of-lookup-refvar
         (implies (member-equal (svar-fix v) (svar-override-triplelist->refvars triples))
                  (member-equal (svar-override-triple->testvar
                                 (svar-override-triplelist-lookup-refvar v triples))
                                (svar-override-triplelist->testvars triples)))
         :hints(("Goal" :in-theory (enable svar-override-triplelist->testvars
                                           svar-override-triplelist-lookup-refvar
                                           svar-override-triplelist->refvars)))))

(local (defthm member-svar-override-triplelist->valvars-when-valvar-of-lookup-refvar
         (implies (member-equal (svar-fix v) (svar-override-triplelist->refvars triples))
                  (member-equal (svar-override-triple->valvar
                                 (svar-override-triplelist-lookup-refvar v triples))
                                (svar-override-triplelist->valvars triples)))
         :hints(("Goal" :in-theory (enable svar-override-triplelist->valvars
                                           svar-override-triplelist-lookup-refvar
                                           svar-override-triplelist->refvars)))))


(defsection svex-alist-vars-of-fast-alist-clean
  (defthm member-svex-alist-vars-of-fast-alist-fork
    (implies (and (not (member-equal v (svex-alist-vars y)))
                  (not (member-equal v (svex-alist-vars x))))
             (not (member-equal v (svex-alist-vars (fast-alist-fork x y)))))
    :hints(("Goal" :in-theory (enable svex-alist-vars))))

  (defthm member-svex-alist-vars-of-fast-alist-clean
    (implies (not (member-equal v (svex-alist-vars x)))
             (not (member-equal v (svex-alist-vars (fast-alist-clean x)))))
    :hints(("Goal" :in-theory (enable svex-alist-vars fast-alist-clean))))

  (defthm subsetp-svex-alist-vars-of-fast-alist-clean
    (subsetp (svex-alist-vars (fast-alist-clean x))
             (svex-alist-vars x))
    :hints(("Goal" :in-theory (e/d (acl2::subsetp-witness-rw) (fast-alist-clean))))))

(defsection fast-alist-clean-of-svex-alist-fix
  (defthm fast-alist-fork-of-svex-alist-fix
    (equal (fast-alist-fork (svex-alist-fix x) (svex-alist-fix y))
           (svex-alist-fix (fast-alist-fork x y)))
    :hints(("Goal" :in-theory (enable svex-alist-fix))))

  (local (defthm cdr-last-of-svex-alist-fix
           (equal (cdr (last (svex-alist-fix x))) nil)
           :hints(("Goal" :in-theory (enable svex-alist-fix)))))
  
  (defthm fast-alist-clean-of-svex-alist-fix
    (equal (fast-alist-clean (svex-alist-fix x))
           (svex-alist-fix (fast-alist-clean x)))
    :hints (("goal" :use ((:instance fast-alist-fork-of-svex-alist-fix
                           (y (cdr (last x))))
                          (:instance fast-alist-fork-of-svex-alist-fix
                           (y nil)))
             :in-theory (e/d (svex-alist-fix)
                             (fast-alist-fork-of-svex-alist-fix))
             :do-not-induct t))))




(defsection svex-width-of-svex-compose-override-alist

  ;; (local (defthm eval-override-alist-of-cons-irrel
  ;;          (implies (and (not (member-equal (svar-fix v) (svar-override-triplelist->testvars triples)))
  ;;                        (not (member-equal (svar-fix v) (svar-override-triplelist->valvars triples)))
  ;;                        (not (member-equal (svar-fix v) (svar-override-triplelist->refvars triples))))
  ;;                   (equal (svex-alist-eval (svar-override-triplelist->override-alist triples)
  ;;                                           (cons (cons v val) rest))
  ;;                          (svex-alist-eval (svar-override-triplelist->override-alist triples)
  ;;                                           rest)))
  ;;          :hints(("Goal" :in-theory (enable svar-override-triplelist->override-alist
  ;;                                            svar-override-triplelist->testvars
  ;;                                            svar-override-triplelist->refvars
  ;;                                            svex-alist-eval svex-apply svex-eval
  ;;                                            svex-env-lookup-of-cons-split)))))

  (local (defthm eval-override-alist-when-testvars-x
           (implies (and (not (intersectp-equal (svar-override-triplelist->refvars triples)
                                                (svar-override-triplelist->testvars triples)))
                         ;; (not (intersectp-equal (svar-override-triplelist->valvars triples)
                         ;;                        (svar-override-triplelist->testvars triples)))
                         ;; (no-duplicatesp-equal (svar-override-triplelist->testvars triples))
                         )
                    (svex-envs-equivalent (svex-alist-eval (svar-override-triplelist->override-alist triples)
                                                           (append (svarlist-x-env (svar-override-triplelist->testvars triples))
                                                                   env))
                                          (svex-env-extract (svar-override-triplelist->refvars triples) env)))
           :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                             svex-apply svex-eval)))))

  (local (defthm svex-eval-lemma-for-svex-width-limited-p-of-svex-compose-override-alist-when-not
           (implies (and (not (intersectp-equal (svex-vars x) (svarlist-fix testvars))))
                    (equal (svex-eval x (append (svex-env-extract refvars env)
                                                (svarlist-x-env testvars)
                                                env))
                           (svex-eval x env)))
           :hints(("Goal" :in-theory (enable svex-eval-equal-when-extract-vars-similar
                                             svex-envs-similar)))))
  
  
  (local
   (defthm svex-width-limited-p-of-svex-compose-override-alist-when-limited
     (implies (svex-width-limited-p width x)
              (svex-width-limited-p width (svex-compose x (svar-override-triplelist->override-alist triples))))
     :hints(("Goal" :expand ((svex-width-limited-p width (svex-compose x (svar-override-triplelist->override-alist triples))))
             :use ((:instance svex-width-limited-p-necc
                    (x x)
                    (env (let ((env1 (svex-width-limited-p-witness width (svex-compose x (svar-override-triplelist->override-alist triples)))))
                           (append (svex-alist-eval
                                    (svar-override-triplelist->override-alist triples) env1)
                                   env1)))))))))

  (local
   (defthm svex-width-limited-p-of-svex-compose-override-alist-when-not
     (implies (and (not (svex-width-limited-p width x))
                   (not (intersectp-equal (svex-vars x) (svar-override-triplelist->testvars triples)))
                   (not (intersectp-equal (svar-override-triplelist->refvars triples)
                                          (svar-override-triplelist->testvars triples))))
              (not (svex-width-limited-p width (svex-compose x (svar-override-triplelist->override-alist triples)))))
     :hints(("Goal" :expand ((svex-width-limited-p width x))
             :use ((:instance svex-width-limited-p-necc
                    (x (svex-compose x (svar-override-triplelist->override-alist triples)))
                    (env (append (svarlist-x-env (svar-override-triplelist->testvars triples))
                                 (svex-width-limited-p-witness width x)))))))))

  (defthm svex-width-limited-p-of-svex-compose-override-alist
    (implies (and (not (intersectp-equal (svex-vars x) (svar-override-triplelist->testvars triples)))
                  (not (intersectp-equal (svar-override-triplelist->refvars triples)
                                         (svar-override-triplelist->testvars triples))))
             (iff (svex-width-limited-p width (svex-compose x (svar-override-triplelist->override-alist triples)))
                  (svex-width-limited-p width x))))

  (defthm svex-width-lower-boundp-of-svex-compose-override-alist
    (implies (and (not (intersectp-equal (svex-vars x) (svar-override-triplelist->testvars triples)))
                  (not (intersectp-equal (svar-override-triplelist->refvars triples)
                                         (svar-override-triplelist->testvars triples))))
             (iff (svex-width-lower-boundp width (svex-compose x (svar-override-triplelist->override-alist triples)))
                  (svex-width-lower-boundp width x)))
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'svex-width-lower-boundp clause))
                      (witness `(svex-width-lower-boundp-witness . ,(cdr lit)))
                      (other (if (eq (caddr lit) 'x)
                                 '(svex-compose x (svar-override-triplelist->override-alist triples))
                               'x)))
                   `(:expand (,lit)
                     :use ((:instance svex-width-lower-boundp-necc
                            (x ,other)
                            (width2 ,witness))))))))
  
  (defthm svex-width-of-svex-compose-override-alist
    (implies (and (not (intersectp-equal (svex-vars x) (svar-override-triplelist->testvars triples)))
                  (not (intersectp-equal (svar-override-triplelist->refvars triples)
                                         (svar-override-triplelist->testvars triples))))
             (equal (svex-width (svex-compose x (svar-override-triplelist->override-alist triples)))
                    (svex-width x)))
    :hints (("Goal" :use ((:instance not-limited-p-when-not-svex-width
                           (x x) (width (svex-width (svex-compose x (svar-override-triplelist->override-alist triples)))))
                          (:instance not-limited-p-when-not-svex-width
                           (x (svex-compose x (svar-override-triplelist->override-alist triples))) (width (svex-width x)))
                          (:instance svex-width-when-limited
                           (x x))
                          (:instance svex-width-when-limited
                           (x (svex-compose x (svar-override-triplelist->override-alist triples)))))
             :in-theory (e/d (svex-width-unique)
                             (svex-width-when-limited
                              not-limited-p-when-not-svex-width)))))

  (local (in-theory (disable fast-alist-clean)))
  
  (defthm svex-alist-width-aux-of-svex-alist-compose-override-alist
    (implies (and (not (intersectp-equal (svex-alist-vars x) (svar-override-triplelist->testvars triples)))
                  (not (intersectp-equal (svar-override-triplelist->refvars triples)
                                         (svar-override-triplelist->testvars triples))))
             (equal (svex-alist-width-aux (svex-alist-compose x (svar-override-triplelist->override-alist triples)))
                    (svex-alist-width-aux x)))
    :hints(("Goal" :in-theory (enable svex-alist-width-aux
                                      svex-alist-vars
                                      svex-alist-compose svex-acons))))

  (local (defun fast-alist-fork-of-svex-alist-compose-ind (x y)
           (if (atom x)
               y
             (if (and (consp (car x))
                      (not (hons-assoc-equal (caar x) y)))
                 (fast-alist-fork-of-svex-alist-compose-ind (cdr x) (cons (car x) y))
               (fast-alist-fork-of-svex-alist-compose-ind (cdr x) y)))))

  (local (defthm hons-assoc-equal-of-svex-alist-compose
           (iff (hons-assoc-equal k (svex-alist-compose x y))
                (and (svar-p k)
                     (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable svex-alist-compose svex-acons)))))
  
  (local (defthm fast-alist-fork-of-svex-alist-compose
           (equal (fast-alist-fork (svex-alist-compose x z) (svex-alist-compose y z))
                  (svex-alist-compose (fast-alist-fork x y) z))
           :hints(("Goal" :in-theory (enable svex-alist-compose svex-acons)
                   :induct (fast-alist-fork-of-svex-alist-compose-ind x y)
                   :expand ((fast-alist-fork x y))))))

  (local (defthm cdr-last-of-svex-alist-compose
           (equal (cdr (last (svex-alist-compose x y))) nil)
           :hints(("Goal" :in-theory (enable svex-alist-compose svex-acons)))))

  (local (defthm svex-alist-compose-of-cdr-last
           (equal (svex-alist-compose (cdr (last x)) y) nil)
           :hints(("Goal" :in-theory (enable svex-alist-compose svex-acons)))))
  
  (local (defthm fast-alist-clean-of-svex-alist-compose
           (equal (fast-alist-clean (svex-alist-compose x y))
                  (svex-alist-compose (fast-alist-clean x) y))
           :hints (("Goal" :in-theory (e/d (fast-alist-clean)
                                           (fast-alist-fork-of-svex-alist-compose))
                    :use ((:instance fast-alist-fork-of-svex-alist-compose
                           (y (cdr (last x))) (z y))))
                   (and stable-under-simplificationp
                        '(:expand ((svex-alist-compose nil y)
                                   (svex-alist-compose x y)))))))

  (local (defthm intersectp-when-subsetp
           (implies (and (not (intersectp-equal x y))
                         (subsetp-equal z x))
                    (not (intersectp-equal z y)))
           :hints(("Goal" :in-theory (enable subsetp-equal intersectp-equal)))))
  
  (defthm svex-alist-width-of-svex-alist-compose-override-alist
    (implies (and (not (intersectp-equal (svex-alist-vars x) (svar-override-triplelist->testvars triples)))
                  (not (intersectp-equal (svar-override-triplelist->refvars triples)
                                         (svar-override-triplelist->testvars triples))))
             (equal (svex-alist-width (svex-alist-compose x (svar-override-triplelist->override-alist triples)))
                    (svex-alist-width x)))
    :hints(("Goal" :in-theory (e/d (svex-alist-width)
                                   (acl2::intersectp-equal-commute))))))


(local (defthm not-intersectp-testvars/refvars-when-not-intersectp-and-subsetp
         (implies (And (subsetp-equal refvars keys)
                       (not (intersectp-equal testvars keys)))
                  (not (intersectp-equal refvars testvars)))
         :hints(("Goal" :in-theory (enable intersectp-equal subsetp-equal)))))


(local (defthm not-intersectp-testvars-when-not-intersectp-override-vars
         (implies (not (intersectp-equal (svar-override-triplelist-override-vars x) y))
                  (not (intersectp-equal (svar-override-triplelist->testvars x) y)))
         :hints (("goal" :use svar-override-triplelist->testvars-subset-of-override-vars
                  :in-theory (disable svar-override-triplelist->testvars-subset-of-override-vars)))))

;; ;; ;; (local
;; ;; ;;  (defthm svex-alist-eval-least-fixpoint-of-overrides
;; ;; ;;    (b* ((fixpoint (svex-alist-eval-least-fixpoint network ref-env))
;; ;; ;;         (override-network (svex-alist-compose network (svar-override-triplelist->override-alist triples)))
;; ;; ;;         (override-fixpoint (svex-alist-eval-least-fixpoint override-network override-env)))
;; ;; ;;      (implies (and (svex-alist-width network)
;; ;; ;;                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
;; ;; ;;                    (no-duplicatesp-equal (svex-alist-keys network))
;; ;; ;;                    (svar-override-triplelist-env-ok triples override-env fixpoint)
;; ;; ;;                    (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
;; ;; ;;                                            override-env ref-env)
;; ;; ;;                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys network)))
;; ;; ;;                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars network)))
;; ;; ;;                    (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys network)))
;; ;; ;;               (svex-env-<<= override-fixpoint fixpoint)))
;; ;; ;;    :hints (("goal" :use ((:instance svex-alist-eval-fixpoint-of-overrides
;; ;; ;;                           (n (svex-alist-width network))))
;; ;; ;;             :in-theory (e/d (svex-alist-eval-least-fixpoint)
;; ;; ;;                             (svex-alist-eval-fixpoint-of-overrides))))))

;; ;; ;; (local
;; ;; ;;  (encapsulate nil
;; ;; ;;    (local (defthm svex-env-<<=-of-append-lemma2
;; ;; ;;             (implies (and (svex-env-<<= (svex-env-extract (alist-keys (svex-env-fix x)) z) x)
;; ;; ;;                           (svex-env-<<= z y))
;; ;; ;;                      (svex-env-<<= z (append x y)))
;; ;; ;;             :hints (("goal" :expand ((svex-env-<<= z (append x y)))
;; ;; ;;                      :use ((:instance svex-env-<<=-necc
;; ;; ;;                             (x (svex-env-extract (alist-keys (svex-env-fix x)) z))
;; ;; ;;                             (y x)
;; ;; ;;                             (var (svex-env-<<=-witness z (append x y)))))
;; ;; ;;                      :in-theory (enable svex-env-boundp-iff-member-alist-keys)
;; ;; ;;                      :do-not-induct t))))


;; ;; ;;    (local (Defthm 4vec-bit?!-branches-same
;; ;; ;;             (equal (4vec-bit?! test x x)
;; ;; ;;                    (4vec-fix x))
;; ;; ;;             :hints(("Goal" :in-theory (enable 4vec-bit?!))
;; ;; ;;                    (bitops::logbitp-reasoning))))

;; ;; ;;    (local (defthm 4vec-bit?!->>=-x
;; ;; ;;             (implies (and (4vec-<<= x then)
;; ;; ;;                           (4vec-<<= x else))
;; ;; ;;                      (4vec-<<= x (4vec-bit?! test then else)))
;; ;; ;;             :hints (("goal" :use ((:instance 4vec-bit?!-monotonic-on-nontest-args
;; ;; ;;                                    (then1 x) (then2 then) (else1 x) (else2 else)))
;; ;; ;;                      :in-theory (disable 4vec-bit?!-monotonic-on-nontest-args)))))
   
;; ;; ;;    (local (defthm 4vec-bit?!->>=-x-combo
;; ;; ;;             (implies (and (equal (4vec-bit?! test then1 something)
;; ;; ;;                                  (4vec-bit?! test then2 something))
;; ;; ;;                           (4vec-<<= x then2)
;; ;; ;;                           (4vec-<<= x else))
;; ;; ;;                      (4vec-<<= x (4vec-bit?! test then1 else)))
;; ;; ;;             :hints (("goal" :use ((:instance 4vec-bit?!->>=-x
;; ;; ;;                                    (then then2))
;; ;; ;;                                   (:instance equal-of-4vec-bit?!-by-example
;; ;; ;;                                    (else1 something)
;; ;; ;;                                    (else2 else)))
;; ;; ;;                      :in-theory (disable 4vec-bit?!->>=-x
;; ;; ;;                                          equal-of-4vec-bit?!-by-example)))))
   
   
;; ;; ;;    (local (defthm override-alist-lookup->>=-ref-when-env-ok
;; ;; ;;             (implies (and (svar-override-triplelist-env-ok triples override-env fixpoint)
;; ;; ;;                           (svex-env-<<= prev-ref fixpoint)
;; ;; ;;                           (svex-env-<<= prev-ref prev-ovr)
;; ;; ;;                           (equal (alist-keys (svex-env-fix prev-ref)) (alist-keys (svex-env-fix prev-ovr)))
;; ;; ;;                           (not (intersectp-equal (svar-override-triplelist-override-vars triples)
;; ;; ;;                                                  (alist-keys (svex-env-fix prev-ref))))
;; ;; ;;                           (subsetp-equal (svar-override-triplelist->refvars triples) (alist-keys (svex-env-fix prev-ref)))
;; ;; ;;                           (member-equal (svar-fix v) (svar-override-triplelist->refvars triples)))
;; ;; ;;                      (4vec-<<= (svex-env-lookup v prev-ref)
;; ;; ;;                                (svex-eval (svex-lookup v (svar-override-triplelist->override-alist triples))
;; ;; ;;                                           (append prev-ovr override-env))))
;; ;; ;;             :hints (("goal" :in-theory (e/d (svar-override-triplelist->override-alist
;; ;; ;;                                              svar-override-triplelist-env-ok
;; ;; ;;                                              svar-override-triplelist->refvars
;; ;; ;;                                              svar-override-triplelist-override-vars
;; ;; ;;                                              svex-eval svex-apply svex-lookup-redef
;; ;; ;;                                              svex-env-boundp-iff-member-alist-keys)
;; ;; ;;                                             (lookup-of-svar-override-triplelist->override-alist))))))

;; ;; ;;    (local (defthm lookup-of-svar-override-triplelist->override-alist-under-iff
;; ;; ;;             (iff (svex-lookup v (svar-override-triplelist->override-alist triples))
;; ;; ;;                  (member-equal (svar-fix v) (svar-override-triplelist->refvars triples)))
;; ;; ;;             :hints(("Goal" :in-theory (enable svar-override-triplelist->refvars
;; ;; ;;                                               svar-override-triplelist->override-alist)))))
   
;; ;; ;;    (local (defthm override-compose->>=-base-compose-lemma
;; ;; ;;             (implies (and (svar-override-triplelist-env-ok triples override-env fixpoint)
;; ;; ;;                           (svex-env-<<= prev-ref prev-ovr)
;; ;; ;;                           (svex-env-<<= prev-ref fixpoint)
;; ;; ;;                           (equal (alist-keys (svex-env-fix prev-ref)) (alist-keys (svex-env-fix prev-ovr)))
;; ;; ;;                           (not (intersectp-equal (svar-override-triplelist-override-vars triples)
;; ;; ;;                                                  (alist-keys (svex-env-fix prev-ref))))
;; ;; ;;                           (subsetp-equal (svar-override-triplelist->refvars triples) (alist-keys (svex-env-fix prev-ref))))
;; ;; ;;                      (svex-env-<<= (svex-env-extract (svar-override-triplelist->refvars triples) prev-ref)
;; ;; ;;                                    (svex-alist-eval (svar-override-triplelist->override-alist triples)
;; ;; ;;                                                     (append prev-ovr override-env))))
;; ;; ;;             :hints(("goal" :do-not-induct t
;; ;; ;;                     :in-theory (e/d (svex-apply
;; ;; ;;                                        svex-eval
;; ;; ;;                                        svex-env-boundp-iff-member-alist-keys)
;; ;; ;;                                     (acl2::intersectp-equal-append2
;; ;; ;;                                      LOOKUP-OF-SVAR-OVERRIDE-TRIPLELIST->OVERRIDE-ALIST)))
;; ;; ;;                    (and stable-under-simplificationp
;; ;; ;;                         (b* ((lit (car (last clause))))
;; ;; ;;                           `(:expand (,lit)))))))
                          
   
;; ;; ;;    (defthm override-compose->>=-base-compose
;; ;; ;;      (implies (and (svar-override-triplelist-env-ok triples override-env fixpoint)
;; ;; ;;                    (svex-env-<<= prev-ref prev-ovr)
;; ;; ;;                    (svex-env-<<= prev-ref fixpoint)
;; ;; ;;                    (equal (alist-keys (svex-env-fix prev-ref)) (alist-keys (svex-env-fix prev-ovr)))
;; ;; ;;                    (not (intersectp-equal (svar-override-triplelist-override-vars triples)
;; ;; ;;                                           (alist-keys (svex-env-fix prev-ovr))))
;; ;; ;;                    (subsetp-equal (svar-override-triplelist->refvars triples) (alist-keys (svex-env-fix prev-ovr))))
;; ;; ;;               (svex-env-<<= prev-ref
;; ;; ;;                             (append (svex-alist-eval (svar-override-triplelist->override-alist triples)
;; ;; ;;                                                      (append prev-ovr override-env))
;; ;; ;;                                     prev-ovr)))
;; ;; ;;      :hints(("goal" :do-not-induct t
;; ;; ;;              :in-theory (enable svex-apply svex-eval))))))


(local
 (defthm svex-alist-eval-fixpoint-iterate-<<=-least-fixpoint
   (implies (and (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                 (no-duplicatesp-equal (svex-alist-keys network))
                 (svex-alist-width network))
            (SVEX-ENV-<<=
             (SVEX-ALIST-EVAL-FIXPOINT-ITERATE n
                                               NETWORK
                                               (SVARLIST-X-ENV (SVEX-ALIST-KEYS NETWORK))
                                               REF-ENV)
             (SVEX-ALIST-EVAL-LEAST-FIXPOINT NETWORK REF-ENV)))))


;; ;; ;; (local
;; ;; ;;  (defthm svex-alist-eval-override-fixpoint-iterate->>=
;; ;; ;;    (b* ((override-network (svex-alist-compose network (svar-override-triplelist->override-alist triples)))
;; ;; ;;         (override-fixpoint (svex-alist-eval-fixpoint-iterate n override-network
;; ;; ;;                                                              (svarlist-x-env (svex-alist-keys network))
;; ;; ;;                                                              override-env))
;; ;; ;;         (fixpoint-iter (svex-alist-eval-fixpoint-iterate n network
;; ;; ;;                                                          (svarlist-x-env (svex-alist-keys network))
;; ;; ;;                                                          ref-env))
;; ;; ;;         (fixpoint (svex-alist-eval-least-fixpoint network ref-env)))
;; ;; ;;      (implies (and (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
;; ;; ;;                                            override-env ref-env)
;; ;; ;;                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
;; ;; ;;                    (no-duplicatesp-equal (svex-alist-keys network))
;; ;; ;;                    (svex-alist-width network)
;; ;; ;;                    (svar-override-triplelist-env-ok triples override-env fixpoint)
;; ;; ;;                    (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys network))
;; ;; ;;                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys network)))
;; ;; ;;                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars network))))
;; ;; ;;               (svex-env-<<= fixpoint-iter override-fixpoint)))
;; ;; ;;    :hints (("goal" :induct (count-down n)
;; ;; ;;             :expand ((:free (network env in-env) (svex-alist-eval-fixpoint-iterate n network env in-env))
;; ;; ;;                      (:free (network env in-env) (svex-alist-eval-fixpoint-iterate 0 network env in-env)))))))


;; ;; ;; (local
;; ;; ;;  (defthm svex-alist-eval-override-fixpoint->>=-ref-fixpoint
;; ;; ;;    (b* ((override-network (svex-alist-compose network (svar-override-triplelist->override-alist triples)))
;; ;; ;;         (override-fixpoint (svex-alist-eval-least-fixpoint override-network override-env))
;; ;; ;;         (fixpoint (svex-alist-eval-least-fixpoint network ref-env)))
;; ;; ;;      (implies (and (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
;; ;; ;;                                            override-env ref-env)
;; ;; ;;                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
;; ;; ;;                    (no-duplicatesp-equal (svex-alist-keys network))
;; ;; ;;                    (svex-alist-width network)
;; ;; ;;                    (svar-override-triplelist-env-ok triples override-env fixpoint)
;; ;; ;;                    (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys network))
;; ;; ;;                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys network)))
;; ;; ;;                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars network))))
;; ;; ;;               (svex-env-<<= fixpoint override-fixpoint)))
;; ;; ;;    :hints (("goal" :use ((:instance svex-alist-eval-override-fixpoint-iterate->>=
;; ;; ;;                           (n (svex-alist-width network))))
;; ;; ;;             :in-theory (enable svex-alist-eval-least-fixpoint)))))


;; ;; ;; (encapsulate nil
;; ;; ;;   (local (defthmd 4vec-equiv-by-<<=
;; ;; ;;            (implies (and (4vec-<<= x y)
;; ;; ;;                          (4vec-<<= y x))
;; ;; ;;                     (4vec-equiv x y))
;; ;; ;;            :hints(("Goal" :in-theory (enable 4vec-<<=
;; ;; ;;                                              4vec-fix-is-4vec-of-fields))
;; ;; ;;                   (bitops::logbitp-reasoning))))
  
;; ;; ;;   (local (defthm svex-envs-equivalent-by-<<=
;; ;; ;;            (implies (and (svex-env-<<= x y)
;; ;; ;;                          (svex-env-<<= y x)
;; ;; ;;                          (set-equiv (alist-keys (svex-env-fix x))
;; ;; ;;                                     (alist-keys (svex-env-fix y))))
;; ;; ;;                     (svex-envs-equivalent x y))
;; ;; ;;            :hints(("Goal" :in-theory (enable svex-envs-equivalent
;; ;; ;;                                              svex-env-boundp-iff-member-alist-keys)
;; ;; ;;                    :use ((:instance 4vec-equiv-by-<<=
;; ;; ;;                           (x (svex-env-lookup (svex-envs-equivalent-witness x y) x))
;; ;; ;;                           (y (svex-env-lookup (svex-envs-equivalent-witness x y) y))))))))

;; ;; ;;   (defthm svex-alist-eval-override-fixpoint-equivalent-to-reference-fixpoint
;; ;; ;;     (b* ((override-network (svex-alist-compose network (svar-override-triplelist->override-alist triples)))
;; ;; ;;          (override-fixpoint (svex-alist-eval-least-fixpoint override-network override-env))
;; ;; ;;          (fixpoint (svex-alist-eval-least-fixpoint network ref-env)))
;; ;; ;;       (implies (and (svex-envs-agree-except (svar-override-triplelist-override-vars triples)
;; ;; ;;                                             override-env ref-env)
;; ;; ;;                     (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
;; ;; ;;                     (no-duplicatesp-equal (svex-alist-keys network))
;; ;; ;;                     (svex-alist-width network)
;; ;; ;;                     (svar-override-triplelist-env-ok triples override-env fixpoint)
;; ;; ;;                     (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys network))
;; ;; ;;                     (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys network)))
;; ;; ;;                     (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars network))))
;; ;; ;;                (svex-envs-equivalent override-fixpoint fixpoint)))))






(defthmd svex-alist-eval-fixpoint-step-stays-below-fixpoint-free
  (implies (and (svex-alist-width y)
                (svex-alist-monotonic-on-vars (svex-alist-keys y) y)
                (no-duplicatesp-equal (svex-alist-keys y))
                (svex-env-<<= (svex-alist-eval-fixpoint-step x env in-env)
                              (svex-alist-eval-fixpoint-step
                               y (svex-alist-eval-least-fixpoint y in-env2)
                               in-env2)))
           (svex-env-<<= (svex-alist-eval-fixpoint-step x env in-env)
                         (svex-alist-eval-least-fixpoint y in-env2))))

;; Impl-fixpoint <<= spec-fixpoint: the composition of the override-alist with the override-env is <<= the spec-fixpoint,
;; and composition iterations preserve that <<=.

(defsection svex-alist-eval-fixpoint-override-impl-fixpoint-<<=-spec-fixpoint
  (defthm svex-alist-eval-fixpoint-override-impl-iter-<<=-spec-fixpoint
    (b* ((override-network (svex-alist-compose network (svar-override-triplelist->override-alist triples)))
         (impl-iter (svex-alist-eval-fixpoint-iterate n override-network start-env impl-env))
         (spec-fixpoint (svex-alist-eval-least-fixpoint override-network spec-env)))
      (implies (and (svex-envs-agree-except (svar-override-triplelist-override-vars triples) impl-env spec-env)
                    (svar-override-triplelist-muxes-agree triples impl-env spec-env spec-fixpoint)
                    (svex-env-muxtests-subsetp (svar-override-triplelist->testvars triples) spec-env impl-env)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    (svex-alist-width network)
                    (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys network))
                    (svex-env-<<= start-env spec-fixpoint)
                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys network)))
                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars network)))
                    (equal (alist-keys (svex-env-fix start-env)) (svex-alist-keys network)))
               (svex-env-<<= impl-iter spec-fixpoint)))
    :hints (("goal" :induct (acl2::dec-induct n)
             :expand ((:free (network) (svex-alist-eval-fixpoint-iterate n network start-env impl-env))
                      (:free (network) (svex-alist-eval-fixpoint-iterate 0 network start-env impl-env)))
             :in-theory (e/d (svex-alist-eval-fixpoint-step-stays-below-fixpoint-free)
                             (svex-alist-eval-least-fixpoint-is-fixpoint)))))

  (defthm svex-alist-eval-fixpoint-override-impl-fixpoint-<<=-spec-fixpoint
    (b* ((override-network (svex-alist-compose network (svar-override-triplelist->override-alist triples)))
         (impl-fixpoint (svex-alist-eval-least-fixpoint override-network impl-env))
         (spec-fixpoint (svex-alist-eval-least-fixpoint override-network spec-env)))
      (implies (and (svex-envs-agree-except (svar-override-triplelist-override-vars triples) impl-env spec-env)
                    (svar-override-triplelist-muxes-agree triples impl-env spec-env spec-fixpoint)
                    (svex-env-muxtests-subsetp (svar-override-triplelist->testvars triples) spec-env impl-env)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    (svex-alist-width network)
                    (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys network))
                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys network)))
                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars network))))
               (svex-env-<<= impl-fixpoint spec-fixpoint)))
    :hints (("goal" :expand ((:free (network) (svex-alist-eval-least-fixpoint network impl-env)))))))


;; Spec-fixpoint <<= impl-fixpoint: the composition of the override-alist with
;; the spec-env is <<= the composition of the override-alist with the override-env

(defsection svex-alist-eval-fixpoint-override-spec-fixpoint-<<=-impl-fixpoint
  (defthm svex-alist-eval-fixpoint-override-spec-iter-<<=-impl-iter
    (b* ((override-network (svex-alist-compose network (svar-override-triplelist->override-alist triples)))
         (impl-iter (svex-alist-eval-fixpoint-iterate n override-network impl-start-env impl-env))
         (spec-iter (svex-alist-eval-fixpoint-iterate n override-network spec-start-env spec-env))
         (spec-fixpoint (svex-alist-eval-least-fixpoint override-network spec-env)))
      (implies (and (svex-envs-agree-except (svar-override-triplelist-override-vars triples) impl-env spec-env)
                    (svar-override-triplelist-muxes-agree triples impl-env spec-env spec-fixpoint)
                    (svex-env-muxtests-subsetp (svar-override-triplelist->testvars triples) spec-env impl-env)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    (svex-alist-width network)
                    (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys network))
                    (svex-env-<<= spec-start-env impl-start-env)
                    (svex-env-<<= impl-start-env spec-fixpoint)
                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys network)))
                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars network)))
                    (equal (alist-keys (svex-env-fix spec-start-env)) (svex-alist-keys network))
                    (equal (alist-keys (svex-env-fix impl-start-env)) (svex-alist-keys network)))
               (svex-env-<<= spec-iter impl-iter)))
    :hints (("goal" :induct (acl2::dec-induct n)
             :expand ((:free (network start-env impl-env) (svex-alist-eval-fixpoint-iterate n network start-env impl-env))
                      (:free (network start-env impl-env) (svex-alist-eval-fixpoint-iterate 0 network start-env impl-env)))
             :in-theory (e/d (svex-alist-eval-fixpoint-step-stays-below-fixpoint-free)
                             (svex-alist-eval-least-fixpoint-is-fixpoint)))))

  (defthm svex-alist-eval-fixpoint-override-spec-fixpoint-<<=-impl-fixpoint
    (b* ((override-network (svex-alist-compose network (svar-override-triplelist->override-alist triples)))
         (impl-fixpoint (svex-alist-eval-least-fixpoint override-network impl-env))
         (spec-fixpoint (svex-alist-eval-least-fixpoint override-network spec-env)))
      (implies (and (svex-envs-agree-except (svar-override-triplelist-override-vars triples) impl-env spec-env)
                    (svar-override-triplelist-muxes-agree triples impl-env spec-env spec-fixpoint)
                    (svex-env-muxtests-subsetp (svar-override-triplelist->testvars triples) spec-env impl-env)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    (svex-alist-width network)
                    (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys network))
                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys network)))
                    (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars network))))
               (svex-env-<<= spec-fixpoint impl-fixpoint)))
    :hints(("Goal" :in-theory (enable svex-alist-eval-least-fixpoint)))))

(defthm svex-envs-equivalent-when-similar-and-alist-keys-equiv
  (implies (set-equiv (alist-keys (svex-env-fix x)) (alist-keys (svex-env-fix y)))
           (equal (svex-envs-equivalent x y)
                  (svex-envs-similar x y)))
  :hints (("goal" :cases ((svex-envs-equivalent x y)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (svex-envs-equivalent
                                  SVEX-ENV-BOUNDP-IFF-MEMBER-ALIST-KEYS)))))
  :otf-flg t)

;; To prove this we need to show impl-fixpoint <<= spec-fixpoint and spec-fixpoint <<= impl-fixpoint.

;; Impl-fixpoint <<= spec-fixpoint: the composition of the override-alist with the override-env is <<= the spec-fixpoint,
;; and composition iterations preserve that <<=.

;; Spec-fixpoint <<= impl-fixpoint: the composition of the override-alist with
;; the spec-env is <<= the composition of the override-alist with the override-env

(defthm svex-alist-eval-fixpoint-override-impl-equiv-spec
  (b* ((override-network (svex-alist-compose network (svar-override-triplelist->override-alist triples)))
       (impl-fixpoint (svex-alist-eval-least-fixpoint override-network impl-env))
       (spec-fixpoint (svex-alist-eval-least-fixpoint override-network spec-env)))
    (implies (and (svar-override-triplelist-muxes-agree triples impl-env spec-env spec-fixpoint)
                  (svex-envs-agree-except (svar-override-triplelist-override-vars triples) impl-env spec-env)
                  (svex-env-muxtests-subsetp (svar-override-triplelist->testvars triples) spec-env impl-env)
                  (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                  (no-duplicatesp-equal (svex-alist-keys network))
                  (svex-alist-width network)
                  (subsetp-equal (svar-override-triplelist->refvars triples) (svex-alist-keys network))
                  (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-keys network)))
                  (not (intersectp-equal (svar-override-triplelist-override-vars triples) (svex-alist-vars network))))
             (svex-envs-equivalent impl-fixpoint spec-fixpoint)))
  :hints(("Goal" 
          :use svex-alist-eval-fixpoint-override-spec-fixpoint-<<=-impl-fixpoint
          :in-theory (e/d (svex-env-<<=-asymm)
                          (svex-alist-eval-fixpoint-override-spec-fixpoint-<<=-impl-fixpoint)))))











(defsection svex-alist-least-fixpoint-override-transparent
  (local (defthmd svarlist-to-override-alist-in-terms-of-svar-override-triplelist->override-alist
           (equal (svarlist-to-override-alist keys)
                  (svar-override-triplelist->override-alist (svarlist-to-override-triples keys)))
           :hints(("Goal" :in-theory (enable svarlist-to-override-triples
                                             svar-override-triplelist->override-alist
                                             svarlist-to-override-alist)))))
  ;; (defthm svex-alist-width-aux-of-svex-alist-compose-svarlist-to-override-alist
  ;;   (implies (svarlist-override-p (svex-alist-vars x) nil)
  ;;            (equal (svex-alist-width-aux (svex-alist-compose x (svarlist-to-override-alist overridekeys)))
  ;;                   (svex-alist-width-aux x)))
  ;;   :hints(("Goal" :in-theory (enable svarlist-to-override-alist-in-terms-of-svar-override-triplelist->override-alist
  ;;                                     ))))

  (defthm svex-alist-width-of-svex-alist-compose-svarlist-to-override-alist
    (implies (svarlist-override-p (svex-alist-vars x) nil)
             (equal (svex-alist-width (svex-alist-compose x (svarlist-to-override-alist overridekeys)))
                    (svex-alist-width x)))
    :hints(("Goal" :in-theory (enable svarlist-to-override-alist-in-terms-of-svar-override-triplelist->override-alist
                                      ))))

  (defthm svarlist-change-override-when-svarlist-override-p
    (implies (svarlist-override-p x type)
             (equal (svarlist-change-override x type)
                    (svarlist-fix x)))
    :hints(("Goal" :in-theory (enable svarlist-override-p
                                      svarlist-change-override))))


  (defthmd svex-envs-agree-except-when-subsetp
    (implies (and (svex-envs-agree-except vars x y)
                  (subsetp-equal (svarlist-fix vars) (Svarlist-fix vars2)))
             (svex-envs-agree-except vars2 x y))
    :hints (("goal" :expand ((svex-envs-agree-except vars2 x y))
             :use ((:instance svex-envs-agree-except-implies
                    (var (svex-envs-agree-except-witness vars2 x y)))))))

  (defthmd svex-alist-monotonic-on-vars-when-subsetp
    (implies (and (svex-alist-monotonic-on-vars vars x)
                  (subsetp-equal (Svarlist-fix vars2) (svarlist-fix vars)))
             (svex-alist-monotonic-on-vars vars2 x))
    :hints (("goal" :expand ((svex-alist-monotonic-on-vars vars2 x))
             :in-theory (enable svex-envs-agree-except-when-subsetp)
             :use ((:instance svex-alist-monotonic-on-vars-necc
                    (env1 (mv-nth 0 (svex-alist-monotonic-on-vars-witness vars2 x)))
                    (env2 (mv-nth 1 (svex-alist-monotonic-on-vars-witness vars2 x))))))))

  (local (defthm member-change-override-when-svarlist-override-p
           (implies (svarlist-override-p vars nil)
                    (not (member-equal (svar-change-override v :test) (Svarlist-fix vars))))
           :hints(("Goal" :in-theory (enable svarlist-change-override
                                             svarlist-override-p
                                             svarlist-fix
                                             equal-of-svar-change-override
                                             svar-override-p-when-other)))))

  (defthm svarlist-to-override-alist-monotonic-on-non-override-vars
    (implies (svarlist-override-p vars nil)
             (svex-alist-monotonic-on-vars vars (svarlist-to-override-alist keys)))
    :hints(("Goal" :in-theory (enable svarlist-to-override-alist))))

  
  (local
   (encapsulate nil

     (local (defthm svex-alist-eval-of-extract-vars
              (implies (subsetp-equal (svex-alist-vars x) (svarlist-fix vars))
                       (Equal (svex-alist-eval x (svex-env-extract vars env))
                              (svex-alist-eval x env)))
              :hints(("Goal" :in-theory (enable svex-alist-eval
                                                svex-alist-vars)))))
     
     (local (defthm svex-env-extract-of-append-envs
              (svex-envs-similar (svex-env-extract vars (append x y))
                                 (append (svex-env-reduce vars x)
                                         (svex-env-reduce vars y)))
              :hints(("Goal" :in-theory (enable svex-envs-similar)))))

     (local (defthm svex-env-reduce-of-append-envs
              (svex-envs-similar (svex-env-reduce vars (append x y))
                                 (append (svex-env-reduce vars x)
                                         (svex-env-reduce vars y)))
              :hints(("Goal" :in-theory (enable svex-envs-similar)))))
     
     (local (defthmd rewrite-svex-alist-eval-with-extract
              (implies (and (svex-envs-similar env1 (double-rewrite (svex-env-extract (svex-alist-vars x) env)))
                            (bind-free
                             (case-match env1
                               (('svex-env-extract & env2)
                                `((env2 . ,env2)))
                               (& `((env2 . ,env1))))
                             (env2))
                            (syntaxp (or (cw "env2: ~x0~%" env2) t))
                            (svex-envs-similar env1 (svex-env-extract (svex-alist-vars x) env2))
                            (syntaxp (not (equal env2 env)))
                            (syntaxp (or (cw "ok~%") t)))
                       (equal (svex-alist-eval x env)
                              (svex-alist-eval x env2)))
              :hints (("goal" :use ((:instance svex-alist-eval-of-extract-vars
                                     (vars (svex-alist-vars x))
                                     (env env2))
                                    (:instance svex-alist-eval-of-extract-vars
                                     (vars (svex-alist-vars x))
                                     (env env)))
                       :in-theory (disable svex-alist-eval-of-extract-vars)))))

     (local (defthmd svex-env-eval-of-svex-alist-reduce-rev
              (equal (svex-env-reduce vars (svex-alist-eval x env))
                     (svex-alist-eval (svex-alist-reduce vars x) env))))

     (local (defthm svex-eval-of-svex-var
              (equal (svex-eval (svex-var x) env)
                     (svex-env-lookup x env))
              :hints(("Goal" :in-theory (enable svex-eval)))))


     


     ;; (local (defthm 4vec-bit?!-<<=-when-4vec-muxtest-subsetp-bitmux-lemma
     ;;          (implies (and (equal (4vec-bitmux impl-test impl-val ref-val)
     ;;                               (4vec-bitmux spec-test spec-val ref-val))
     ;;                        (equal (logandc2 spec-test impl-test) 0)
     ;;                        (4vec-<<= other-val ref-val))
     ;;                   (4vec-<<= (4vec-bitmux impl-test impl-val other-val)
     ;;                             (4vec-bitmux spec-test spec-val ref-val)))
     ;;          :hints (("goal" :in-theory (enable 4vec-muxtest-subsetp
     ;;                                             4vec-bitmux
     ;;                                             4vec-<<=))
     ;;                  (acl2::logbitp-reasoning)
     ;;                  (and stable-under-simplificationp
     ;;                       '(:in-theory (enable bool->bit))))))
     
     ;; (local (defthm 4vec-bit?!-<<=-when-4vec-muxtest-subsetp-lemma
     ;;          (implies (and (equal (4vec-bit?! impl-test impl-val ref-val)
     ;;                               (4vec-bit?! spec-test spec-val ref-val))
     ;;                        (4vec-muxtest-subsetp spec-test impl-test)
     ;;                        (4vec-<<= other-val ref-val))
     ;;                   (4vec-<<= (4vec-bit?! impl-test impl-val other-val)
     ;;                             (4vec-bit?! spec-test spec-val ref-val)))
     ;;          :hints (("goal" :in-theory (enable 4vec-muxtest-subsetp
     ;;                                             4vec-bit?!
     ;;                                             4vec-<<=))
     ;;                  (acl2::logbitp-reasoning)
     ;;                  (and stable-under-simplificationp
     ;;                       '(:in-theory (enable bool->bit))))))

     (local (defthm member-equal-of-svar-change-override
              (implies (svarlist-override-p x nil)
                       (not (member-equal (svar-change-override v :val) (svarlist-fix x))))
              :hints(("Goal" :in-theory (enable svarlist-override-p
                                                svarlist-fix
                                                svar-override-p-when-other
                                                equal-of-svar-change-override)))))
     
     (local
      (defthm eval-override-mux-lemma
        (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env env2)
                      (svar-override-p v nil)
                      (member-equal (svar-fix v) (svarlist-change-override overridekeys nil))
                      (svarlist-override-p non-override-vars nil)
                      (svex-env-<<= env1 env2)
                      (member-equal (svar-change-override v nil) (svarlist-fix non-override-vars)))
                 (4vec-<<= (svex-eval (svex-call 'bit?!
                                                 (list (svex-var (svar-change-override v :test))
                                                       (svex-var (svar-change-override v :val))
                                                       (svex-var v)))
                                      (append (svex-env-extract non-override-vars env1)
                                              impl-env))
                           (svex-eval (svex-call 'bit?!
                                                 (list (svex-var (svar-change-override v :test))
                                                       (svex-var (svar-change-override v :val))
                                                       (svex-var v)))
                                      (append (svex-env-extract non-override-vars env2)
                                              spec-env))))
        :hints(("Goal" :in-theory (enable svex-apply)
                :use ((:instance 4vec-bit?!-agree-when-overridekeys-envs-agree
                       (spec-outs env2)
                       (testvar (svar-change-override v :test))
                       (valvar (svar-change-override v :val))
                       (refval (svex-env-lookup (svar-change-override v nil) env2))))
                ))
        :otf-flg t))

     (local (defthm svar-override-p-when-equal-change-override
              (implies (equal (svar-fix v) (svar-change-override x type))
                       (svar-override-p v type))
              :hints (("goal" :use ((:instance SVAR-OVERRIDE-P-OF-SVAR-CHANGE-OVERRIDE
                                     (x x) (type type) (other-type type)))))))
     
     (local (defthm svar-override-p-when-member-change-override
              (implies (member-equal (svar-fix v) (svarlist-change-override overridekeys type))
                       (svar-override-p v type))
              :hints(("Goal" :in-theory (enable svarlist-change-override
                                                equal-of-svar-change-override)
                      :induct t))))
     
     (local (defthm svarlist-override-p-when-subsetp-change-override
              (implies (subsetp-equal (Svarlist-fix v) (svarlist-change-override overridekeys type))
                       (svarlist-override-p v type))
              :hints(("Goal" :in-theory (enable svarlist-fix
                                                svarlist-override-p)
                      :induct t))))

     (local (defthm svar-override-p-when-member
              (implies (and (member-equal (Svar-fix v) (svarlist-fix x))
                            (svarlist-override-p x type))
                       (svar-override-p v type))
              :hints(("Goal" :in-theory (enable svarlist-fix
                                                svarlist-override-p)
                      :induct t))))
     
     (local (defthm svarlist-override-p-when-subsetp
              (implies (and (subsetp-equal (Svarlist-fix v) (svarlist-fix x))
                            (svarlist-override-p x type))
                       (svarlist-override-p v type))
              :hints(("Goal" :in-theory (enable svarlist-fix
                                                svarlist-override-p)
                      :induct t))))

     (local (defthm svarlist-override-p-when-subsetp-nofix
              (implies (and (subsetp-equal (Svarlist-fix v) x)
                            (svarlist-p x)
                            (svarlist-override-p x type))
                       (svarlist-override-p v type))
              :hints (("goal" :use svarlist-override-p-when-subsetp))))
              
     
     (local (defthm svex-lookup-in-svarlist-to-override-alist
              (equal (svex-lookup v (svarlist-to-override-alist overridekeys))
                     (and (member-equal (svar-fix v) (svarlist-change-override overridekeys nil))
                          (svex-call 'bit?!
                                     (list (svex-var (svar-change-override v :test))
                                           (svex-var (svar-change-override v :val))
                                           (svex-var v)))))
              :hints(("Goal" :in-theory (enable svarlist-change-override
                                                svarlist-to-override-alist
                                                svex-lookup-redef
                                                equal-of-svar-change-override
                                                svar-change-override-when-svar-override-p)))))
     
     ;; (local
     ;;  (defthm 4vec-<<=-of-eval-lookup-of-svarlist-to-override-alist-when-overridekeys-envs-agree
     ;;    (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env env2)
     ;;                 (member-equal (svar-fix v) (svarlist-change-override overridekeys nil))
     ;;                 (svex-env-<<= env1 env2)
     ;;                 (svar-override-p v nil)
     ;;                 (member-equal (svar-fix v) (svarlist-fix non-override-vars))
     ;;                 (svarlist-override-p non-override-vars nil))
     ;;             (4vec-<<= (svex-eval (svex-lookup v (svarlist-to-override-alist overridekeys))
     ;;                                  (append (svex-env-extract non-override-vars env1)
     ;;                                          impl-env))
     ;;                       (svex-eval (svex-lookup v (svarlist-to-override-alist overridekeys))
     ;;                                  (append (svex-env-extract non-override-vars env2)
     ;;                                          spec-env))))
     ;;    :hints(("Goal" :in-theory (disable svex-eval-when-fncall
     ;;                                       svex-eval-of-svex-call)))))

     (local
      (defthm svex-env-<<=-of-svarlist-to-override-alist-when-overridekeys-envs-agree
        (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env env2)
                      (svex-env-<<= env1 env2)
                      (svarlist-override-p keys nil)
                      (subsetp-equal (svarlist-fix overridekeys) (svarlist-fix keys))
                      (svex-env-<<= env1 env2))
                 (svex-env-<<= (svex-alist-eval
                                (svarlist-to-override-alist overridekeys)
                                (append (svex-env-extract keys env1)
                                        impl-env))
                               (svex-alist-eval
                                (svarlist-to-override-alist overridekeys)
                                (append (svex-env-extract keys env2)
                                        spec-env))))
        :hints(("Goal" :in-theory (e/d (svex-env-<<=)
                                       (svex-eval-when-fncall
                                        svex-eval-of-svex-call))))))


     (local (defthm reduce-nonoverride-vars-when-overridekeys-envs-agree
              (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env spec-outs)
                            (svarlist-override-p keys nil))
                       (svex-envs-similar (svex-env-reduce keys impl-env)
                                          (svex-env-reduce keys spec-env)))
              :hints(("Goal" :in-theory (enable svex-envs-similar
                                                nonoverride-vars-agree-when-overridekeys-envs-agree)))))

     (local (defthm svex-env-<<=-of-svex-env-reduce
              (implies (svex-env-<<= x y)
                       (svex-env-<<= (svex-env-reduce vars x)
                                     (svex-env-reduce vars y)))
              :hints (("goal" :expand ((svex-env-<<= (svex-env-reduce vars x)
                                                     (svex-env-reduce vars y)))))))

     (local (defthm svex-envs-agree-except-of-append
              (implies (and (svex-envs-agree-except vars x1 y1)
                            (svex-envs-agree-except vars x2 y2)
                            (equal (alist-keys (svex-env-fix x1))
                                   (alist-keys (svex-env-fix y1))))
                       (svex-envs-agree-except vars (append x1 x2) (append y1 y2)))
              :hints (("goal" :expand ((svex-envs-agree-except vars (append x1 x2) (append y1 y2)))
                       :in-theory (e/d (svex-env-boundp-iff-member-alist-keys
                                        svex-envs-agree-except-implies)
                                       (acl2::alist-keys-member-hons-assoc-equal))
                       :do-not-induct t))
              :otf-flg t))

     (local (defthm svex-envs-agree-except-of-reduce
              (implies (svex-envs-agree-except vars x y)
                       (svex-envs-agree-except vars (svex-env-reduce vars2 x)
                                               (svex-env-reduce vars2 y)))
              :hints (("goal" :expand ((svex-envs-agree-except vars (svex-env-reduce vars2 x)
                                                               (svex-env-reduce vars2 y)))
                       :in-theory (e/d (svex-envs-agree-except-implies))))))

     (local (defthm svex-env-removekeys-when-keys-subsetp
              (implies (subsetp-equal (alist-keys (svex-env-fix env)) (svarlist-fix vars))
                       (equal (svex-env-removekeys vars env) nil))
              :hints(("Goal" :in-theory (enable svex-env-removekeys svex-env-fix alist-keys)))))
     
     (defthm svex-alist-eval-fixpoint-step-when-overridekeys-envs-agree
       (b* ((override-network (svex-alist-compose network (svarlist-to-override-alist overridekeys))))
         (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env env2)
                       (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                       (svarlist-override-p (svex-alist-vars network) nil)
                       (svarlist-override-p (svex-alist-keys network) nil)
                       (subsetp-equal (svarlist-fix overridekeys) (svex-alist-keys network))
                       (svex-env-<<= env1 env2))
                  (svex-env-<<= (svex-alist-eval-fixpoint-step override-network env1 impl-env)
                                (svex-alist-eval-fixpoint-step override-network env2 spec-env))))
       :hints(("Goal" :in-theory (enable svex-alist-eval-fixpoint-step
                                         rewrite-svex-alist-eval-with-extract
                                         svex-alist-monotonic-on-vars-necc
                                         svex-envs-agree-except-when-removekeys-similar)
               :restrict (( rewrite-svex-alist-eval-with-extract
                            ((x network)))))))

     
     (local (defthm 4vec-bit?!-<<=-when-4vec-muxtest-subsetp-bitmux-lemma
              (implies (and (equal (4vec-bitmux impl-test impl-val ref-val)
                                   (4vec-bitmux spec-test spec-val ref-val))
                            (equal (logandc2 spec-test impl-test) 0)
                            (4vec-<<= other-val1 other-val2)
                            (4vec-<<= other-val1 ref-val)
                            )
                       (4vec-<<= (4vec-bitmux spec-test spec-val other-val1)
                                 (4vec-bitmux impl-test impl-val other-val2)))
              :hints (("goal" :in-theory (enable 4vec-muxtest-subsetp
                                                 4vec-bitmux
                                                 4vec-<<=))
                      (acl2::logbitp-reasoning)
                      (and stable-under-simplificationp
                           '(:in-theory (enable bool->bit))))))
     
     (local (defthm 4vec-bit?!-<<=-when-4vec-muxtest-subsetp-lemma
              (implies (and (equal (4vec-bit?! impl-test impl-val ref-val)
                                   (4vec-bit?! spec-test spec-val ref-val))
                            (4vec-muxtest-subsetp spec-test impl-test)
                            (4vec-<<= other-val1 other-val2)
                            (4vec-<<= other-val1 ref-val))
                       (4vec-<<= (4vec-bit?! spec-test spec-val other-val1)
                                 (4vec-bit?! impl-test impl-val other-val2)))
              :hints (("goal" :in-theory (enable 4vec-muxtest-subsetp
                                                 4vec-bit?!)))))

     

     (local
      (defthm eval-override-mux-lemma-2
        (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env env3)
                      (svar-override-p v nil)
                      (member-equal (svar-fix v) (svarlist-change-override overridekeys nil))
                      (svarlist-override-p non-override-vars nil)
                      (svex-env-<<= env1 env2)
                      (svex-env-<<= env1 env3)
                      (member-equal (svar-change-override v nil) (svarlist-fix non-override-vars)))
                 (4vec-<<= (svex-eval (svex-call 'bit?!
                                                 (list (svex-var (svar-change-override v :test))
                                                       (svex-var (svar-change-override v :val))
                                                       (svex-var v)))
                                      (append (svex-env-extract non-override-vars env1)
                                              spec-env))
                           (svex-eval (svex-call 'bit?!
                                                 (list (svex-var (svar-change-override v :test))
                                                       (svex-var (svar-change-override v :val))
                                                       (svex-var v)))
                                      (append (svex-env-extract non-override-vars env2)
                                              impl-env))))
        :hints(("Goal" :in-theory (enable svex-apply
                                          4vec-muxtest-subsetp-when-overridekeys-envs-agree)
                :use ((:instance 4vec-bit?!-agree-when-overridekeys-envs-agree
                       (spec-outs env3)
                       (testvar (svar-change-override v :test))
                       (valvar (svar-change-override v :val))
                       (refval (svex-env-lookup (svar-change-override v nil) env3))))
                ))
        :otf-flg t))

     (local
      (defthm svex-env-<<=-of-svarlist-to-override-alist-when-overridekeys-envs-agree-2
        (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env env3)
                      (svex-env-<<= env1 env2)
                      (svex-env-<<= env1 env3)
                      (svarlist-override-p keys nil)
                      (subsetp-equal (svarlist-fix overridekeys) (svarlist-fix keys)))
                 (svex-env-<<= (svex-alist-eval
                                (svarlist-to-override-alist overridekeys)
                                (append (svex-env-extract keys env1)
                                        spec-env))
                               (svex-alist-eval
                                (svarlist-to-override-alist overridekeys)
                                (append (svex-env-extract keys env2)
                                        impl-env))))
        :hints(("Goal" :in-theory (e/d (svex-env-<<=)
                                       (svex-eval-when-fncall
                                        svex-eval-of-svex-call))))))

     (defthm svex-alist-eval-fixpoint-step-when-overridekeys-envs-agree-2
       (b* ((override-network (svex-alist-compose network (svarlist-to-override-alist overridekeys))))
         (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env env3)
                       (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                       (svarlist-override-p (svex-alist-vars network) nil)
                       (svarlist-override-p (svex-alist-keys network) nil)
                       (subsetp-equal (svarlist-fix overridekeys) (svex-alist-keys network))
                       (svex-env-<<= env1 env2)
                       (svex-env-<<= env1 env3))
                  (svex-env-<<= (svex-alist-eval-fixpoint-step override-network env1 spec-env)
                                (svex-alist-eval-fixpoint-step override-network env2 impl-env))))
       :hints(("Goal" :in-theory (enable svex-alist-eval-fixpoint-step
                                         rewrite-svex-alist-eval-with-extract
                                         svex-alist-monotonic-on-vars-necc
                                         svex-envs-agree-except-when-removekeys-similar)
               :restrict (( rewrite-svex-alist-eval-with-extract
                            ((x network)))))))
     ))

  
  (defthm svex-alist-eval-fixpoint-override-impl-iter-<<=-spec-fixpoint-when-overridekeys-envs-agree
    (b* ((override-network (svex-alist-compose network (svarlist-to-override-alist overridekeys)))
         (impl-iter (svex-alist-eval-fixpoint-iterate n override-network start-env impl-env))
         (spec-fixpoint (svex-alist-eval-least-fixpoint override-network spec-env)))
      (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env spec-fixpoint)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    (no-duplicatesp-equal (svarlist-fix overridekeys))
                    (svex-alist-width network)
                    (svarlist-override-p overridekeys nil)
                    (subsetp-equal (svarlist-fix overridekeys) (svex-alist-keys network))
                    (svex-env-<<= start-env spec-fixpoint)
                    (svarlist-override-p (svex-alist-keys network) nil)
                    (svarlist-override-p (svex-alist-vars network) nil)
                    (equal (alist-keys (svex-env-fix start-env)) (svex-alist-keys network)))
               (svex-env-<<= impl-iter spec-fixpoint)))
    :hints (("goal" :induct (acl2::dec-induct n)
             :expand ((:free (network) (svex-alist-eval-fixpoint-iterate n network start-env impl-env))
                      (:free (network) (svex-alist-eval-fixpoint-iterate 0 network start-env impl-env)))
             :in-theory (e/d (svex-alist-eval-fixpoint-step-stays-below-fixpoint-free
                              svex-alist-monotonic-on-vars-when-subsetp)
                             (svex-alist-eval-least-fixpoint-is-fixpoint
                              SVEX-ALIST-EVAL-FIXPOINT-STEP-OF-COMPOSE)))))

  (defthm svex-alist-eval-fixpoint-override-impl-fixpoint-<<=-spec-fixpoint-when-overridekeys-envs-agree
    (b* ((override-network (svex-alist-compose network (svarlist-to-override-alist overridekeys)))
         (impl-fixpoint (svex-alist-eval-least-fixpoint override-network impl-env))
         (spec-fixpoint (svex-alist-eval-least-fixpoint override-network spec-env)))
      (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env spec-fixpoint)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    (no-duplicatesp-equal (svarlist-fix overridekeys))
                    (svex-alist-width network)
                    (svarlist-override-p overridekeys nil)
                    (subsetp-equal (svarlist-fix overridekeys) (svex-alist-keys network))
                    (svarlist-override-p (svex-alist-keys network) nil)
                    (svarlist-override-p (svex-alist-vars network) nil))
               (svex-env-<<= impl-fixpoint spec-fixpoint)))
    :hints (("goal" :expand ((:free (network) (svex-alist-eval-least-fixpoint network impl-env))))))


  (local (defthm svex-env-<<=-of-svex-env-extract-first
           (implies (svex-env-<<= x y)
                    (svex-env-<<= (Svex-env-extract vars x) y))
           :hints (("goal" :expand ((svex-env-<<= (Svex-env-extract vars x) y))))))
  
  (local (defthm SVEX-ALIST-EVAL-FIXPOINT-ITERATE-LEAST-FIXPOINT-rw
           (b* ((fixpoint (svex-alist-eval-least-fixpoint network env)))
             (implies (and (svex-env-<<= start-env fixpoint)
                           (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                           (svex-alist-width network)
                           (no-duplicatesp-equal (svex-alist-keys network)))
                    (svex-env-<<= (svex-alist-eval-fixpoint-iterate
                                   n network start-env env)
                                  fixpoint)))
           :hints (("goal" :induct (acl2::dec-induct n)
                    :expand ((:free (start-env) (svex-alist-eval-fixpoint-iterate
                                                 n network start-env env))
                             (:free (start-env) (svex-alist-eval-fixpoint-iterate
                                                 0 network start-env env)))))))
                         


  (defthm svex-alist-eval-fixpoint-override-spec-iter-<<=-impl-iter-when-overridekeys-envs-agree
    (b* ((override-network (svex-alist-compose network (svarlist-to-override-alist overridekeys)))
         (spec-start-env (svarlist-x-env (Svex-alist-keys network)))
         (impl-iter (svex-alist-eval-fixpoint-iterate n override-network impl-start-env impl-env))
         (spec-iter (svex-alist-eval-fixpoint-iterate n override-network spec-start-env spec-env))
         (spec-fixpoint (svex-alist-eval-least-fixpoint override-network spec-env)))
      (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env spec-fixpoint)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    (no-duplicatesp-equal (svarlist-fix overridekeys))
                    (svex-alist-width network)
                    (svarlist-override-p overridekeys nil)
                    (subsetp-equal (svarlist-fix overridekeys) (svex-alist-keys network))
                    (svex-env-<<= spec-start-env impl-start-env)
                    (svex-env-<<= impl-start-env spec-fixpoint)
                    (equal (alist-keys (svex-env-fix spec-start-env)) (svex-alist-keys network))
                    (equal (alist-keys (svex-env-fix impl-start-env)) (svex-alist-keys network))
                    (svarlist-override-p (svex-alist-keys network) nil)
                    (svarlist-override-p (svex-alist-vars network) nil))
               (svex-env-<<= spec-iter impl-iter)))
    :hints (("goal" :induct (acl2::dec-induct n)
             :expand ((:free (network start-env impl-env) (svex-alist-eval-fixpoint-iterate n network start-env impl-env))
                      (:free (network start-env impl-env) (svex-alist-eval-fixpoint-iterate 0 network start-env impl-env)))
             :in-theory (e/d (svex-alist-eval-fixpoint-step-stays-below-fixpoint-free)
                             (svex-alist-eval-least-fixpoint-is-fixpoint
                              SVEX-ALIST-EVAL-FIXPOINT-STEP-OF-COMPOSE)))))

  (defthm svex-alist-eval-fixpoint-override-spec-fixpoint-<<=-impl-fixpoint-when-overridekeys-envs-agree
    (b* ((override-network (svex-alist-compose network (svarlist-to-override-alist overridekeys)))
         (impl-fixpoint (svex-alist-eval-least-fixpoint override-network impl-env))
         (spec-fixpoint (svex-alist-eval-least-fixpoint override-network spec-env)))
      (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env spec-fixpoint)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    (no-duplicatesp-equal (svarlist-fix overridekeys))
                    (svex-alist-width network)
                    (svarlist-override-p overridekeys nil)
                    (subsetp-equal (svarlist-fix overridekeys) (svex-alist-keys network))
                    (svarlist-override-p (svex-alist-keys network) nil)
                    (svarlist-override-p (svex-alist-vars network) nil))
               (svex-env-<<= spec-fixpoint impl-fixpoint)))
    :hints(("Goal" :in-theory (enable svex-alist-eval-least-fixpoint))))

  (defthm svex-alist-eval-fixpoint-override-impl-fixpoint-==-spec-fixpoint-when-overridekeys-envs-agree
    (b* ((override-network (svex-alist-compose network (svarlist-to-override-alist overridekeys)))
         (impl-fixpoint (svex-alist-eval-least-fixpoint override-network impl-env))
         (spec-fixpoint (svex-alist-eval-least-fixpoint override-network spec-env)))
      (implies (and (overridekeys-envs-agree overridekeys impl-env spec-env spec-fixpoint)
                    (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    (no-duplicatesp-equal (svarlist-fix overridekeys))
                    (svex-alist-width network)
                    (svarlist-override-p overridekeys nil)
                    (subsetp-equal (svarlist-fix overridekeys) (svex-alist-keys network))
                    (svarlist-override-p (svex-alist-keys network) nil)
                    (svarlist-override-p (svex-alist-vars network) nil))
               (svex-envs-equivalent spec-fixpoint impl-fixpoint)))
  :hints(("Goal" 
          :use svex-alist-eval-fixpoint-override-spec-fixpoint-<<=-impl-fixpoint-when-overridekeys-envs-agree
          :in-theory (e/d (svex-env-<<=-asymm)
                          (svex-alist-eval-fixpoint-override-spec-fixpoint-<<=-impl-fixpoint-when-overridekeys-envs-agree)))))
  
  (local (defun svex-envs-unequal-key (x y)
           (if (atom x)
               nil
             (if (equal (cdar x) (cdar y))
                 (svex-envs-unequal-key (cdr x) (cdr y))
               (caar x)))))

  (local (defthm alist-keys-under-iff-when-svex-env-p
           (implies (svex-env-p y)
                    (iff (alist-keys y) y))
           :hints(("Goal" :in-theory (enable svex-env-p alist-keys)))))

  (local (defthm svex-envs-unequal-key-finds-unequal
           (implies (and (svex-env-p x)
                         (svex-env-p y)
                         (equal (alist-keys x) (alist-keys y))
                         (no-duplicatesp-equal (alist-keys x))
                         (not (equal x y)))
                    (not (equal (svex-env-lookup (svex-envs-unequal-key x y) x)
                                (svex-env-lookup (svex-envs-unequal-key x y) y))))
           :hints(("Goal" :in-theory (e/d (svex-env-lookup
                                           alist-keys svex-env-p
                                           acl2::hons-assoc-equal-when-not-member-alist-keys)
                                          (acl2::alist-keys-member-hons-assoc-equal))))))
  
  (local (defthm equal-of-svex-envs-when-keys-equal
           (implies (and (svex-env-p x)
                         (svex-env-p y)
                         (equal (alist-keys x) (alist-keys y))
                         (no-duplicatesp-equal (alist-keys x)))
                    (equal (equal x y)
                           (svex-envs-similar x y)))
           :hints (("goal" :use ((:instance svex-envs-similar-necc
                                  (k (svex-envs-unequal-key x y))))
                    :in-theory (disable SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-LOOKUP-2)))))
  
  (defthm svex-alist-least-fixpoint-override-transparent
    (b* ((override-network (svex-alist-compose network (svarlist-to-override-alist overridekeys)))
         (fixpoint (svex-alist-least-fixpoint override-network)))
      (implies (and (svex-alist-monotonic-on-vars (svex-alist-keys network) network)
                    (no-duplicatesp-equal (svex-alist-keys network))
                    (no-duplicatesp-equal (svarlist-fix overridekeys))
                    (svex-alist-width network)
                    (svarlist-override-p overridekeys nil)
                    (subsetp-equal (svarlist-fix overridekeys) (svex-alist-keys network))
                    (svarlist-override-p (svex-alist-keys network) nil)
                    (svarlist-override-p (svex-alist-vars network) nil))
               (svex-alist-overridekey-transparent-p fixpoint overridekeys fixpoint)))
    :hints(("Goal" :in-theory (enable svex-alist-overridekey-transparent-p)))))
