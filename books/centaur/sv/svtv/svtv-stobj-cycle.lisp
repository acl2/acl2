; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "svtv-stobj")
(include-book "cycle-compile")

(local (include-book "std/util/termhints" :dir :system))
(local (defstub hq (x) nil))
(local (acl2::termhint-add-quotesym hq))






(local
 (defsection svtv-fsm-to-cycle-cong
   (defret eval-outs-lookup-of-<fn>
     (equal (svex-eval (svex-lookup var outs) env)
            (svex-env-lookup var (svtv-cycle-eval-outs env
                                                       (svex-alist-eval prev-st env)
                                                       phases x)))
     :hints (("goal" :use eval-outs-of-<fn>
              :in-theory (disable eval-outs-of-<fn>)))
     :fn svtv-cycle-compile)

   (local
    (defret outs-lookup-exists-of-<fn>
      (iff (svex-lookup var outs)
           (svex-env-boundp var (svtv-cycle-eval-outs env
                                                      (svex-alist-eval prev-st env)
                                                      phases x)))
      :hints (("goal" :use eval-outs-of-<fn>
               :in-theory (disable eval-outs-of-<fn>)))
      :fn svtv-cycle-compile))

   (defret eval-nextst-lookup-of-<fn>
     (equal (svex-eval (svex-lookup var nextst) env)
            (svex-env-lookup var (svtv-cycle-eval-nextst env
                                                       (svex-alist-eval prev-st env)
                                                       phases x)))
     :hints (("goal" :use eval-nextsts-of-<fn>
              :in-theory (disable eval-nextsts-of-<fn>)))
     :fn svtv-cycle-compile)

   (local
    (defret nextst-lookup-exists-of-<fn>
      (iff (svex-lookup var nextst)
           (svex-env-boundp var (svtv-cycle-eval-nextst env
                                                      (svex-alist-eval prev-st env)
                                                      phases x)))
      :hints (("goal" :use eval-nextsts-of-<fn>
               :in-theory (disable eval-nextsts-of-<fn>)))
      :fn svtv-cycle-compile))

   (defthm svtv-fsm-eval-equiv-congruence-of-svtv-cycle-compile-outs
     (implies (svtv-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 0 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 0 (svtv-cycle-compile prev-st phases fsm-equiv))))
     :hints((witness) (witness))
     :rule-classes :congruence)

   (defthm svtv-fsm-eval-equiv-congruence-of-svtv-cycle-compile-nextst
     (implies (svtv-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 1 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 1 (svtv-cycle-compile prev-st phases fsm-equiv))))
     :hints((witness) (witness))
     :rule-classes :congruence)
   
   (defthm prev-st-congruence-of-svtv-cycle-compile-outs
     (implies (svex-alist-eval-equiv prev-st prev-st-equiv)
              (svex-alist-eval-equiv (mv-nth 0 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 0 (svtv-cycle-compile prev-st-equiv phases fsm))))
     :hints((witness :ruleset svex-alist-eval-equiv-witnessing) ;; (witness)
            (witness :ruleset svex-eval-equiv-witnessing)
            )
     :rule-classes :congruence)

   (defthm prev-st-congruence-of-svtv-cycle-compile-nextst
     (implies (svex-alist-eval-equiv prev-st prev-st-equiv)
              (svex-alist-eval-equiv (mv-nth 1 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 1 (svtv-cycle-compile prev-st-equiv phases fsm))))
     :hints((witness :ruleset svex-alist-eval-equiv-witnessing) ;; (witness)
            (witness :ruleset svex-eval-equiv-witnessing)
            )
     :rule-classes :congruence)

   (defthm svtv-fsm-eval-equiv-congruence-of-svtv-cycle-compile-nextst
     (implies (svtv-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 1 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 1 (svtv-cycle-compile prev-st phases fsm-equiv))))
     :hints((witness) (witness))
     :rule-classes :congruence)

   (defthm svtv-fsm-eval-equiv-congruence-of-svtv-cycle-compile-outs
     (implies (svtv-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 0 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 0 (svtv-cycle-compile prev-st phases fsm-equiv))))
     :hints((witness) (witness))
     :rule-classes :congruence)

   (defthm svtv-fsm-eval-equiv-congruence-of-svtv-cycle-compile-nextst
     (implies (svtv-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 1 (svtv-cycle-compile prev-st phases fsm))
                                     (mv-nth 1 (svtv-cycle-compile prev-st phases fsm-equiv))))
     :hints((witness) (witness))
     :rule-classes :congruence)



   

   (defcong svtv-fsm-eval-equiv svtv-fsm-eval-equiv (svtv-fsm-to-cycle phases fsm) 2
     :hints(("Goal" :in-theory (enable svtv-fsm-to-cycle))))))

  


(local (in-theory (disable hons-dups-p)))


(local (defthm cycle-fsm-okp-of-svtv-fsm-to-cycle
         (b* (((svtv-fsm base-fsm) (svtv-data$c->base-fsm svtv-data))
              ((mv values nextstate)
               (svtv-cycle-compile (svex-identity-subst
                                    (svex-alist-keys (svtv-data$c->base-nextstate svtv-data)))
                                   (svtv-data$c->cycle-phases svtv-data)
                                   base-fsm)))
           (svtv-data$c-cycle-fsm-okp svtv-data values nextstate))
         :hints(("Goal" :in-theory (enable svtv-data$c-cycle-fsm-okp)))))

(local (defthm cycle-fsm-okp-implies-cycle-compile-values-equiv
         (implies (svtv-data$c-cycle-fsm-okp svtv-data values1 nextstate1)
                  (b* (((svtv-fsm base-fsm) (svtv-data$c->base-fsm svtv-data))
                       ((mv ?values ?nextstate)
                        (svtv-cycle-compile (svex-identity-subst
                                             (svex-alist-keys (svtv-data$c->base-nextstate svtv-data)))
                                            (svtv-data$c->cycle-phases svtv-data)
                                            base-fsm)))
                    (svex-alist-eval-equiv values values1)))
         :hints ((acl2::use-termhint
                  (b* (((svtv-fsm base-fsm) (svtv-data$c->base-fsm svtv-data))
                       ((mv ?values ?nextstate)
                        (svtv-cycle-compile (svex-identity-subst
                                             (svex-alist-keys (svtv-data$c->base-nextstate svtv-data)))
                                            (svtv-data$c->cycle-phases svtv-data)
                                            base-fsm)))
                    `(:use ((:instance svex-envs-equivalent-implies-alist-eval-equiv
                             (x ,(hq values))
                             (y ,(hq values1)))
                            (:instance svtv-data$c-cycle-fsm-okp-necc
                             (values ,(hq values1))
                             (nextstate ,(hq nextstate1))
                             (svtv-data$c svtv-data)
                             (env (svex-alist-eval-equiv-envs-equivalent-witness
                                   ,(hq values) ,(hq values1)))))))))))


(local (defthm cycle-fsm-okp-implies-cycle-compile-nextstate-equiv
         (implies (svtv-data$c-cycle-fsm-okp svtv-data values1 nextstate1)
                  (b* (((svtv-fsm base-fsm) (svtv-data$c->base-fsm svtv-data))
                       ((mv ?values ?nextstate)
                        (svtv-cycle-compile (svex-identity-subst
                                             (svex-alist-keys (svtv-data$c->base-nextstate svtv-data)))
                                            (svtv-data$c->cycle-phases svtv-data)
                                            base-fsm)))
                    (svex-alist-eval-equiv! nextstate nextstate1)))
         :hints ((acl2::use-termhint
                  (b* (((svtv-fsm base-fsm) (svtv-data$c->base-fsm svtv-data))
                       ((mv ?values ?nextstate)
                        (svtv-cycle-compile (svex-identity-subst
                                             (svex-alist-keys (svtv-data$c->base-nextstate svtv-data)))
                                            (svtv-data$c->cycle-phases svtv-data)
                                            base-fsm)))
                    `(:use ((:instance svex-envs-equivalent-implies-alist-eval-equiv
                             (x ,(hq nextstate)) (y ,(hq nextstate1)))
                            (:instance svex-alist-eval-equiv!-when-svex-alist-eval-equiv
                             (x ,(hq nextstate)) (y ,(hq nextstate1)))
                            (:instance svtv-data$c-cycle-fsm-okp-necc
                             (values ,(hq values1))
                             (nextstate ,(hq nextstate1))
                             (svtv-data$c svtv-data)
                             (env (svex-alist-eval-equiv-envs-equivalent-witness
                                   ,(hq nextstate) ,(hq nextstate1)))))))))))
         
         
;; (local (defthm cycle-fsm-okp-equivalent-values-and-nextstate
;;          (implies (svtv-data$c-cycle-fsm-okp svtv-data values1 nextstate1)
;;                   (iff (svtv-data$c-cycle-fsm-okp svtv-data values nextstate)
;;                        (and (svex-alist-eval-equiv values1 values)
;;                             (svex-alist-eval-equiv! nextstate1 nextstate))))
;;          :hints (("goal" :cases ((svtv-data$c-cycle-fsm-okp svtv-data values1 nextstate)))
;;                  '(:cases ((svtv-data$c-cycle-fsm-okp svtv-data values nextstate1))))))


(define svtv-data-compute-cycle-fsm (svtv-data)
           :guard (and (svtv-data->base-fsm-validp svtv-data)
                       (not (svtv-data->pipeline-validp svtv-data)))
           :guard-hints (("goal" :do-not-induct t)
                         (and stable-under-simplificationp
                              '(:in-theory (e/d (svtv-data$ap svtv-fsm-to-cycle)
                                                (;; cycle-fsm-okp-equivalent-values
                                                 ;; cycle-fsm-okp-equivalent-nextstates
                                                 ))))
                         ;; (and stable-under-simplificationp
                         ;;      (let ((lit (assoc 'svex-alist-eval-equiv clause)))
                         ;;        (and lit
                         ;;             `(:expand (,lit)))))
                         )
           :returns new-svtv-data
           (b* (((svtv-fsm cycle-fsm)
                 (svtv-fsm-to-cycle (svtv-data->cycle-phases svtv-data)
                                    (svtv-data->base-fsm svtv-data)))
                (svtv-data (update-svtv-data->cycle-values cycle-fsm.values svtv-data))
                (svtv-data (update-svtv-data->cycle-nextstate cycle-fsm.nextstate svtv-data)))
             (update-svtv-data->cycle-fsm-validp t svtv-data))
           ///
           (defret svtv-data$c-get-of-<fn>
             (implies (and (equal key (svtv-data$c-field-fix k))
                           (not (equal key :cycle-values))
                           (not (equal key :cycle-nextstate))
                           (not (equal key :cycle-fsm-validp)))
                      (equal (svtv-data$c-get k new-svtv-data)
                             (svtv-data$c-get key svtv-data))))

           (defret cycle-fsm-validp-of-<fn>
             (svtv-data$c->cycle-fsm-validp new-svtv-data)))






       
