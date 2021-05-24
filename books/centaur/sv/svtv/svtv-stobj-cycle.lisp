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

   (defthm base-fsm-eval-equiv-congruence-of-svtv-cycle-compile-outs
     (implies (base-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 0 (svtv-cycle-compile prev-st phases fsm simp))
                                     (mv-nth 0 (svtv-cycle-compile prev-st phases fsm-equiv simp))))
     :hints((witness) (witness))
     :rule-classes :congruence)

   (defthm base-fsm-eval-equiv-congruence-of-svtv-cycle-compile-nextst
     (implies (base-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv! (mv-nth 1 (svtv-cycle-compile prev-st phases fsm simp))
                                     (mv-nth 1 (svtv-cycle-compile prev-st phases fsm-equiv simp))))
     :hints((witness) (witness))
     :rule-classes :congruence)
   
   (defthm prev-st-congruence-of-svtv-cycle-compile-outs
     (implies (svex-alist-eval-equiv prev-st prev-st-equiv)
              (svex-alist-eval-equiv (mv-nth 0 (svtv-cycle-compile prev-st phases fsm simp))
                                     (mv-nth 0 (svtv-cycle-compile prev-st-equiv phases fsm simp))))
     :hints((witness :ruleset svex-alist-eval-equiv-witnessing) ;; (witness)
            (witness :ruleset svex-eval-equiv-witnessing)
            )
     :rule-classes :congruence)

   (defthm prev-st-congruence-of-svtv-cycle-compile-nextst
     (implies (svex-alist-eval-equiv prev-st prev-st-equiv)
              (svex-alist-eval-equiv (mv-nth 1 (svtv-cycle-compile prev-st phases fsm simp))
                                     (mv-nth 1 (svtv-cycle-compile prev-st-equiv phases fsm simp))))
     :hints((witness :ruleset svex-alist-eval-equiv-witnessing) ;; (witness)
            (witness :ruleset svex-eval-equiv-witnessing)
            )
     :rule-classes :congruence)

   (defthm base-fsm-eval-equiv-congruence-of-svtv-cycle-compile-outs
     (implies (base-fsm-eval-equiv fsm fsm-equiv)
              (svex-alist-eval-equiv (mv-nth 0 (svtv-cycle-compile prev-st phases fsm simp))
                                     (mv-nth 0 (svtv-cycle-compile prev-st phases fsm-equiv simp))))
     :hints((witness) (witness))
     :rule-classes :congruence)


   (defcong svex-alist-eval-equiv base-fsm-eval-equiv (base-fsm values nextstate) 1
     :hints(("Goal" :in-theory (enable base-fsm-eval-equiv))))

   (defcong svex-alist-eval-equiv! base-fsm-eval-equiv (base-fsm values nextstate) 2
     :hints(("Goal" :in-theory (enable base-fsm-eval-equiv))))



   

   (defcong base-fsm-eval-equiv base-fsm-eval-equiv (base-fsm-to-cycle phases fsm simp) 2
     :hints(("Goal" :in-theory (enable base-fsm-to-cycle))))))

  


(local (in-theory (disable hons-dups-p)))


(local (defthm cycle-fsm-okp-of-base-fsm-to-cycle
         (b* (((base-fsm base-fsm) (svtv-data$c->phase-fsm svtv-data))
              ((mv values nextstate)
               (svtv-cycle-compile (svex-identity-subst
                                    (svex-alist-keys base-fsm.nextstate))
                                   (svtv-data$c->cycle-phases svtv-data)
                                   base-fsm simp)))
           (svtv-data$c-cycle-fsm-okp svtv-data (make-base-fsm :values values :nextstate nextstate)))
         :hints(("Goal" :in-theory (enable svtv-data$c-cycle-fsm-okp)))))

(local (defthm cycle-fsm-okp-implies-cycle-compile-values-equiv
         (implies (svtv-data$c-cycle-fsm-okp svtv-data cycle-fsm)
                  (b* (((base-fsm base-fsm) (svtv-data$c->phase-fsm svtv-data))
                       ((mv ?values ?nextstate)
                        (svtv-cycle-compile (svex-identity-subst
                                             (svex-alist-keys base-fsm.nextstate))
                                            (svtv-data$c->cycle-phases svtv-data)
                                            base-fsm simp)))
                    (base-fsm-eval-equiv (make-base-fsm :values values :nextstate nextstate) cycle-fsm)))
         :hints ((acl2::use-termhint
                  (b* (((base-fsm base-fsm) (svtv-data$c->phase-fsm svtv-data))
                       ((base-fsm cycle-fsm))
                       ((mv ?values ?nextstate)
                        (svtv-cycle-compile (svex-identity-subst
                                             (svex-alist-keys base-fsm.nextstate))
                                            (svtv-data$c->cycle-phases svtv-data)
                                            base-fsm simp)))
                    `(:use ((:instance svex-envs-equivalent-implies-alist-eval-equiv
                             (x ,(hq values))
                             (y ,(hq cycle-fsm.values)))
                            (:instance svex-envs-equivalent-implies-alist-eval-equiv
                             (x ,(hq nextstate))
                             (y ,(hq cycle-fsm.nextstate)))
                            (:instance svtv-data$c-cycle-fsm-okp-necc
                             (cycle-fsm ,(hq cycle-fsm))
                             (svtv-data$c svtv-data)
                             (env (svex-alist-eval-equiv-envs-equivalent-witness
                                   ,(hq values) ,(hq values1)))))
                      :in-theory (enable base-fsm-eval-equiv
                                         svex-alist-eval-equiv!-when-svex-alist-eval-equiv)))))))
         
         
;; (local (defthm cycle-fsm-okp-equivalent-values-and-nextstate
;;          (implies (svtv-data$c-cycle-fsm-okp svtv-data values1 nextstate1)
;;                   (iff (svtv-data$c-cycle-fsm-okp svtv-data values nextstate)
;;                        (and (svex-alist-eval-equiv values1 values)
;;                             (svex-alist-eval-equiv! nextstate1 nextstate))))
;;          :hints (("goal" :cases ((svtv-data$c-cycle-fsm-okp svtv-data values1 nextstate)))
;;                  '(:cases ((svtv-data$c-cycle-fsm-okp svtv-data values nextstate1))))))



;; (defcong svex-alist-eval-equiv! equal (svex-alist-keys x) 1)

(define svtv-data-compute-cycle-fsm (svtv-data (simp svex-simpconfig-p))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatnorm-validp svtv-data)
              (not (svtv-data->pipeline-validp svtv-data)))
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable base-fsm-to-cycle)))
  :returns new-svtv-data
  (b* (((base-fsm cycle-fsm)
        (base-fsm-to-cycle (svtv-data->cycle-phases svtv-data)
                           (svtv-data->phase-fsm svtv-data)
                           simp))
       (svtv-data (update-svtv-data->cycle-fsm cycle-fsm svtv-data)))
    (update-svtv-data->cycle-fsm-validp t svtv-data))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :cycle-fsm))
                  (not (equal key :cycle-fsm-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret cycle-fsm-validp-of-<fn>
    (svtv-data$c->cycle-fsm-validp new-svtv-data)))



(define svtv-data-maybe-compute-cycle-fsm ((phases svtv-cyclephaselist-p)
                                           svtv-data
                                           (simp svex-simpconfig-p)
                                           &key (skip 'nil))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatnorm-validp svtv-data))
  :returns new-svtv-data
  (if (and (equal (svtv-cyclephaselist-fix phases)
                  (svtv-data->cycle-phases svtv-data))
           (svtv-data->cycle-fsm-validp svtv-data))
      svtv-data
    (b* ((svtv-data (update-svtv-data->cycle-fsm-validp nil svtv-data))
         (svtv-data (update-svtv-data->cycle-phases phases svtv-data))
         ((when skip) svtv-data)
         (svtv-data (update-svtv-data->pipeline-validp nil svtv-data)))
      (svtv-data-compute-cycle-fsm svtv-data simp)))
  ///
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :cycle-fsm))
                  (not (equal key :cycle-fsm-validp))
                  (not (equal key :pipeline-validp))
                  (not (equal key :cycle-phases)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret cycle-fsm-validp-of-<fn>
    (implies (not skip)
             (svtv-data$c->cycle-fsm-validp new-svtv-data)))

  (defret cycle-phases-validp-of-<fn>
    (equal (svtv-data$c->cycle-phases new-svtv-data)
           (svtv-cyclephaselist-fix phases))))


       
