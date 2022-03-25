;;
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")
(include-book "step-time")
(include-book "coi/util/rewrite-equiv" :dir :system)

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

(in-theory (enable NOT-EXISTS-UAV-WITH-EVENT-FLIP-ON-EVENTS-EQUAL))
(in-theory (disable FORCE-EQUAL-DT-REWRITE))

(in-theory (enable NEXT-STEP))

(defthm escort-condition-val-1-next-step
  (IMPLIES (AND (ESCORT-CONDITION ENS)
                (WF-ENSEMBLE ENS))
           (ESCORT-CONDITION (VAL 1 (NEXT-STEP dt ens)))))

(defthm WF-ENSEMBLE-val-1-next-step
  (IMPLIES (AND (ESCORT-CONDITION ENS)
                (WF-ENSEMBLE ENS))
           (WF-ENSEMBLE (VAL 1 (NEXT-STEP dt ens)))))

(defthm decreasing-dt
  (IMPLIES (AND (ESCORT-CONDITION ENS)
                (WF-ENSEMBLE ENS)
                (<= (NNRAT-FIX DT)
                    (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
           (<= (VAL 0 (NEXT-STEP DT ENS))
               (MIN-TIME-TO-IMPACT-FOR-UAV I (VAL 1 (NEXT-STEP DT ENS)))))
  :hints ('(:cases ((impact-event-for-uav i ens)))
          (pattern::hint
           (IMPACT-EVENT-FOR-UAV I ENS)
           :in-theory (enable ESCORT-EVENT-FOR-UAV)
           :expand ((IMPACT-EVENT-FOR-UAV I ENS)
                    (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))))

(defthmd force-equal-dt-rewrite-2
  (implies
   (in-conclusion-check (equal z (nnrat-fix dt)) :top t)
   (iff (equal z (nnrat-fix dt))
        (hide (rewrite-equiv (equal (nnrat-fix dt) z)))))
  :hints (("goal" :expand (:free (x) (hide x)))))

;; This (now) works .. we need to update flip-uav-next-step
;;
(encapsulate
    ()

  (local (in-theory (disable
                     CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV
                     )))
  (local
   (defthmd flip-uav-update-location-all-helper
     (implies
      (and
       (ESCORT-CONDITION ENS)
       (WF-ENSEMBLE ENS)
       (lte-min-time-to-impending-impact-event dt ens)
       (implies
        (not (chasing-neighbor i ens))
        (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens))))
      (equal (FLIP-UAV I (update-location-all dt ens))
             (if (and (equal (nnrat-fix dt) (min-time-to-impact-for-uav i ens))
                      (impending-event-for-uav i ens))
                 (uav->flip (update-uav-location dt (ith-uav i ens)))
               (update-uav-location dt (ith-uav i ens)))))
     :hints (("Goal" :in-theory (disable impending-event-for-uav))
             (and stable-under-simplificationp
                  '(:in-theory (e/d (FLIP-UAV uav->flip) ())))
             (and stable-under-simplificationp
                  '(:expand (EVENT-FOR-UAV I (UPDATE-LOCATION-ALL DT ENS))))
             (pattern::hint*
              escort-condition-implies
              expand-CHASING-NEIGHBOR
              expand-min-time-to-impact-for-uav
              (pattern::hint
               (EQUAL (NNRAT-FIX DT) (MIN-TIME-TO-IMPACT-FOR-UAV I ENS))
               :expand ((MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
              )
             (and stable-under-simplificationp
                  '(:in-theory (e/d (IMPENDING-EVENT-FOR-UAV
                                     FORCE-EQUAL-DT-REWRITE
                                     FORCE-EQUAL-DT-REWRITE-2)
                                    nil)))
             )))

   (defthm flip-uav-update-location-all
     (implies
      (and
       (ESCORT-CONDITION ENS)
       (WF-ENSEMBLE ENS)
       (lte-min-time-to-impending-impact-event dt ens))
      (equal (FLIP-UAV I (update-location-all dt ens))
             (if (and (equal (nnrat-fix dt) (min-time-to-impact-for-uav i ens))
                      (impending-event-for-uav i ens))
                 (uav->flip (update-uav-location dt (ith-uav i ens)))
               (update-uav-location dt (ith-uav i ens)))))
     :hints (("Goal" :in-theory '(CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV
                                  LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-IMPLICATION-1)
              :use flip-uav-update-location-all-helper)))

   )

(defthm positive-ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT
  (implies
   (and
    (ESCORT-CONDITION ENS)
    (WF-ENSEMBLE ENS)
    (not (exists-uav-with-event ens)))
   (< 0 (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT ens)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT))))

(defthm event-for-uav-implies-zp-MIN-TIME-TO-IMPACT-FOR-UAV
  (implies
   (and
    (ESCORT-CONDITION ENS)
    (WF-ENSEMBLE ENS)
    (EVENT-FOR-UAV I ENS))
   (equal (MIN-TIME-TO-IMPACT-FOR-UAV I ENS) 0)))

(defthm event-for-uav-implies-impending-event-for-uav
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (event-for-uav i ens))
   (impending-event-for-uav i ens))
  :hints ('(:in-theory (enable impending-event-for-uav))
          (pattern::hint escort-condition-implies)))

(encapsulate
    ()

  (local (in-theory (disable CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV)))

  (local
   (defthmd EVENT-FOR-UAV-UPDATE-LOCATION-ALL-helper
     (implies
      (and
       (ESCORT-CONDITION ENS)
       (WF-ENSEMBLE ENS)
       (lte-min-time-to-impending-impact-event dt ens)
       (implies
        (not (chasing-neighbor i ens))
        (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens))))
      (iff (EVENT-FOR-UAV I (UPDATE-LOCATION-ALL DT ens))
           (and (impending-event-for-uav i ens)
                (equal (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))))
     :hints (;;(except "Subgoal 3.4.1.8")
             (pattern::hint*
              escort-condition-implies
              ;;ordering-rule
              (pattern::hint
               (:and
                (CHASING-NEIGHBOR I ENS)
                (EVENT-FOR-UAV I (UPDATE-LOCATION-ALL DT ENS)))
               :expand ((CHASING-NEIGHBOR I ENS)
                        (EVENT-FOR-UAV I (UPDATE-LOCATION-ALL DT ENS)))))
             (and stable-under-simplificationp
                  (not (cw "expanding IMPENDING-EVENT-FOR-UAV"))
                  '(:in-theory (enable IMPENDING-EVENT-FOR-UAV)))
             (and stable-under-simplificationp
                  (not (cw "expanding MIN-TIME-TO-IMPACT-FOR-UAV"))
                  '(:in-theory (enable MIN-TIME-TO-IMPACT-FOR-UAV)))
             (and stable-under-simplificationp
                  (not (cw "expanding EVENT-FOR-UAV"))
                  '(:in-theory (enable EVENT-FOR-UAV)))
             )))

  (defthm EVENT-FOR-UAV-UPDATE-LOCATION-ALL-lte
    (implies
     (and
      (ESCORT-CONDITION ENS)
      (WF-ENSEMBLE ENS)
      (lte-min-time-to-impending-impact-event dt ens))
     (iff (EVENT-FOR-UAV I (UPDATE-LOCATION-ALL DT ens))
          (and (impending-event-for-uav i ens)
               (equal (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))))
    :hints (("Goal" :use EVENT-FOR-UAV-UPDATE-LOCATION-ALL-helper
             :in-theory (enable lte-min-time-to-impending-impact-event-implication-chasing-neighbor))))

  )

(defthm implies-not-impending-impact-event-for-uav
  (implies
   (and
    (NOT (IMPENDING-ESCORT-FOR-UAV I ENS))
    (NOT (IMPENDING-EVENT-FOR-UAV I ENS)))
   (not (impending-impact-event-for-uav i ens)))
  :hints (("Goal" :in-theory (enable IMMINENT-EVENT-REDUCTION))))

(defthm update-uav-location-zero
  (implies
   (<= (NNRAT-FIX DT) 0)
   (equal (UPDATE-UAV-LOCATION dt uav)
          (uav-fix uav)))
  :hints (("GOal" :in-theory (enable UPDATE-UAV-LOCATION))))

(defthm flip-uav-next-step
  (implies
   (and
    (ESCORT-CONDITION ENS)
    (WF-ENSEMBLE ENS))
   (equal (FLIP-UAV I (VAL 1 (NEXT-STEP DT ENS)))
          (if (and (equal (min (nnrat-fix dt) (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT (FLIP-ON-EVENTS ENS)))
                          (MIN-TIME-TO-IMPACT-FOR-UAV I (flip-on-events ens)))
                   (impending-event-for-uav i (flip-on-events ens)))
              (uav->flip (ith-uav i (VAL 1 (NEXT-STEP DT ENS))))
            (ith-uav i (VAL 1 (NEXT-STEP DT ENS))))))
  :hints (("Goal" :in-theory (e/d (next-step)
                                  (UPDATE-UAV-LOCATION
                                   EQUAL-OF-UAV)))))

(defthm inductive-case
  (IMPLIES
   (AND
    (< 0 (NNRAT-FIX DT))
    (ESCORT-CONDITION ENS)
    (WF-ENSEMBLE ENS)
    (<= (NNRAT-FIX DT)
        (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
   (EQUAL (ITH-UAV I (UPDATE-LOCATION-ALL (VAL 0 (NEXT-STEP DT ENS))
                                          (VAL 1 (NEXT-STEP DT ENS))))
          (ITH-UAV I (UPDATE-LOCATION-ALL DT ens))))
  :hints (("Goal" :in-theory (enable flip-uav)
           :do-not-induct t)
          (pattern::hint
           (<= (NNRAT-FIX DT) (MIN-TIME-TO-IMPACT-FOR-UAV I ENS))
           :expand ((MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
          ))

(defthm ith-uav-val-1-next-step
  (implies
   (wf-ensemble ens)
   (equal (ITH-UAV I (VAL 1 (NEXT-STEP DT ENS)))
          (update-uav-location (min (nnrat-fix dt) (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT (FLIP-ON-EVENTS ENS))) (flip-uav i ens))))
  :hints (("Goal" :in-theory (e/d (next-step)
                                  (UPDATE-UAV-LOCATION
                                   equal-of-uav)))))

(defthm val-0-next-step
  (equal (val 0 (NEXT-STEP DT ENS))
         (- (nnrat-fix dt) (min (nnrat-fix dt) (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT (FLIP-ON-EVENTS ENS)))))
  :hints (("Goal" :in-theory (enable next-step))))


(defthm MIN-TIME-TO-IMPACT-FOR-UAV-NEXT-STEP
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens))
   (equal (MIN-TIME-TO-IMPACT-FOR-UAV I (VAL 1 (NEXT-STEP DT ENS)))
          (if (chasing-neighbor i (flip-on-events ens))
              (MIN-TIME-TO-IMPACT-FOR-UAV I (FLIP-ON-EVENTS ENS))
            (- (MIN-TIME-TO-IMPACT-FOR-UAV I (FLIP-ON-EVENTS ENS))
               (min (nnrat-fix dt) (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT (FLIP-ON-EVENTS ENS)))))))
  :hints (("Goal" :in-theory (enable NEXT-STEP))))


(defthm flip-on-events-is-closer-to-event
  (implies
   (and
    (wf-ensemble ens)
    (not (impact-EVENT-FOR-UAV I ens)))
   (<= (MIN-TIME-TO-IMPACT-FOR-UAV I (FLIP-ON-EVENTS ENS))
       (MIN-TIME-TO-IMPACT-FOR-UAV I ens)))
  ;;
  ;; So .. the usual problem with forward-chaining
  ;; structure into the hypothesis applies.
  ;;
  :hints (("GOal" :in-theory (enable ESCORT-EVENT-FOR-UAV
                                     IMPACT-EVENT-FOR-UAV
                                     flip-uav
                                     location-linear
                                     right-boundary-is-ordered-linear
                                     MIN-TIME-TO-IMPACT-FOR-UAV))))


(defthmd zp-min-time-to-impact-event-when-impact-event-rewrite
  (implies (and (escort-condition ens)
                (wf-ensemble ens)
                (impact-event-for-uav i ens))
           (equal (min-time-to-impact-for-uav i ens)
                  0))
  :hints (("goal" :in-theory (enable zp-min-time-to-impact-event-is-impact-event))))

(defthm update-location-update-location
  (equal (update-uav-location x (update-uav-location y uav))
         (update-uav-location (+ (nnrat-fix x) (nnrat-fix y)) uav)))

(defthm flip-on-events-is-closer-to-event-linear
  (implies
   (and
    (wf-ensemble ens)
    (not (impact-EVENT-FOR-UAV I ens)))
   (<= (MIN-TIME-TO-IMPACT-FOR-UAV I (FLIP-ON-EVENTS ENS))
       (MIN-TIME-TO-IMPACT-FOR-UAV I ens)))
  :rule-classes :linear)


(defthm always-smallest-min-time-to-impending-impact-is-smallest-better-trigger
  (implies
   (impending-event-for-uav k ens)
   (<= (always-smallest-min-time-to-impending-impact ens)
       (min-time-to-impact-for-uav k ens)))
  :hints (("Goal" :in-theory (enable impending-event-for-uav-implies-impending-impact-event-for-uav)))
  :rule-classes ((:linear :trigger-terms ((always-smallest-min-time-to-impending-impact ens)))))

(encapsulate
    ()
  (local (in-theory (disable min VAL-0-NEXT-STEP UPDATE-UAV-LOCATION equal-of-uav next-step)))
  (local (include-arithmetic))

  (defthm ith-uav-step-time-update-location-all
    (implies
     (and
      (step-time-always-terminates)
      (escort-condition ens)
      (wf-ensemble ens)
      (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I ens)))
     (equal (ith-uav i (step-time dt ens))
            (if (equal (nnrat-fix dt) 0)
                (ith-uav i ens)
              (update-uav-location dt (flip-uav i ens)))))
    :hints (("Goal"
             :induct (step-time dt ens)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable VAL-0-NEXT-STEP)))
            (and stable-under-simplificationp
                 '(:in-theory (enable min zp-min-time-to-impact-event-when-impact-event-rewrite)
                              :cases ((impact-EVENT-FOR-UAV I ens))))
            ))

  )

(defthm always-smallest-decreases-with-update-location-all
  (implies
   (and
    (WF-ENSEMBLE ENS)
    (ESCORT-CONDITION ENS)
    (<= (nnrat-fix dt) (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT ens)))
   (equal (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT (UPDATE-LOCATION-ALL dt ens))
          (- (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT ens)
             (nnrat-fix dt))))
  :hints (("Goal" :in-theory (enable smallest-impending-dt-index-properties
                                     ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT))))

(with-arithmetic
 (defthm okie-dokie
   (IMPLIES
    (AND
     (STEP-TIME-ALWAYS-TERMINATES)
     (ESCORT-CONDITION ENS)
     (WF-ENSEMBLE ENS))
    (EQUAL (STEP-TIME (+ (NNRAT-FIX A)
                         (VAL 0 (NEXT-STEP B ENS)))
                      (VAL 1 (NEXT-STEP B ENS)))
           (STEP-TIME (+ (NNRAT-FIX A) (NNRAT-FIX B))
                      (FLIP-ON-EVENTS ENS))))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable NOT-EXISTS-UAV-WITH-EVENT-UPDATE-LOCATION-ALL-ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT))
           '(:expand (STEP-TIME (+ (NNRAT-FIX A) (NNRAT-FIX B)) (FLIP-ON-EVENTS ENS)))
           (pattern::hint
            (:and
             (< (NNRAT-FIX B) (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT (FLIP-ON-EVENTS ENS)))
             (:term (STEP-TIME A (UPDATE-LOCATION-ALL B (FLIP-ON-EVENTS ENS)))))
            :expand ((STEP-TIME A (UPDATE-LOCATION-ALL B (FLIP-ON-EVENTS ENS)))))
           )
   ))


(defthm step-time-flip-on-events
  (implies
   (and
    (step-time-always-terminates)
    (wf-ensemble ens))
   (equal (step-time dt (flip-on-events ens))
          (if (equal (nnrat-fix dt) 0)
              (flip-on-events ens)
            (step-time dt ens))))
  :hints (("GOal" :do-not-induct t
           :expand (:free (ens) (step-time dt ens)))))

(defthmd introduce-flip-on-events-symbolp
  (implies
   (and
    (syntaxp (symbolp ens))
    (STEP-TIME-ALWAYS-TERMINATES)
    (WF-ENSEMBLE ENS))
   (equal (step-time dt ens)
          (if (equal (nnrat-fix dt) 0)
              ens
            (step-time dt (flip-on-events ens))))))

(defthmd introduce-flip-on-events-generic
  (implies
   (and
    (STEP-TIME-ALWAYS-TERMINATES)
    (WF-ENSEMBLE ENS))
   (equal (step-time dt ens)
          (if (equal (nnrat-fix dt) 0)
              ens
            (step-time dt (flip-on-events ens))))))

(theory-invariant
 (incompatible
  (:rewrite introduce-flip-on-events-symbolp)
  (:rewrite step-time-flip-on-events)))

(theory-invariant
 (incompatible
  (:rewrite introduce-flip-on-events-generic)
  (:rewrite step-time-flip-on-events)))

(defthm step-time-composition
  (implies
   (and
    (step-time-always-terminates)
    (escort-condition ens)
    (wf-ensemble ens))
   (equal (step-time a (step-time b ens))
          (step-time (+ (nnrat-fix a) (nnrat-fix b)) ens)))
  :hints (("Goal" :induct (step-time b ens)
           :do-not-induct t
           :in-theory '(okie-dokie
                        step-time-flip-on-events
                        (:REWRITE ESCORT-CONDITION-VAL-1-NEXT-STEP)
                        (:REWRITE NNRAT-EQUIV-OF-NNRAT-FIX)
                        (:REWRITE NNRAT-FIX-NNRAT-P)
                        (:DEFINITION |STEP-TIME-base|)
                        (:DEFINITION |STEP-TIME-test|)
                        (:FORWARD-CHAINING T-T-IMPLIES-NNRAT-P-T-NEXT-STEP)
                        (:REWRITE DEFUNG::OPEN-TRUE)
                        (:REWRITE UAV-LIST-FIX!-TO-UAV-LIST-FIX)
                        (:REWRITE UAV-LIST-FIX-UNDER-UAV-LIST-EQUIV)
                        (:CONGRUENCE NNRAT-EQUIV-1-IMPLIES-EQUAL-NEXT-STEP)
                        (:CONGRUENCE NNRAT-EQUIV-2-IMPLIES-EQUAL-NEXT-STEP)
                        (:CONGRUENCE UAV-LIST-EQUIV-3-IMPLIES-EQUAL-NEXT-STEP)
                        (:CONGRUENCE UAV-LIST-EQUIV-4-IMPLIES-EQUAL-NEXT-STEP)
                        (:INDUCTION STEP-TIME-INDUCTION)
                        (:INDUCTION STEP-TIME-INDUCTION-RULE)
                        (:REWRITE STEP-TIME-ALWAYS-TERMINATES-IMPLICATION)
                        (:DEFINITION STEP-TIME-DEFINITION)
                        (:REWRITE WF-ENSEMBLE-VAL-1-NEXT-STEP)
                        ))
          (and stable-under-simplificationp
               '(:in-theory (enable nnrat-fix)))
          ))

(with-arithmetic
 (defthmd step-time-decomposition
   (implies
    (and
     (step-time-always-terminates)
     (escort-condition ens)
     (wf-ensemble ens)
     (<= x (nnrat-fix dt))
     (nnrat-p x))
    (equal (step-time dt ens)
           (step-time (- (nnrat-fix dt) x) (step-time x ens))))
   :hints (("Goal" :in-theory (enable step-time-composition))))
 )

(theory-invariant
 (incompatible
  (:rewrite step-time-decomposition)
  (:rewrite step-time-composition)
  ))

;; (defun raw-set-ith-uav (i uav ens)
;;   (update-nth (uav-id-fix i) (uav-fix uav) (wf-ensemble-fix ens)))

;; (defthm ith-uav-update-nth
;;   (implies
;;    (uav-id-p j)
;;    (equal (ith-uav i (update-nth j uav ens))
;;           (if (equal (uav-id-fix i) j)
;;               (uav-fix uav)
;;             (ith-uav i ens))))
;;   :hints (("Goal" :do-not-induct t
;;            :in-theory (enable ith-uav))))

;; (defthm ith-uav-raw-set-ith-uav
;;   (implies
;;    (wf-ensemble ens)
;;    (equal (ith-uav i (raw-set-ith-uav j uav ens))
;;           (if (uav-id-equiv i j)
;;               (uav-fix uav)
;;             (ith-uav i ens)))))

;; (encapsulate
;;     ()

;;   (local
;;    (encapsulate
;;        ()

;;      (defthm force-rewrite
;;        (implies
;;         (in-conclusion-check (EQUAL (UAV->LOCATION UAV) (UAV->LOCATION (ITH-UAV I ENS))) :top t)
;;         (iff (EQUAL (UAV->LOCATION UAV) (UAV->LOCATION (ITH-UAV I ENS)))
;;              (hide (rewrite-equiv (equal (UAV->LOCATION UAV) (UAV->LOCATION (ITH-UAV I ENS)))))))
;;        :hints (("Goal" :expand (:free (x) (hide x)))))

;;      (defthmd hide-one-uav->id
;;        (equal (UPDATE-NTH (UAV->ID UAV) i ens)
;;               (update-nth (hide (UAV->ID UAV)) i ens))
;;        :hints (("Goal" :expand (:free (x) (hide x)))))


;;      (defthmd force-rewrite-2
;;        (iff (EQUAL (ORDERED-LOCATION-LIST-P-FIRST-WITNESS x) (UAV->ID UAV))
;;             (hide (rewrite-equiv (EQUAL (UAV->ID UAV) (ORDERED-LOCATION-LIST-P-FIRST-WITNESS x)))))
;;        :hints (("Goal" :expand (:free (x) (hide x)))))

;;      ))

;;   (defthm wf-ensemble-raw-set-ith-uav
;;     (implies
;;      (and
;;       (wf-ensemble ens)
;;       (uav-id-equiv i (uav->id uav))
;;       (equal (uav->location uav) (uav->location (ith-uav i ens))))
;;      (wf-ensemble (raw-set-ith-uav i uav ens)))
;;     :hints (("Goal" :in-theory (e/d (wf-ensemble
;;                                      sequential-id-list-p-reduction
;;                                      ORDERED-LOCATION-LIST-P-TO-ORDERED-LOCATION-LIST-QUANT-P
;;                                      ORDERED-LOCATION-LIST-QUANT-P
;;                                      location-linear
;;                                      )
;;                                     (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV)
;;                                     ))
;;             (and stable-under-simplificationp
;;                  '(:in-theory (enable hide-one-uav->id
;;                                       EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV)))
;;             (rewrite-equiv-hint UAV-ID-EQUIV)
;;             (and stable-under-simplificationp
;;                  '(:in-theory (enable force-rewrite-2)))
;;             ))

;;   )

;; (in-theory (disable raw-set-ith-uav))

;; (defun set-ith-uav (i uav ens)
;;   (wf-ensemble-fix (raw-set-ith-uav i uav ens)))

;; (defthm ith-uav-set-ith-uav
;;   (implies
;;    (and
;;     (wf-ensemble ens)
;;     (uav-id-equiv i (uav->id uav))
;;     (equal (uav->location uav) (uav->location (ith-uav i ens))))
;;    (equal (ith-uav j (set-ith-uav i uav ens))
;;           (if (equal (uav-id-fix j) (uav-id-fix i))
;;               (uav-fix uav)
;;             (ith-uav j ens)))))

;; (defthm set-ith-uav-ith-uav
;;   (implies
;;    (wf-ensemble ens)
;;    (equal (set-ith-uav i (ith-uav i ens) ens)
;;           ens))
;;   :hints (("Goal" :in-theory (enable equal-to-uav-list-equiv
;;                                      uav-list-equiv-pick-a-point-alt
;;                                      ))))

;; ===========================================================================

(def::un seq2 (x y)
  (declare (xargs :fty ((nnrat nnrat) nnrat)))
  (+ x y))

(defthm step-time-seq2
  (implies
   (and
    (step-time-always-terminates)
    (escort-condition ens)
    (wf-ensemble ens))
   (equal (step-time (seq2 a b) ens)
          (step-time a (step-time b ens)))))

(in-theory (disable STEP-TIME-COMPOSITION seq2))

(defthm flip-uav-i-flip-on-events
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens))
   (equal (FLIP-UAV I (FLIP-ON-EVENTS ENS))
          (flip-uav i ens)))
  :hints (("Goal" :in-theory (enable flip-uav))))

(defthmd step-time-min-time-to-impact-flip-helper
  (implies
   (and
    (step-time-always-terminates)
    (escort-condition ens)
    (wf-ensemble ens))
   (equal (ith-uav i (step-time (MIN-TIME-TO-IMPACT-FOR-UAV I (flip-on-events ens)) ens))
          (if (equal (MIN-TIME-TO-IMPACT-FOR-UAV I (flip-on-events ens)) 0)
              (ith-uav i ens)
            (update-uav-location (MIN-TIME-TO-IMPACT-FOR-UAV I (flip-on-events ens)) (flip-uav i ens)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable UPDATE-UAV-LOCATION
                               equal-of-uav))
          (pattern::hint
           (:term (step-time dt ens))
           :in-theory (disable UPDATE-UAV-LOCATION
                               equal-of-uav
                               step-time-flip-on-events)
           :use ((:instance step-time-flip-on-events
                            (dt dt)
                            (ens ens))))
          (rewrite-equiv-hint equal)
          ))

(defthmd step-time-min-time-to-impact-flip
  (implies
   (and
    (step-time-always-terminates)
    (escort-condition ens)
    (equal (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I (flip-on-events ens)))
    (wf-ensemble ens))
   (equal (ith-uav i (step-time dt ens))
          (if (equal (MIN-TIME-TO-IMPACT-FOR-UAV I (flip-on-events ens)) 0)
              (ith-uav i ens)
            (update-uav-location (MIN-TIME-TO-IMPACT-FOR-UAV I (flip-on-events ens)) (flip-uav i ens)))))
  :hints (("Goal" :in-theory '(nnrat-p-min-time-to-impact-for-uav
                               equal-nnrat-fix-to-nnrat-equiv-rewrite
                               step-time-min-time-to-impact-flip-helper
                               nnrat-equiv-is-an-equivalence
                               nnrat-equiv-implies-equal-step-time-1))))


(defthmd step-time-min-time-to-impact
  (implies
   (and
    (step-time-always-terminates)
    (escort-condition ens)
    (equal (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I ens))
    (wf-ensemble ens))
   (equal (ith-uav i (step-time dt ens))
          (if (equal (MIN-TIME-TO-IMPACT-FOR-UAV I ens) 0)
              (ith-uav i ens)
            (update-uav-location (MIN-TIME-TO-IMPACT-FOR-UAV I ens) (flip-uav i ens)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (step-time-min-time-to-impact-flip)
                           (UPDATE-UAV-LOCATION
                            equal-of-uav))
          )))

(in-theory (disable ith-uav-STEP-TIME-UPDATE-LOCATION-ALL))

;; ===========================================================================

(with-arithmetic
 (defthmd min-time-mirror
   (implies
    (and
     (escort-condition ens)
     (wf-ensemble ens)
     (impending-escort-for-uav i ens))
    (equal (min-time-to-impact-for-uav i ens)
           (if (< 0 (uav->direction (ith-uav i ens)))
               (min-time-to-impact-for-uav (+ 1 (uav-id-fix i)) ens)
             (min-time-to-impact-for-uav (+ -1 (uav-id-fix i)) ens))))
   :hints (("Goal" :in-theory (enable impending-escort-for-uav))
           (and stable-under-simplificationp
                '(:in-theory (enable min-time-to-impact-for-uav)))))
 )

(in-theory (disable OPEN-STEP-TIME-BASE step-time-definition))
(in-theory (disable STEP-TIME-MIN-TIME-TO-IMPACT))

(defthm not-impact-event-for-uav-implies-not-zero-MIN-TIME-TO-IMPACT-FOR-UAV
  (implies
   (and
    (IMPENDING-ESCORT-FOR-UAV I ENS)
    (not (ESCORT-EVENT-FOR-UAV I ENS))
    (ESCORT-CONDITION ENS)
    (WF-ENSEMBLE ENS))
   (not (equal 0 (MIN-TIME-TO-IMPACT-FOR-UAV I ENS))))
  :hints (("Goal" :in-theory (enable IMPACT-EVENT-FOR-UAV
                                     ZP-MIN-TIME-TO-IMPACT-EVENT-IS-IMPACT-EVENT)))
  :rule-classes (:forward-chaining))

(defthm rex
  (implies
   (and
    (IMPENDING-ESCORT-FOR-UAV I ENS)
    (NOT (EQUAL (MIN-TIME-TO-IMPACT-FOR-UAV I ENS) 0))
    (ESCORT-CONDITION ENS)
    (WF-ENSEMBLE ENS))
   (not (event-for-uav i ens)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable ZP-MIN-TIME-TO-IMPACT-EVENT-IS-IMPACT-EVENT))))

(in-theory (disable UPDATE-UAV-LOCATION))
;; (in-theory (disable cellular-escort-event-for-uav
;;                     cellular-escort-event-for-uav-left
;;                     cellular-escort-event-for-uav-right))

(defthm impending-escort-upper-bound
  (implies
   (and
    (IMPENDING-ESCORT-FOR-UAV I ENS)
    (< 0 (UAV->DIRECTION (ITH-UAV I ENS))))
   (< (uav-id-fix I) (+ -1 (N))))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable IMPENDING-ESCORT-FOR-UAV))))

(defthm impending-escort-lower-bound
  (implies
   (and
    (IMPENDING-ESCORT-FOR-UAV I ENS)
    (< (UAV->DIRECTION (ITH-UAV I ENS)) 0))
   (< 0 (uav-id-fix i)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable IMPENDING-ESCORT-FOR-UAV))))

;; (defthm uncellularize-ESCORT-EVENT-FOR-UAV-ith-uav-right
;;   (implies
;;    (and
;;     (syntaxp (symbolp ens))
;;     (wf-ensemble ens)
;;     (< (uav-id-fix i) (+ -1 (N)))
;;     (< 0 (UAV->DIRECTION (ITH-UAV I ENS))))
;;    (equal (CELLULAR-ESCORT-EVENT-FOR-UAV-RIGHT (ITH-UAV I ENS)
;;                                                (ITH-UAV (+ 1 (UAV-ID-FIX I)) ENS))
;;           (ESCORT-EVENT-FOR-UAV I ENS)))
;;   :hints (("Goal" :in-theory (enable CELLULARIZE-ESCORT-EVENT-FOR-UAV
;;                                      CELLULAR-ESCORT-EVENT-FOR-UAV))))

;; (defthm uncellularize-ESCORT-EVENT-FOR-UAV-ith-uav-left
;;   (implies
;;    (and
;;     (syntaxp (symbolp ens))
;;     (wf-ensemble ens)
;;     (< 0 (uav-id-fix i))
;;     (< (UAV->DIRECTION (ITH-UAV I ENS)) 0))
;;    (equal (CELLULAR-ESCORT-EVENT-FOR-UAV-LEFT (ITH-UAV (+ -1 (UAV-ID-FIX I)) ENS)
;;                                               (ITH-UAV I ENS))
;;           (ESCORT-EVENT-FOR-UAV I ENS)))
;;   :hints (("Goal" :in-theory (enable CELLULARIZE-ESCORT-EVENT-FOR-UAV
;;                                      CELLULAR-ESCORT-EVENT-FOR-UAV))))

(defthm uav->direction-update-uav-location
  (equal (UAV->DIRECTION (UPDATE-UAV-LOCATION dt uav))
         (uav->direction uav))
  :hints ('(:in-theory (enable update-uav-location))))

(defthm uav->id-update-uav-location
  (equal (UAV->ID (UPDATE-UAV-LOCATION dt uav))
         (uav->id uav))
  :hints ('(:in-theory (enable update-uav-location))))

(defthm uav->direction-flip-uav
  (equal (UAV->DIRECTION (flip-uav i ens))
         (if (EVENT-FOR-UAV I ENS)
             (- (uav->direction (ith-uav i ens)))
           (uav->direction (ith-uav i ens))))
  :hints ('(:in-theory (enable flip-uav uav->flip))))

(defthm not-event-implies-flip-uav-id
  (implies
   (and
    (not (event-for-uav i ens))
    (wf-ensemble ens))
   (equal (flip-uav i ens)
          (ith-uav i ens)))
  :hints (("Goal" :in-theory (enable flip-uav))))

(encapsulate
    ()

  (local (in-theory (disable next-step)))

  (def::un time-to-impact (i dt ens)
    (declare (xargs :measure (step-time-measure dt ens)
                    :fty ((uav-id nnrat uav-list) nnrat)))
    (if (not (step-time-domain dt ens)) 0
      (let ((dt  (nnrat-fix dt))
            (ens (uav-list-fix! ens)))
        (if (<= dt 0) 0
          (if (impact-event-for-uav i ens) 0
            (let ((delta (min dt (always-smallest-min-time-to-impending-impact (flip-on-events ens)))))
              (metlist ((dt ens) (next-step dt ens))
                (+ delta (time-to-impact i dt ens)))))))))

  (def::un lte-time-to-impact (i dt ens)
    (declare (xargs :measure (step-time-measure dt ens)
                    :fty ((uav-id nnrat uav-list) bool)))
    (if (not (step-time-domain dt ens)) nil
      (let ((dt  (nnrat-fix dt))
            (ens (uav-list-fix! ens)))
        (if (<= dt 0) t
          (if (impact-event-for-uav i ens) nil
            (metlist ((dt ens) (next-step dt ens))
              (lte-time-to-impact i dt ens)))))))

  (def::un lt-time-to-impact (i dt ens)
    (declare (xargs :measure (step-time-measure dt ens)
                    :fty ((uav-id nnrat uav-list) bool)))
    (if (not (step-time-domain dt ens)) nil
      (let ((dt  (nnrat-fix dt))
            (ens (uav-list-fix! ens)))
        (if (impact-event-for-uav i ens) nil
          (if (<= dt 0) t
            (metlist ((dt ens) (next-step dt ens))
              (lt-time-to-impact i dt ens)))))))

  )

(defthm time-to-impact-upper-bound
  (implies
   (step-time-always-terminates)
   (<= (time-to-impact i dt ens) (nnrat-fix dt)))
  :rule-classes ((:linear :trigger-terms ((time-to-impact i dt ens)))))

(defthm equal-always-smallest-is-lte-always-smallest
  (implies
   (EQUAL (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT ens) (NNRAT-FIX DT))
   (<= (nnrat-fix dt) (always-smallest-min-time-to-impending-impact ens)))
  :rule-classes (:forward-chaining
                 (:forward-chaining
                  :corollary
                  (implies
                   (EQUAL (NNRAT-FIX DT) (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT ens))
                   (<= (nnrat-fix dt) (always-smallest-min-time-to-impending-impact ens))))))

(with-arithmetic
 (defthm time-to-impact-upper-bound-strict
   (implies
    (and
     (wf-ensemble ens)
     (escort-condition ens)
     ;; If dt is larger than time-to-impact
     (not (lte-time-to-impact i dt ens))
     (< 0 (nnrat-fix dt))
     (step-time-always-terminates))
    (< (time-to-impact i dt ens) (nnrat-fix dt)))
   :hints (("Goal" :do-not-induct t
            :expand (LTE-TIME-TO-IMPACT I DT ENS)
            :induct (time-to-impact i dt ens))))
 )

(defthm not-gte-time-to-impact-implies-no-incremental-impact
  (implies
   (step-time-always-terminates)
   (or (not (lt-time-to-impact i dt ens))
       (lte-time-to-impact i dt ens)))
  :rule-classes ((:forward-chaining :trigger-terms ((lt-time-to-impact i dt ens)
                                                    (lte-time-to-impact i dt ens)))))

(defthm gte-and-lte-implies-equal-time-to-impact
  (implies
   (and
    (step-time-always-terminates)
    (not (lt-time-to-impact i dt ens))
    (lte-time-to-impact i dt ens))
   (equal (time-to-impact i dt ens)
          (nnrat-fix dt)))
  :rule-classes ((:forward-chaining :trigger-terms ((lt-time-to-impact i dt ens)
                                                    (lte-time-to-impact i dt ens)))))

(defthm lt-time-to-impact-not-impending-impact
  (implies
   (and
    (step-time-always-terminates)
    (wf-ensemble ens)
    (escort-condition ens)
    (lt-time-to-impact i dt ens))
   (not (impact-event-for-uav i (step-time dt ens)))))

(defthm ith-uav-step-time-lte-time-to-impact
  (implies
   (and
    (step-time-always-terminates)
    (wf-ensemble ens)
    (lte-time-to-impact i dt ens))
   (equal (ith-uav i (step-time dt ens))
          (UPDATE-LOCATION-UAV DT I ENS)))
  :hints (("Goal" :induct (lte-time-to-impact i dt ens)
           :in-theory (enable step-time-definition
                              update-uav-location))))

(with-arithmetic
 (defthm impending-impact-event-for-uav-after-time-to-impact
   (implies
    (and
     (wf-ensemble ens)
     (escort-condition ens)
     (step-time-always-terminates)
     (not (lt-time-to-impact i dt ens)))
    (impact-event-for-uav i (step-time (time-to-impact i dt ens) ens)))
   :hints (("Goal" :do-not-induct t
            :induct (time-to-impact i dt ens)
            :expand ((lt-TIME-TO-IMPACT I DT ENS)
                     (:free (x) (step-time x ens))))))
 )

(def::un ms-update-location-all (dt ens)
  (declare (xargs :fty ((nnrat uav-list) uav-list)))
  (step-time dt ens))

(def::signature ms-update-location-all (t wf-ensemble) wf-ensemble)
(def::signature ms-update-location-all (t wf-escort-p) escort-condition)

(with-arithmetic
 (in-theory (disable STEP-TIME-MIN-TIME-TO-IMPACT-FLIP))
 (defthmd open-ith-uav-step-time
  (implies
   (and
    (step-time-always-terminates)
    (wf-ensemble ens)
    (escort-condition ens))
   (equal (ith-uav i (step-time dt ens))
          (if (lte-time-to-impact i dt ens)
              (update-uav-location dt (ith-uav i ens))
            (ith-uav i (step-time (- (nnrat-fix dt) (time-to-impact i dt ens))
                                  (ms-update-location-all (time-to-impact i dt ens) ens))))))
  :hints (("Goal" :do-not-induct t)
          (and stable-under-simplificationp
               '(:in-theory (enable STEP-TIME-COMPOSITION)))))
 )

(defthm test-this
  (implies
   (and
    (wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (equal (uav->location (ith-uav i (update-location-all dt ens)))
          (+ (uav->location (ith-uav i ens))
             (* (uav->direction (ith-uav i ens))
                (nnrat-fix dt)))))
  :hints (("GOal" :in-theory (enable update-uav-location))))

(defthm lte-min-time-to-impact-implies-lte-time-to-impact
  (implies
   (and
    (step-time-always-terminates)
    (escort-condition ens)
    (wf-ensemble ens)
    (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I ens)))
   (lte-time-to-impact i dt ens))
  :hints (("Goal" :in-theory (enable next-step)
           :induct (lte-time-to-impact i dt ens))))

(in-theory (disable ms-update-location-all))

(defthm ith-uav-ms-update-location-all-impending-event
  (implies
   (and
    (step-time-always-terminates)
    (wf-ensemble ens)
    (escort-condition ens)
    (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I ens)))
   (equal (ith-uav i (ms-update-location-all dt ens))
          (UPDATE-LOCATION-UAV DT I ENS)))
  :hints (("Goal" :in-theory (enable ms-update-location-all))))

(defthm impending-implies-impending-right
  (implies
   (and
    (IMPENDING-ESCORT-FOR-UAV I ENS)
    (< 0 (UAV->DIRECTION (ITH-UAV I ENS)))
    (WF-ENSEMBLE ENS))
   (IMPENDING-EVENT-FOR-UAV (+ 1 (uav-id-fix I)) ENS))
  :hints (("Goal" :in-theory (enable IMPENDING-EVENT-FOR-UAV
                                     IMPENDING-ESCORT-FOR-UAV))
          (average-hint))
  :rule-classes (:forward-chaining))

(defthm impending-implies-impending-left
  (implies
   (and
    (IMPENDING-ESCORT-FOR-UAV I ENS)
    (< (UAV->DIRECTION (ITH-UAV I ENS)) 0)
    (WF-ENSEMBLE ENS))
   (IMPENDING-EVENT-FOR-UAV (+ -1 (uav-id-fix I)) ENS))
  :hints (("Goal" :in-theory (enable IMPENDING-EVENT-FOR-UAV
                                     IMPENDING-ESCORT-FOR-UAV))
          (average-hint))
  :rule-classes (:forward-chaining))

(encapsulate
    ()

  (local (in-theory (disable next-step)))

  (def::un time-to-event (i dt ens)
    (declare (xargs :measure (step-time-measure dt ens)
                    :fty ((uav-id nnrat uav-list) nnrat)))
    (if (not (step-time-domain dt ens)) 0
      (let ((dt  (nnrat-fix dt))
            (ens (uav-list-fix! ens)))
        (if (<= dt 0) 0
          (if (event-for-uav i ens) 0
            (let ((alt-ens (flip-on-events ens)))
              (let ((delta (min dt
                                (always-smallest-min-time-to-impending-impact alt-ens))))
                (metlist ((dt ens) (next-step dt ens))
                  (+ delta (time-to-event i dt ens))))))))))

  (def::un lte-time-to-event (i dt ens)
    (declare (xargs :measure (step-time-measure dt ens)
                    :fty ((uav-id nnrat uav-list) bool)))
    (if (not (step-time-domain dt ens)) nil
      (let ((dt  (nnrat-fix dt))
            (ens (uav-list-fix! ens)))
        (if (<= dt 0) t
          (if (event-for-uav i ens) nil
            (metlist ((dt ens) (next-step dt ens))
              (lte-time-to-event i dt ens)))))))

  (def::un lt-time-to-event (i dt ens)
    (declare (xargs :measure (step-time-measure dt ens)
                    :fty ((uav-id nnrat uav-list) bool)))
    (if (not (step-time-domain dt ens)) nil
      (let ((dt  (nnrat-fix dt))
            (ens (uav-list-fix! ens)))
        (if (event-for-uav i ens) nil
          (if (<= dt 0) t
            (metlist ((dt ens) (next-step dt ens))
              (lt-time-to-event i dt ens)))))))
  )

(defthm ith-uav-step-time-lte-time-to-event
  (implies
   (and
    (step-time-always-terminates)
    (wf-ensemble ens)
    (lte-time-to-event i dt ens))
   (equal (ith-uav i (step-time dt ens))
          (UPDATE-LOCATION-UAV DT I ENS)))
  :hints (("Goal" :induct (lte-time-to-event i dt ens)
           :in-theory (enable step-time-definition
                              update-uav-location))))

(defthm time-to-event-upper-bound
  (implies
   (step-time-always-terminates)
   (<= (time-to-event i dt ens)
       (nnrat-fix dt)))
  :rule-classes ((:linear :trigger-terms ((time-to-event i dt ens)))))

(with-arithmetic
 (defthm event-for-uav-after-time-to-event
   (implies
    (and
     (wf-ensemble ens)
     (escort-condition ens)
     (step-time-always-terminates)
     (not (lt-time-to-event i dt ens)))
    (event-for-uav i (step-time (time-to-event i dt ens) ens)))
   :hints (("Goal" :do-not-induct t
            :induct (time-to-event i dt ens)
            :expand ((lt-TIME-TO-event I DT ENS)
                     (:free (x) (step-time x ens))))))
 )

(defthm uav-location-update-uav-location
  (equal (UAV->LOCATION (UPDATE-UAV-LOCATION dt uav))
         (uav-location-fix (+ (* (uav->direction uav) (nnrat-fix dt))
                              (uav->Location uav))))
  :hints (("GOal" :in-theory (enable UPDATE-UAV-LOCATION))))

(defthm uav-location-update-location-uav
  (equal (UAV->LOCATION (UPDATE-LOCATION-UAV DT I ENS))
         (uav-location-fix (+ (* (uav->direction (ith-uav i ens)) (nnrat-fix dt))
                              (uav->Location (ith-uav i ens)))))
  :hints (("GOal" :in-theory (enable UPDATE-LOCATION-UAV))))

(defthm uav-right-boundary-update-uav-location
  (equal (uav-right-boundary (update-uav-location dt uav))
         (uav-right-boundary uav))
  :hints (("Goal" :in-theory (enable update-uav-location))))

(defthm uav-left-boundary-update-uav-location
  (equal (uav-left-boundary (update-uav-location dt uav))
         (uav-left-boundary uav))
  :hints (("Goal" :in-theory (enable UAV-LEFT-BOUNDARY
                                     update-uav-location))))


(defthm uav-right-boundary-flip-uav
  (equal (uav-right-boundary (FLIP-UAV I ENS))
         (uav-right-boundary (ith-uav i ens)))
  :hints (("Goal" :in-theory (enable flip-uav))))

(defthm uav-left-boundary-flip-uav
  (equal (uav-left-boundary (FLIP-UAV I ENS))
         (uav-left-boundary (ith-uav i ens)))
  :hints (("Goal" :in-theory (enable flip-uav))))

(defthm normalize-additive-constants-under-equality
  (implies
   (and
    (syntaxp (and (quotep x) (quotep z)))
    (and (rationalp x) (rationalp y) (rationalp z))
    (equal a (+ z (- x))))
   (and (iff (EQUAL (+ x y) z)
             (equal y a))
        (iff (EQUAL z (+ x y))
             (equal y a)))))

(defthm normalize-additive-constants-under-<
  (implies
   (and
    (syntaxp (and (quotep x) (quotep z)))
    (and (rationalp x) (rationalp y) (rationalp z))
    (equal a (+ z (- x))))
   (and (iff (< (+ x y) z)
             (< y a))
        (iff (< z (+ x y))
             (< a y)))))

;; ==========================================================================
;;
;; These lemmas should be useful when we go to prove
;; convergence (periodicity)
;;
;; ==========================================================================

(defthm distance-to-right-boundary-is-lte-time-to-event
  (implies
   (and
    (step-time-always-terminates)
    (wf-escort-p ens)
    (< 0 (uav->direction (ith-uav i ens)))
    (<= (uav->location (ith-uav i ens))
        (uav-right-boundary (ith-uav i ens)))
    (<= (nnrat-fix dt) (- (uav-right-boundary (ith-uav i ens))
                          (uav->location (ith-uav i ens)))))
   (lte-time-to-event i dt ens))
  :hints (("Goal" :induct (lte-time-to-event i dt ens)
           :do-not-induct t)))

(defthm step-to-right-boundary
  (implies
   (and
    (step-time-always-terminates)
    (wf-escort-p ens)
    (< 0 (uav->direction (ith-uav i ens)))
    (<= (uav->location (ith-uav i ens))
        (uav-right-boundary (ith-uav i ens)))
    (<= (nnrat-fix dt) (- (uav-right-boundary (ith-uav i ens))
                          (uav->location (ith-uav i ens)))))
   (equal (ith-uav i (step-time dt ens))
          (UPDATE-LOCATION-UAV DT I ENS))))

(defthm how-long??
  (equal (EVENT-FOR-UAV (UAV-ID-FIX I) ENS)
         (EVENT-FOR-UAV I ENS)))

(defthm this-is-getting-ridiculous
  (equal (ITH-UAV (UAV-ID-FIX I) ENS)
         (ith-uav i ens)))

;; I was having problems here again ..
;; remove the above rules and do:
;; :monitor (:rewrite step-to-right-boundary) '(:target :go)
;;
(defthm flip-step-to-right-boundary
  (implies
   (and
    (step-time-always-terminates)
    (wf-escort-p ens)
    (< (uav->direction (ith-uav i ens)) 0)
    (event-for-uav i ens)
    (<= (uav->location (ith-uav i ens))
        (uav-right-boundary (ith-uav i ens)))
    (<= (nnrat-fix dt) (- (uav-right-boundary (ith-uav i ens))
                          (uav->location (ith-uav i ens)))))
   (equal (ith-uav i (step-time dt ens))
          (if (equal (nnrat-fix dt) 0)
              (ith-uav i ens)
            (UPDATE-UAV-LOCATION DT (uav->flip (ith-uav i ens))))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (flip-uav
                              update-location-uav
                              introduce-flip-on-events-symbolp)
                           (step-time-flip-on-events)))))

(defthm distance-to-left-boundary-is-lte-time-to-event
  (implies
   (and
    (step-time-always-terminates)
    (wf-escort-p ens)
    (< (uav->direction (ith-uav i ens)) 0)
    (<= (uav-left-boundary (ith-uav i ens))
        (uav->location (ith-uav i ens)))
    (<= (nnrat-fix dt) (- (uav->location (ith-uav i ens))
                          (uav-left-boundary (ith-uav i ens)))))
   (lte-time-to-event i dt ens))
  :hints (("Goal" :induct (lte-time-to-event i dt ens)
           :do-not-induct t)))

(defthm step-to-left-boundary
  (implies
   (and
    (step-time-always-terminates)
    (wf-escort-p ens)
    (< (uav->direction (ith-uav i ens)) 0)
    (<= (uav-left-boundary (ith-uav i ens))
        (uav->location (ith-uav i ens)))
    (<= (nnrat-fix dt) (- (uav->location (ith-uav i ens))
                          (uav-left-boundary (ith-uav i ens)))))
   (equal (ith-uav i (step-time dt ens))
          (UPDATE-LOCATION-UAV DT I ENS))))

(defthm flip-step-to-left-boundary
  (implies
   (and
    (step-time-always-terminates)
    (wf-escort-p ens)
    (< 0 (uav->direction (ith-uav i ens)))
    (event-for-uav i ens)
    (<= (uav-left-boundary (ith-uav i ens))
        (uav->location (ith-uav i ens)))
    (<= (nnrat-fix dt) (- (uav->location (ith-uav i ens))
                          (uav-left-boundary (ith-uav i ens)))))
   (equal (ith-uav i (step-time dt ens))
          (if (equal (nnrat-fix dt) 0)
              (ith-uav i ens)
            (UPDATE-UAV-LOCATION DT (uav->flip (ith-uav i ens))))))
  :hints (("Goal" :do-not-induct t
           :cases ((equal (N) 1))
           :in-theory (e/d (flip-uav
                            update-location-uav
                            introduce-flip-on-events-symbolp)
                           (step-time-flip-on-events)))))

;; ==========================================================================

(defthm time-to-event-is-bounded-by-distance-to-boundary-right
  (implies
   (and
    (step-time-always-terminates)
    (wf-ensemble ens)
    (escort-condition ens)
    (< 0 (uav->direction (ith-uav i ens))))
   (<= (time-to-event i dt ens)
       (- (right-perimeter-boundary) (uav->location (ith-uav i ens)))))
  :hints (("Goal" :do-not-induct t
           :induct (time-to-event i dt ens))
          (pattern::hint
           (equal (time-to-event i dt ens) 0)
           :expand ((time-to-event i dt ens)))
          ;;
          ;; This should have worked on its own
          ;;
          (pattern::hint
           (< (+ (RIGHT-PERIMETER-BOUNDARY)
                 (* -1 (UAV->LOCATION (ITH-UAV I ENS))))
              (NNRAT-FIX DT))
           :name upper-bound
           :in-theory (disable lte-min-time-to-impending-impact-event-bounded-by-location-right)
           :use ((:instance lte-min-time-to-impending-impact-event-bounded-by-location-right
                            (i i)
                            (dt dt)
                            (ens (FLIP-ON-EVENTS ENS)))))
          (pattern::hint
           (< (+ (RIGHT-PERIMETER-BOUNDARY)
                 (* -1 (UAV->LOCATION (ITH-UAV I ENS))))
              (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT (FLIP-ON-EVENTS ENS)))
           :name upper-bound
           :in-theory (disable lte-min-time-to-impending-impact-event-bounded-by-location-right)
           :use ((:instance lte-min-time-to-impending-impact-event-bounded-by-location-right
                            (i i)
                            (dt (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT (FLIP-ON-EVENTS ENS)))
                            (ens (FLIP-ON-EVENTS ENS)))))

          ))

(defthm time-to-event-is-bounded-by-distance-to-boundary-left
  (implies
   (and
    (step-time-always-terminates)
    (wf-ensemble ens)
    (escort-condition ens)
    (< (uav->direction (ith-uav i ens)) 0))
   (<= (time-to-event i dt ens)
       (- (uav->location (ith-uav i ens)) (left-perimeter-boundary))))
  :hints (("Goal" :do-not-induct t
           :induct (time-to-event i dt ens))
          (pattern::hint
           (equal (time-to-event i dt ens) 0)
           :expand ((time-to-event i dt ens)))
          (pattern::hint
           (< (+ (* -1 (LEFT-PERIMETER-BOUNDARY))
                 (UAV->LOCATION (ITH-UAV I ENS)))
              (NNRAT-FIX DT))
           :name lower-bound
           :in-theory (disable lte-min-time-to-impending-impact-event-bounded-by-location-left)
           :use ((:instance lte-min-time-to-impending-impact-event-bounded-by-location-left
                            (i i)
                            (dt dt)
                            (ens (FLIP-ON-EVENTS ENS)))))
          (pattern::hint
           (< (+ (* -1 (LEFT-PERIMETER-BOUNDARY))
                 (UAV->LOCATION (ITH-UAV I ENS)))
              (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT (FLIP-ON-EVENTS ENS)))
           :name lower-bound-2
           :in-theory (disable lte-min-time-to-impending-impact-event-bounded-by-location-left)
           :use ((:instance lte-min-time-to-impending-impact-event-bounded-by-location-left
                            (i i)
                            (dt (ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT (FLIP-ON-EVENTS ENS)))
                            (ens (FLIP-ON-EVENTS ENS)))))
          ))


(with-arithmetic
 (defthmd not-lte-time-to-event-left
   (implies
    (and
     (step-time-always-terminates)
     (wf-ensemble ens)
     (escort-condition ens)
     (< (uav->direction (ith-uav i ens)) 0)
     (force (<= (- (uav->location (ith-uav i ens)) (left-perimeter-boundary))
                (nnrat-fix dt))))
    (not (lt-time-to-event i dt ens)))
   :hints (("GOal" :induct (lt-time-to-event i dt ens))
           (average-hint)
           )))

(with-arithmetic
 (defthmd not-lte-time-to-event-right
   (implies
    (and
     (step-time-always-terminates)
     (wf-ensemble ens)
     (escort-condition ens)
     (< 0 (uav->direction (ith-uav i ens)))
     (force (<= (- (right-perimeter-boundary) (uav->location (ith-uav i ens)) )
                (nnrat-fix dt))))
    (not (lt-time-to-event i dt ens)))
   :hints (("GOal" :induct (lt-time-to-event i dt ens))
           (average-hint)
           )))

(def::und TEE ()
  (declare (xargs :fty (() nnrat)))
  (- (right-perimeter-boundary)
     (left-perimeter-boundary)))

(defthm not-lte-time-to-event
  (implies
   (and
    (step-time-always-terminates)
    (wf-ensemble ens)
    (escort-condition ens))
   (not (lt-time-to-event i (TEE) ens)))
  :hints (("GOal" :do-not-induct t
           :in-theory (enable not-lte-time-to-event-left
                              not-lte-time-to-event-right)
           :cases ((< 0 (uav->direction (ith-uav i ens)))))
          (pattern::hint
           (< (TEE) a)
           :in-theory (enable TEE))
          ))

(defthm not-lt-time-to-event-property
  (implies
   (not (lt-time-to-event i dt ens))
   (<= (time-to-event i dt ens)
       (nnrat-fix dt)))
  :rule-classes ((:linear :trigger-terms ((time-to-event i dt ens)))))

(with-arithmetic
 (defthmd open-step-time-on-TEE
   (implies
    (and
     (wf-escort-p ens)
     (step-time-always-terminates))
    (equal (step-time (TEE) ens)
           (step-time (- (TEE) (time-to-event i (TEE) ens))
                      (step-time (time-to-event i (TEE) ens) ens))))
   :hints (("Goal" :in-theory (enable STEP-TIME-COMPOSITION))))
 )

;;
;; OK .. so we know we will see an event after (TEE) ticks ..
;;
(defthm event-for-uav-time-to-event-TEE
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (step-time-always-terminates))
   (event-for-uav i (step-time (time-to-event i (TEE) ens) ens))))

