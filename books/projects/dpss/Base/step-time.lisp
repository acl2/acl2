;;
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")
(include-book "flip")
(include-book "step")
(include-book "coi/defung/defung" :dir :system)

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

(defthm equal-common-addend-reduction
  (implies
   (and (rationalp x) (rationalp a) (rationalp b))
   (iff (equal (+ x a)
               (+ x b))
        (equal a b))))

;; ==================================================================

(in-theory (disable LIST::CONSP-WHEN-LEN-IS-KNOWN-AND-POSITIVE))

(encapsulate
    ()

  (local
   (defthmd not-exists-uav-with-event-update-location-all-helper
     (implies
      (and
       (hide (always-true k))
       (escort-condition ens)
       ;;(homogenous-escort-direction ens)
       (wf-ensemble ens)
       (< (nnrat-fix dt) (always-smallest-min-time-to-impending-impact ens)))
      (not (event-for-uav k (update-location-all dt ens))))
     :hints (("Goal" :in-theory (e/d (event-for-uav
                                      IMPENDING-IMPACT-EVENT-FOR-UAV
                                      MIN-TIME-TO-IMPACT-FOR-UAV)
                                     (always-smallest-min-time-to-impending-impact-is-smallest))
              :use always-smallest-min-time-to-impending-impact-is-smallest)
             (pattern::hint
              escort-condition-implies
              )
             (average-hint)
             )))

  (defthmd not-exists-uav-with-event-update-location-all-always-smallest-min-time-to-impending-impact
    (implies
     (and
      (escort-condition ens)
      ;;(homogenous-escort-direction ens)
      (wf-ensemble ens)
      (< (nnrat-fix dt) (always-smallest-min-time-to-impending-impact ens)))
     (not (exists-uav-with-event (update-location-all dt ens))))
    :hints (("Goal" :expand (:Free (x) (hide x))
             :in-theory (enable exists-uav-with-event)
             :use (:instance not-exists-uav-with-event-update-location-all-helper
                             (k (EXISTS-UAV-WITH-EVENT-WITNESS (UPDATE-LOCATION-ALL DT ENS)))))))

  )

(in-theory (disable FORCE-EQUAL-DT-REWRITE))
(in-theory (disable IMPENDING-ESCORT-FOR-UAV IMPENDING-EVENT-FOR-UAV))

(defthm update-location-all-update-location-all
  (implies
   (equal (len ens) (N))
   (equal (UPDATE-LOCATION-ALL A (UPDATE-LOCATION-ALL B ens))
          (update-location-all (+ (nnrat-fix a) (nnrat-fix b)) ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable equal-to-uav-list-equiv))
          (and stable-under-simplificationp
               '(:in-theory (e/d (uav-list-equiv-pick-a-point-alt
                                  uav-location-fix
                                  uav-location-p)
                                 ())))
          (pattern::hint
           (:term (uav->direction z))
           :cases ((equal (uav->direction z) 1)))))

(def::un next-step (dt ens)
  (declare (xargs :fty ((nnrat uav-list) rational uav-list)))
  (let ((ens (flip-on-events ens)))
    (let ((step (min dt (always-smallest-min-time-to-impending-impact ens))))
      (let ((ens (update-location-all step ens)))
        (mvlist (- dt step) ens)))))

(def::signature next-step (t wf-ensemble) t wf-ensemble)
(def::signature next-step (t t) nnrat-p t)

(defthm escort-condition-next-step-invariant
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens))
   (escort-condition (val 1 (next-step dt ens)))))

(defthm not-equal-always-smallest-means-greater
  (implies
   (and
    (impending-impact-event-for-uav i ens)
    (not (equal (always-smallest-min-time-to-impending-impact ens) (MIN-TIME-TO-IMPACT-FOR-UAV I ENS))))
   (< (always-smallest-min-time-to-impending-impact ens) (MIN-TIME-TO-IMPACT-FOR-UAV I ENS))))

(defthm less-than-least-implies-less-than-any
  (implies
   (and
    (impending-impact-event-for-uav i ens)
    (< x (always-smallest-min-time-to-impending-impact ens)))
   (< x (MIN-TIME-TO-IMPACT-FOR-UAV I ENS))))



(defthmd positive-min-time-to-impact-event-implies-not-impact-event
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (< 0 (min-time-to-impact-for-uav i ens)))
   (not (impact-event-for-uav i ens)))
  :hints (("Goal" :in-theory (enable min-time-to-impact-for-uav
                                     impact-event-for-uav
                                     escort-event-for-uav
                                     ))))

(defthmd zp-min-time-to-impact-event-implies-impact-event
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (equal 0 (min-time-to-impact-for-uav i ens)))
   (impact-event-for-uav i ens))
  :hints (("Goal" :in-theory (enable impending-impact-event-for-uav
                                     min-time-to-impact-for-uav
                                     impact-event-for-uav
                                     escort-event-for-uav
                                     ))
          (pattern::hint*
           escort-condition-implies
           ordering-rule
           )
          (average-hint)
          ))

(defthmd zp-min-time-to-impact-event-is-impact-event
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens))
   (iff (equal (min-time-to-impact-for-uav i ens) 0)
        (impact-event-for-uav i ens)))
  :hints (("GOal" :in-theory (enable positive-min-time-to-impact-event-implies-not-impact-event
                                     zp-min-time-to-impact-event-implies-impact-event
                                     ))))
;;
;; This proof is *way* too slow !! (?)
;; Apparently IMPENDING-IMPACT-EVENT-FOR-UAV appears
;; in some expensive hypothesis somewhere (?)
;;
;; ie: ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT-IS-SMALLEST
;;
(defthm impact-event-for-uav-implies-IMPENDING-IMPACT-EVENT-FOR-UAV
  (implies
   (and
    (wf-ensemble ens)
    (ESCORT-CONDITION ENS)
    (IMPACT-EVENT-FOR-UAV i ens))
   (IMPENDING-IMPACT-EVENT-FOR-UAV i ENS))
  :hints (("Goal" :in-theory (enable IMPACT-EVENT-FOR-UAV
                                     ESCORT-EVENT-FOR-UAV
                                     ;;IMPENDING-IMPACT-EVENT-FOR-UAV
                                     )
           :expand (IMPENDING-IMPACT-EVENT-FOR-UAV i ENS)
           )
          (pattern::hint
           escort-condition-implies
           )))

(encapsulate
    ()
  (local
   (encapsulate
       ()

     (defun-sk exists-impact-event (ens)
       (exists (i) (impact-event-for-uav i ens)))

     (in-theory (disable exists-impact-event))

     (defthmd zp-always-smallest-min-time-to-impending-impact-to-exists-impact-event-helper
       (implies
        (and
         (escort-condition ens)
         ;;(homogenous-escort-direction ens)
         (wf-ensemble ens))
        (iff (equal (always-smallest-min-time-to-impending-impact ens) 0)
             (exists-impact-event ens)))
       :otf-flg t
       :hints (("Goal" :do-not-induct t
                :in-theory (enable positive-min-time-to-impact-event-implies-not-impact-event))
               ("Subgoal 1" :in-theory (e/d (always-smallest-min-time-to-impending-impact
                                             zp-min-time-to-impact-event-implies-impact-event)
                                            ())
                :cases ((impact-event-for-uav (smallest-impending-dt-index ens) ens)))
               ("Subgoal 2"
                :use (:instance positive-min-time-to-impact-event-implies-not-impact-event
                                (i (EXISTS-IMPACT-EVENT-WITNESS ENS)))
                :in-theory (e/d (exists-impact-event
                                 ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT
                                 )
                                (positive-min-time-to-impact-event-implies-not-impact-event
                                 smallest-impending-dt-index-properties)))
               )
       )

     (defthm exists-uav-with-event-implies-exists-impact-event
       (implies
        (exists-uav-with-event ens)
        (exists-impact-event ens))
       :rule-classes (:rewrite :forward-chaining)
       :hints (("GOal" :in-theory (enable exists-uav-with-event)
                :use (:instance EXISTS-IMPACT-EVENT-suff
                                (i (EXISTS-UAV-WITH-EVENT-WITNESS ENS))))))

     (defthm exists-impact-event-implies-exists-uav-with-event
       (implies
        (and
         (exists-impact-event ens)
         (wf-ensemble ens))
        (exists-uav-with-event ens))
       :rule-classes (:rewrite :forward-chaining)
       :hints (("Goal" :in-theory (enable ESCORT-EVENT-FOR-UAV
                                          IMPACT-EVENT-FOR-UAV
                                          exists-impact-event))
               (pattern::hint
                (:term (+ 1 (uav-id-fix (EXISTS-IMPACT-EVENT-WITNESS ENS))))
                :use ((:instance EXISTS-UAV-WITH-EVENT-suff
                                 (i (+ 1 (uav-id-fix (EXISTS-IMPACT-EVENT-WITNESS ENS))))))
                :expand ((:free (i) (event-for-uav i ens))))
               (pattern::hint
                (:term (+ -1 (uav-id-fix (EXISTS-IMPACT-EVENT-WITNESS ENS))))
                :use ((:instance EXISTS-UAV-WITH-EVENT-suff
                                 (i (+ -1 (uav-id-fix (EXISTS-IMPACT-EVENT-WITNESS ENS))))))
                :expand ((:free (i) (event-for-uav i ens))))
               (pattern::hint*
                ordering-rule
                )
               (and stable-under-simplificationp
                    '(:use ((:instance EXISTS-UAV-WITH-EVENT-suff
                                       (i (uav-id-fix (EXISTS-IMPACT-EVENT-WITNESS ENS)))))
                           :expand (:free (i) (event-for-uav i ens))))
               ))

     ))

  (defthmd zp-always-smallest-min-time-to-impending-impact-to-exists-uav-with-event
    (implies
     (and
      (escort-condition ens)
      ;;(homogenous-escort-direction ens)
      (wf-ensemble ens))
     (iff (equal (always-smallest-min-time-to-impending-impact ens) 0)
          (exists-uav-with-event ens)))
    :hints (("Goal" :in-theory (enable zp-always-smallest-min-time-to-impending-impact-to-exists-impact-event-helper))))

  )

(defthmd nnrat-equiv-always-smallest-min-time-to-impending-impact
  (implies
   (impending-impact-event-for-uav i ens)
   (iff (nnrat-equiv (always-smallest-min-time-to-impending-impact ens)
                     (min-time-to-impact-for-uav i ens))
        (not (< (always-smallest-min-time-to-impending-impact ens)
                (min-time-to-impact-for-uav i ens)))))
  :hints (("goal" :in-theory (enable nnrat-equiv))))

(defthmd event-implies-zero-min-time
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (event-for-uav i ens))
   (equal (MIN-TIME-TO-IMPACT-FOR-UAV I ENS) 0))
  :hints (("Goal" :in-theory (enable
                              event-for-uav
                              MIN-TIME-TO-IMPACT-FOR-UAV
                              ))))

;;
;; The other relevant events ..
;;

(in-theory (disable next-step))

(def::ung step-time (dt ens)
  (declare (xargs :signature ((t t) uav-list-p)
                  :verify-guards nil))
  (let ((dt  (nnrat-fix dt))
        (ens (uav-list-fix! ens)))
    (if (<= dt 0) ens
      (metlist ((dt ens) (next-step dt ens))
        (step-time dt ens)))))

(encapsulate
    ()

  (local
   (defthmd step-time-definition-alt
     (equal (step-time dt ens)
            (if (not (step-time-domain dt ens)) (uav-list-fix! ens)
              (let ((dt  (nnrat-fix dt))
                    (ens (uav-list-fix! ens)))
                (if (<= dt 0) ens
                  (metlist ((dt ens) (next-step dt ens))
                    (step-time dt ens))))))))

  (local
   (defthmd step-time-measure-alt
     (equal (step-time-measure dt ens)
            (if (not (step-time-domain dt ens)) 0
              (let ((dt  (nnrat-fix dt))
                    (ens (uav-list-fix! ens)))
                (if (<= dt 0) 0
                  (metlist ((dt ens) (next-step dt ens))
                    (+ 1 (step-time-measure dt ens)))))))))

  )


(verify-guards
 step-time-monadic
 :hints (("goal" :expand (step-time-0-domain dt ens))))

(verify-guards step-time)

(verify-guards step-time-domain)

(defthm step-time-zero
  (equal (step-time 0 ens)
         (uav-list-fix ens))
  :hints (("Goal" :expand (step-time 0 ens))))

(in-theory (disable wf-ensemble))

(def::signature step-time (t wf-ensemble) wf-ensemble)

(defthm step-time-invariants
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    ;; DAG: technially we can get rid of this if we
    ;; accept time steps of 0.  The key is that
    ;; moving in time (by zero) doesn't change
    ;; anything.
    ;; (not (exists-uav-with-event ens))
    )
   (and (escort-condition (step-time dt ens))
        ;;(homogenous-escort-direction (step-time dt ens))
        (wf-ensemble (step-time dt ens)))))

(encapsulate
    ()

  (local
   (defthm step-time-domain-uav-list-fix
     (implies
      (syntaxp (symbolp ens))
      (equal (step-time-domain dt ens)
             (step-time-domain dt (uav-list-fix ens))))
     :hints (("Goal" :expand (step-time-domain dt (uav-list-fix ens))))))

  (defcong uav-list-equiv equal (step-time-domain dt ens) 2)

  )

(encapsulate
    ()

  (local
   (defthm step-time-domain-nnrat-fix
     (implies
      (syntaxp (symbolp dt))
      (equal (step-time-domain dt ens)
             (step-time-domain (nnrat-fix dt) ens)))
     :hints (("Goal" :expand (step-time-domain (nnrat-fix dt) ens)))))

  (defcong nnrat-equiv equal (step-time-domain dt ens) 1)

  )

(encapsulate
    ()

  (local
   (defthm step-time-measure-uav-list-fix
     (implies
      (syntaxp (symbolp ens))
      (equal (step-time-measure dt ens)
             (step-time-measure dt (uav-list-fix ens))))
     :hints (("Goal" :expand (step-time-measure dt (uav-list-fix ens))))))

  (defcong uav-list-equiv equal (step-time-measure dt ens) 2)

  )

(encapsulate
    ()

  (local
   (defthm step-time-measure-nnrat-fix
     (implies
      (syntaxp (symbolp dt))
      (equal (step-time-measure dt ens)
             (step-time-measure (nnrat-fix dt) ens)))
     :hints (("Goal" :expand (step-time-measure (nnrat-fix dt) ens)))))

  (defcong nnrat-equiv equal (step-time-measure dt ens) 1)

  )

(encapsulate
    ()

  (local
   (defthm step-fix-nnrat-fix
     (implies
      (syntaxp (symbolp d1))
      (equal (step-time d1 ens)
             (step-time (nnrat-fix d1) ens)))
     :hints (("Goal" :expand (step-time (nnrat-fix d1) ens)))))

  (defcong nnrat-equiv equal (step-time dt ens) 1)

  )

(encapsulate
    ()

  (local
   (defthm step-fix-nnrat-fix
     (implies
      (syntaxp (symbolp ens))
      (equal (step-time dt ens)
             (step-time dt (uav-list-fix ens))))
     :hints (("Goal" :expand (step-time dt (uav-list-fix ens))))))

  (defcong uav-list-equiv equal (step-time dt ens) 2)

  )

(defun-sk step-time-always-terminates ()
  (forall (dt ens) (step-time-domain dt ens)))

(defthm step-time-always-terminates-implication
  (implies
   (step-time-always-terminates)
   (step-time-domain dt ens))
  :hints (("Goal" :use step-time-always-terminates-necc)))

(in-theory (disable step-time-always-terminates))

(defthm zoola
  (implies
   (and
    (syntaxp (symbolp dt))
    (in-conclusion-check (nnrat-equiv z dt) :top t)
    )
   (iff (nnrat-equiv z dt)
        (hide (rewrite-equiv (nnrat-equiv dt z)))))
  :hints (("Goal" :expand (:Free (x) (hide x)))))

(in-theory (disable chasing-neighbor))
(in-theory (enable chasing-neighbor-is-not-impending-impact-event-for-uav))

;; I think we need a stronger version of this ..
;; one that says that it is sufficient for the
;; time to be less than than
;;

(defthm not-impact-event-for-uav-update-location-all-invariant-awkward
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens)
    (implies
      (not (chasing-neighbor i ens))
      (< (nnrat-fix dt) (min-time-to-impact-for-uav i ens))))
   (not (impact-event-for-uav i (update-location-all dt ens))))
  :hints (("Goal" :do-not-induct t
           ;;:expand (:free (i) (IMPENDING-IMPACT-EVENT-FOR-UAV I ENS))
           :in-theory (e/d (EVENT-FOR-UAV
                            ESCORT-EVENT-FOR-UAV
                            impact-event-for-uav)
                           (IMPACT-EVENT-FOR-UAV-IMPLIES-IMPENDING-IMPACT-EVENT-FOR-UAV)))
          (pattern::hint*
           escort-condition-implies
           ordering-rule
           )
          (pattern::hint
           (:term (IMPENDING-IMPACT-EVENT-FOR-UAV I ENS))
           :expand ((IMPENDING-IMPACT-EVENT-FOR-UAV I ENS)))
          (pattern::hint
           (:term (MIN-TIME-TO-IMPACT-FOR-UAV I ENS))
           :expand ((MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
          (average-hint)
          ))

(defthm this-seems-like-a-nice-property
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (NOT (IMPENDING-impact-EVENT-FOR-UAV I ENS)))
   (equal (MIN-TIME-TO-IMPACT-FOR-UAV I (FLIP-ON-EVENTS ENS))
          (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
  :hints (("Goal" :in-theory (e/d (FLIP-UAV
                                   IMPENDING-IMPACT-EVENT-FOR-UAV
                                   MIN-TIME-TO-IMPACT-FOR-UAV)
                                  (WF-ENSEMBLE)))
          (pattern::hint
           escort-condition-implies
           )))

(defthm this-seems-like-a-nice-property-too
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (IMPENDING-impact-EVENT-FOR-UAV I ENS)
    (not (impact-event-for-uav i ens)))
   (equal (MIN-TIME-TO-IMPACT-FOR-UAV I (FLIP-ON-EVENTS ENS))
          (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
  :hints (("Goal" :in-theory (e/d (FLIP-UAV
                                   ESCORT-EVENT-FOR-UAV
                                   IMPACT-EVENT-FOR-UAV
                                   IMPENDING-IMPACT-EVENT-FOR-UAV
                                   IMPENDING-EVENT-FOR-UAV
                                   MIN-TIME-TO-IMPACT-FOR-UAV)
                                  (WF-ENSEMBLE)))
          (pattern::hint*
           escort-condition-implies
           ordering-rule
           )))
