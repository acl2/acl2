;;
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")
(include-book "events")

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

;; ===================================================================
;;
;; Here we introduce the primitive operation "flip"
;;
;; ===================================================================

(def::und UAV->flip (uav)
  (declare (xargs :fty ((uav) uav)))
  (let ((uav (uav-fix! uav)))
    (let ((id        (UAV->id uav))
          (location  (UAV->location uav))
          (direction (UAV->direction uav)))
      (UAV id location (- direction)))))

(encapsulate
    ()

  (local (in-theory (enable UAV->flip)))

  (defthm UAV->id-UAV->flip
    (equal (UAV->id (UAV->flip uav))
           (UAV->id uav)))

  (defthm UAV->direction-UAV->flip
    (equal (UAV->direction (UAV->flip uav))
           (- (UAV->direction uav))))

  (defthm UAV->location-UAV->flip
    (equal (UAV->location (UAV->flip uav))
           (UAV->location uav)))

  )

(def::und flip-uav (i ens)
  (declare (xargs :signature ((t t) uav-p)))
  (let ((i (uav-id-fix i)))
    (if (event-for-uav i ens) (UAV->flip (ith-uav i ens))
      (ith-uav i ens))))

(defcong uav-id-equiv equal (flip-uav i ens) 1
  :hints (("Goal" :in-theory (enable flip-uav))))

(defcong uav-list-equiv equal (flip-uav i ens) 2
  :hints (("Goal" :in-theory (enable flip-uav))))

(def::un flip-on-events-rec (i ens)
  (declare (xargs :measure (uav-id-fix i)
                  :signature ((t t) true-listp)))
  (let ((i (uav-id-fix i)))
    (let ((uav (flip-uav i ens)))
      (if (zp i) (list uav)
        (update-nth i uav (flip-on-events-rec (1- i) ens))))))

(defthm len-flip-on-events-rec
  (equal (len (flip-on-events-rec i list))
         (1+ (uav-id-fix i)))
  :hints (("Goal" :in-theory (e/d (UAV-ID-EQUIV)
                                  (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV)))))

(defthm uav-list-p-update-nth
  (implies
   (and
    (<= (nfix n) (len list))
    (uav-list-p list)
    (uav-p v))
   (uav-list-p (update-nth n v list))))

(defthm uav-listp-flip-on-events-rec
  (uav-list-p (FLIP-ON-EVENTS-REC z ENS))
  :hints (("Goal" :in-theory (disable LESS-THAN-ZERO-TO-UAV-ID-EQUIV
                                      UAV-ID-FIX-PLUS))))

(def::signature flip-on-events-rec (t t) uav-list-p)

(defthm nth-flip-on-events-rec
  (implies
   (and
    (uav-id-p i)
    (<= i (uav-id-fix j)))
   (equal (nth i (flip-on-events-rec j ens))
          (flip-uav i ens)))
  :hints (("Goal" :induct (flip-on-events-rec j ens))))

(defthm ith-uav-flip-on-events-rec
  (implies
   (force (<= (uav-id-fix i) (uav-id-fix j)))
   (equal (ith-uav i (flip-on-events-rec j ens))
          (flip-uav i ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable ith-uav))))

;; ===================================================================
;;
;; flip-on-events is one of the fundamental building blocks of our
;; event-based simulator.  It changes the direction of any UAV
;; experiencing an event.
;;
;; ===================================================================

(def::und flip-on-events (list)
  (declare (xargs :fty ((uav-list) uav-list)))
  (flip-on-events-rec (1- (N)) list))

(defthm len-flip-on-events
  (equal (len (flip-on-events list))
         (N))
  :hints (("Goal" :in-theory (enable flip-on-events))))

(defthm ith-uav-flip-on-events
  (equal (ith-uav i (flip-on-events ens))
         (flip-uav i ens))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable uav-id-fix
                              uav-id-p
                              flip-on-events))))

(defthmd not-exists-uav-with-event-flip-on-events
  (implies
   (and
    (equal (len ens) (N))
    (not (exists-uav-with-event ens)))
   (uav-list-equiv (flip-on-events ens)
                   ens))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (flip-uav
                            uav-list-equiv-pick-a-point-alt)
                           (exists-uav-with-event)))))

(defthmd not-exists-uav-with-event-flip-on-events-equal
  (implies
   (and
    (equal (len ens) (N))
    (not (exists-uav-with-event ens)))
   (equal (flip-on-events ens)
          (uav-list-fix ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (not-exists-uav-with-event-flip-on-events
                            equal-to-uav-list-equiv)
                           (exists-uav-with-event)))))

(defthm uav-left-boundary-uav->flip
  (equal (UAV-left-BOUNDARY (UAV->FLIP uav))
         (UAV-left-boundary uav))
  :hints (("Goal" :in-theory (enable uav->flip UAV-LEFT-BOUNDARY
                                     uav-right-boundary))))

(defthm uav-right-boundary-uav->flip
  (equal (UAV-RIGHT-BOUNDARY (UAV->FLIP uav))
         (UAV-right-boundary uav))
  :hints (("Goal" :in-theory (enable uav->flip UAV-LEFT-BOUNDARY
                                     uav-right-boundary))))

(defthm uav->location-flip-auv
  (equal (uav->location (flip-uav i ens))
         (uav->location (ith-uav i ens)))
  :hints (("Goal" :in-theory (enable EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV
                                     flip-uav))))

(defthm uav->id-flip-auv
  (equal (uav->id (flip-uav i ens))
         (uav->id (ith-uav i ens)))
  :hints (("Goal" :in-theory (enable EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV
                                     flip-uav))))

(encapsulate
    ()

  (local
   (defthm equal-len-N-implies-consp
     (implies
      (equal (len x) (N))
      (consp x))
     :rule-classes (:rewrite :forward-chaining)))

  (local
   (defthm natp-implies-not-less-than-zero
     (implies
      (natp x)
      (not (< x 0)))))

  (defthm ORDERED-LOCATION-LIST-P-FLIP-ON-EVENTS
    (implies
     (and
      (equal (len ens) (N))
      (ORDERED-LOCATION-LIST-P ENS))
     (ORDERED-LOCATION-LIST-P (FLIP-ON-EVENTS ENS)))
    :hints (("Goal" :do-not-induct t
             :expand (ORDERED-LOCATION-LIST-QUANT-P (FLIP-ON-EVENTS ENS))
             :in-theory (enable ORDERED-LOCATION-LIST-P-TO-ORDERED-LOCATION-LIST-QUANT-P))
            (pattern::hint
             (< (uav->location (ith-uav j ens))
                (uav->location (ith-uav i ens)))
             :use ((:instance what-we-want-to-say-about-ordered-location-list-p
                              (list ens)
                              (i i)
                              (j j))))))

  )

(defthm SEQUENTIAL-ID-LIST-P-FLIP-ON-EVENTS
  (implies
   (and
    (equal (len ens) (N))
    (SEQUENTIAL-ID-LIST-P ENS))
   (SEQUENTIAL-ID-LIST-P (FLIP-ON-EVENTS ENS)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable sequential-id-list-p-reduction)
           :restrict ((sequential-id-list-p-reduction
                       ((list (FLIP-ON-EVENTS ENS))))))))

(defthmd escort-condition-flip-on-invariants-helper
  (implies
   (and
    (wf-ensemble ens))
   (escort-condition-p i j (flip-on-events ens)))
  :hints (("Goal" :do-not '(fertilize generalize)

           :do-not-induct t)
          (and stable-under-simplificationp
               '(:in-theory (e/d (flip-uav
                                  equal-uav-id-fix-1-to-uav-id-equiv)
                                 nil)))

          (and stable-under-simplificationp
               '(:in-theory (enable equal-uav-id-fix-1-to-uav-id-equiv
                                    location-linear
                                    right-boundary-is-ordered-linear
                                    ;;IMPLIES-UAV-ID-P
                                    UAV-ID-FIX-UAV-ID-P
                                    )))


          ))

(encapsulate
    ()

  (local
   (defthm escort-condition-flip-on-invariants
     (implies
      (and
       ;;(escort-condition ens)
       (wf-ensemble ens))
      (escort-condition (flip-on-events ens)))
     :hints (("Goal" :in-theory (disable ESCORT-CONDITION-P)
              :expand ((:free (x) (hide x))
                       (escort-condition (flip-on-events ens))))
             (pattern::hint
              (not (escort-condition-p i j (flip-on-events ens)))
              :use ((:instance escort-condition-flip-on-invariants-helper
                               (i i)
                               (j j))))
             )))

  (def::signature flip-on-events (wf-ensemble) escort-condition)

  )

(def::signature flip-on-events (wf-ensemble) wf-ensemble)

(defthm flip-on-events-invariants
  (implies
   (and
    ;;(exists-uav-with-event ens)
    ;;(escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens))
   (and (escort-condition (flip-on-events ens))
        ;;(homogenous-escort-direction (flip-on-events ens))
        (wf-ensemble (flip-on-events ens))))
  :hints (("Goal" :do-not-induct t)))

(defthm flip-on-events-eliminates-all-events
  (implies
   (and
    ;;(escort-condition ens)
    (wf-ensemble ens))
   (not (exists-uav-with-event (flip-on-events ens))))
  :hints (("Goal" :expand (exists-uav-with-event (flip-on-events ens))
           :in-theory (enable EVENT-FOR-UAV)
           :do-not '(fertilize generalize)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:in-theory (enable location-linear
                                    right-boundary-is-ordered-linear
                                    FLIP-UAV)))
          ))

(in-theory (disable location-linear right-boundary-is-ordered-linear))

(defthm min-time-to-impact-for-uav-flip-on-events-invariant
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    (NOT (IMPACT-EVENT-FOR-UAV I ENS))
    )
   (equal (min-time-to-impact-for-uav I (flip-on-events ens))
          (min-time-to-impact-for-uav I ens)))
  :hints (("Goal" :in-theory (e/d (MIN-TIME-TO-IMPACT-FOR-UAV
                                   IMPACT-EVENT-FOR-UAV
                                   escort-event-for-uav
                                   flip-uav)
                                  nil
                                  ))
          (pattern::hint*
           location-pinching-rule
           escort-condition-implies
           ordering-rule
           )
          (and stable-under-simplificationp
               '(:in-theory (enable event-for-uav)))
          ))

(defthm impending-event-for-uav-still-impending-flip-on-events
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (impending-event-for-uav i ens)
    (not (event-for-uav i ens)))
   (impending-event-for-uav i (flip-on-events ens)))
  :hints (("Goal" :in-theory (disable event-for-uav impending-event-for-uav)
           :expand ((min-time-to-impact-for-uav i ens)
                    (event-for-uav i ens)
                    (impending-event-for-uav i ens)))
          (and stable-under-simplificationp
               '(:in-theory (enable flip-uav event-for-uav impending-event-for-uav)))
          (pattern::hint*
           location-pinching-rule
           escort-condition-implies
           ordering-rule
          )))

(defthm not-escort-for-uav-flip-on-events-invariant
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    )
   (not (escort-event-for-uav i (flip-on-events ens))))
  :hints (("Goal" :in-theory (e/d (flip-uav
                                   event-for-uav
                                   escort-event-for-uav)
                                  (right-perimeter-pinching)))
          (pattern::hint*
           escort-condition-implies
           location-pinching-rule
           ordering-rule
           right-perimeter-escort-condition-implies
           )
          (pattern::hint
           (equal (RIGHT-PERIMETER-BOUNDARY) (UAV->LOCATION (ITH-UAV (+ -2 (N)) ENS)))
           :cases ((equal (UAV->LOCATION (ITH-UAV (+ -2 (N)) ENS))
                          (UAV->LOCATION (ITH-UAV (+ -1 (N)) ENS))))
           :name case-split
          )))

(without-subsumption
 (defthm not-event-for-uav-flip-on-events-invariant
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    ;;(not (event-for-uav i ens)))
    )
   (not (event-for-uav i (flip-on-events ens))))
  :hints (("Goal" :do-not-induct t
           :do-not '(preprocess)
           :in-theory (enable flip-uav)
           :expand ((event-for-uav i (flip-on-events ens))))
          (pattern::hint*
           escort-condition-implies
           location-pinching-rule
           ordering-rule
           right-perimeter-escort-condition-implies
           )
          (and stable-under-simplificationp
               '(:in-theory (e/d (flip-uav event-for-uav)
                                 (right-perimeter-pinching))))
           )))

(defthm not-impact-event-for-uav-flip-on-events-invariant
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    ;;(not (impact-event-for-uav i ens))
    )
   (not (impact-event-for-uav i (flip-on-events ens))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable impact-event-for-uav))))

(defthm impending-escort-for-uav-still-impending-flip-on-events
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (not (escort-event-for-uav i ens))
    (impending-escort-for-uav i ens))
   (impending-escort-for-uav i (flip-on-events ens)))
  :hints (("Goal" :in-theory (disable escort-event-for-uav impending-escort-for-uav)
           :expand ((min-time-to-impact-for-uav i ens)
                    (escort-event-for-uav i ens)
                    (impending-escort-for-uav i ens)))
          (and stable-under-simplificationp
               '(:in-theory (enable flip-uav escort-event-for-uav impending-escort-for-uav)))
          (pattern::hint*
           location-pinching-rule
           escort-condition-implies
           ordering-rule
          )))

(defthm impending-impact-event-for-uav-flip-on-events-invariant
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (impending-impact-event-for-uav i ens)
    (not (impact-event-for-uav i ens)))
   (impending-impact-event-for-uav i (flip-on-events ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (impact-event-for-uav
                            imminent-event-reduction)
                           (IMPENDING-ESCORT-FOR-UAV
                            IMPENDING-EVENT-FOR-UAV)))))

