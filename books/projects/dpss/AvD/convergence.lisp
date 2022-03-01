;;
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "../Base/step-time-induction")
(include-book "invariants")

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

;; ===================================================================
;;
;; A mechanization of the AvD proof of DPSS-A bounded convergnece time
;;
;; ===================================================================

(in-theory (disable have-met-Right-p have-met-left-p))

(defthm have-met-left-p-after-time-to-event-TEE
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (step-time-always-terminates))
   (have-met-Left-p i (flip-on-events (step-time (time-to-event i (TEE) ens) ens)))))

(defthm have-met-Right-p-after-time-to-event-TEE
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (step-time-always-terminates))
   (have-met-Right-p i (flip-on-events (step-time (time-to-event i (TEE) ens) ens)))))

(defthm have-met-left-p-step-time-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (have-met-left-p i ens))
   (have-met-left-p i (step-time dt ens)))
  :hints (("Goal" :in-theory
           (enable
            (:INDUCTION STEP-TIME-INDUCTION-RULE))
           :induct (step-time dt ens))))

(defthm have-met-Right-p-step-time-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (have-met-right-p i ens))
   (have-met-right-p i (step-time dt ens)))
  :hints (("Goal" :in-theory (enable (:INDUCTION STEP-TIME-INDUCTION-RULE))
           :induct (step-time dt ens))))

(defthm have-met-left-p-at-TEE
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (step-time-always-terminates))
   (have-met-Left-p i (flip-on-events (step-time (TEE) ens))))
  :hints (("Goal" :in-theory (e/d (introduce-flip-on-events-generic
                                   open-step-time-on-TEE)
                                  (step-time-flip-on-events))
           :restrict ((open-step-time-on-TEE ((i i)))
                      (introduce-flip-on-events-generic
                       ((ens (STEP-TIME (TIME-TO-EVENT I (TEE) ENS) ENS))))
                      ))))

(defthm have-met-right-p-at-TEE
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (step-time-always-terminates))
   (have-met-Right-p i (flip-on-events (step-time (TEE) ens))))
  :hints (("Goal" :in-theory (e/d (introduce-flip-on-events-generic
                                   open-step-time-on-TEE)
                                  (step-time-flip-on-events))
           :restrict ((open-step-time-on-TEE ((i i)))
                      (introduce-flip-on-events-generic ((ens (STEP-TIME (TIME-TO-EVENT I (TEE) ENS) ENS))))
                      ))))

(defun-sk all-have-met-left (ens)
  (forall (i) (have-met-left-p i ens)))

(in-theory (disable all-have-met-left))

(defthm all-have-met-left-implication
  (implies
   (all-have-met-left ens)
   (have-met-left-p i ens)))

(in-theory (disable all-have-met-left-necc))

(defthm all-have-met-left-at-TEE
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (step-time-always-terminates))
   (all-have-met-left (flip-on-events (step-time (TEE) ens))))
  :hints (("Goal" :in-theory (enable all-have-met-left))))

(defthm all-have-met-left-step-time-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens))
   (all-have-met-left (step-time dt ens)))
  :hints (("Goal" :expand (all-have-met-left (step-time dt ens))
           :in-theory (disable all-have-met-left-implication)
           :use ((:instance all-have-met-left-implication
                            (i (ALL-have-met-LEFT-WITNESS (STEP-TIME DT ENS)))))
           :do-not-induct t)))

(defthm all-have-met-left-after-TEE
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (step-time-always-terminates)
    (< (TEE) (nnrat-fix dt)))
   (all-have-met-left (step-time dt ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (step-time-decomposition
                            introduce-flip-on-events-generic
                            )
                           (step-time-composition
                            STEP-TIME-FLIP-ON-EVENTS
                            ))
           :restrict ((introduce-flip-on-events-generic ((ens (STEP-TIME (TEE) ENS))))
                      (step-time-decomposition ((dt dt) (ens ens) (x (TEE))))))))

(defthm all-have-met-left-flip-on-events
  (implies
   (and
    (wf-escort-p ens)
    (all-have-met-left ens))
   (all-have-met-left (FLIP-ON-EVENTS ENS)))
  :hints (("Goal" :expand (all-have-met-left (FLIP-ON-EVENTS ENS))
           :in-theory (disable all-have-met-left-implication)
           :use ((:instance all-have-met-left-implication
                            (i (ALL-have-met-LEFT-WITNESS (FLIP-ON-EVENTS ENS))))))))

(defthm all-have-met-left-update-location-all
  (implies
   (and
    (wf-escort-p ens)
    (lte-min-time-to-impending-impact-event dt ens)
    (all-have-met-left ens))
   (all-have-met-left (update-location-all dt ens)))
  :hints (("Goal" :expand (all-have-met-left (update-location-all dt ens))
           :in-theory (disable all-have-met-left-implication)
           :use ((:instance all-have-met-left-implication
                            (i (ALL-have-met-LEFT-WITNESS (update-location-all dt ens))))))))

(defun-sk all-have-met-right (ens)
  (forall (i) (have-met-right-p i ens)))

(in-theory (disable all-have-met-right))

(defthm all-have-met-right-implication
  (implies
   (all-have-met-right ens)
   (have-met-right-p i ens)))

(in-theory (disable all-have-met-right-necc))

(defthm all-have-met-right-at-TEE
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (step-time-always-terminates))
   (all-have-met-right (flip-on-events (step-time (TEE) ens))))
  :hints (("Goal" :in-theory (enable all-have-met-right))))

(defthm all-have-met-right-step-time-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-right ens))
   (all-have-met-right (step-time dt ens)))
  :hints (("Goal" :expand (all-have-met-right (step-time dt ens))
           :in-theory (disable all-have-met-right-implication)
           :use ((:instance all-have-met-right-implication
                            (i (ALL-have-met-RIGHT-WITNESS (STEP-TIME DT ENS)))))
           :do-not-induct t)))

(defthm all-have-met-right-after-TEE
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (step-time-always-terminates)
    (< (TEE) (nnrat-fix dt)))
   (all-have-met-right (step-time dt ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (step-time-decomposition
                            introduce-flip-on-events-generic
                            )
                           (step-time-composition
                            STEP-TIME-FLIP-ON-EVENTS
                            ))
           :restrict ((introduce-flip-on-events-generic ((ens (STEP-TIME (TEE) ENS))))
                      (step-time-decomposition ((dt dt) (ens ens) (x (TEE))))))))

(defthm all-have-met-right-flip-on-events
  (implies
   (and
    (wf-escort-p ens)
    (all-have-met-right ens))
   (all-have-met-right (FLIP-ON-EVENTS ENS)))
  :hints (("Goal" :expand (all-have-met-right (FLIP-ON-EVENTS ENS))
           :in-theory (disable all-have-met-right-implication)
           :use ((:instance all-have-met-right-implication
                            (i (ALL-have-met-RIGHT-WITNESS (FLIP-ON-EVENTS ENS))))))))

(defthm all-have-met-right-update-location-all
  (implies
   (and
    (wf-escort-p ens)
    (lte-min-time-to-impending-impact-event dt ens)
    (all-have-met-right ens))
   (all-have-met-right (update-location-all dt ens)))
  :hints (("Goal" :expand (all-have-met-right (update-location-all dt ens))
           :in-theory (disable all-have-met-right-implication)
           :use ((:instance all-have-met-right-implication
                            (i (ALL-have-met-RIGHT-WITNESS (update-location-all dt ens))))))))

(in-theory (disable RIGHT-SYNCHRONIZED-p LEFT-SYNCHRONIZED-p))

(defthm left-synchronized-p-0
  (LEFT-SYNCHRONIZED-P 0 ens)
  :hints (("Goal" :in-theory (enable LEFT-SYNCHRONIZED-p))))

(defthm right-synchronized-p-N-1
  (RIGHT-SYNCHRONIZED-P (+ -1 (N)) ens)
  :hints (("Goal" :in-theory (enable RIGHT-SYNCHRONIZED-p))))

(defthm left-synchronized-p-N
  (implies
   (equal (N) 1)
   (LEFT-SYNCHRONIZED-P i ens))
  :hints (("Goal" :in-theory (enable LEFT-SYNCHRONIZED-p))))

(defthm right-synchronized-p-N
  (implies
   (equal (N) 1)
   (RIGHT-SYNCHRONIZED-P i ens))
  :hints (("Goal" :in-theory (enable RIGHT-SYNCHRONIZED-p))))

(def::un all-lte-are-left-synchronized (i ens)
  (declare (xargs :measure (uav-id-fix i)
                  :fty ((uav-id uav-list) bool)))
  (if (zp i) (LEFT-SYNCHRONIZED-p i ens)
    (and (LEFT-SYNCHRONIZED-p i ens)
         (all-lte-are-left-synchronized (1- i) ens))))

(defthm all-lte-left-synchronized-implication
  (implies
   (and
    (all-lte-are-left-synchronized i ens)
    (<= (uav-id-fix j) (uav-id-fix i)))
   (LEFT-SYNCHRONIZED-p j ens)))

(defthm all-lte-left-synchronized-flip-on-event-invariant
  (implies
   (and
    (wf-escort-p ens)
    (all-have-met-left ens)
    (all-lte-are-left-synchronized i ens))
   (all-lte-are-left-synchronized i (flip-on-events ens)))
    :hints (("Goal" :do-not-induct t
             :induct (all-lte-are-left-synchronized i ens))))

(defthm all-lte-left-synchronized-update-location-all-invariant
  (implies
   (and
    (wf-escort-p ens)
    (all-have-met-left ens)
    (lte-min-time-to-impending-impact-event dt ens)
    (all-lte-are-left-synchronized i ens))
   (all-lte-are-left-synchronized i (update-location-all dt ens)))
    :hints (("Goal" :do-not-induct t
             :induct (all-lte-are-left-synchronized i ens))))

(defthm simple-arithmetic-fact
  (equal (+ x (* -1 x)) 0))

(defthm left-synchronized-p-flip-on-events-invariant-strong
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens)
    (all-lte-are-left-synchronized i ens))
   (left-synchronized-p i (flip-on-events ens)))
  :hints (("Goal" :cases ((uav-id-equiv i 0))
           :do-not-induct t)))

(defthm left-synchronized-p-step-time-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens)
    (all-lte-are-left-synchronized i ens))
   (left-synchronized-p i (step-time dt ens)))
  :hints (("Goal" :do-not-induct t
           :induct (step-time dt ens))))

(defthm all-lte-left-synchronized-step-time-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens)
    (all-lte-are-left-synchronized i ens))
   (all-lte-are-left-synchronized i (step-time dt ens)))
  :hints (("Goal" :do-not-induct t
           :induct (step-time dt ens))))

(in-theory (disable all-lte-are-left-synchronized))

(def::un all-gte-are-right-synchronized (i ens)
  (declare (xargs :measure (nfix (- (N) (uav-id-fix i)))
                  :fty ((uav-id uav-list) bool)))
  (if (equal i (+ -1 (N))) (RIGHT-SYNCHRONIZED-p i ens)
    (and (RIGHT-SYNCHRONIZED-p i ens)
         (all-gte-are-right-synchronized (1+ i) ens))))

(defthm all-gte-right-synchronized-implication
  (implies
   (and
    (all-gte-are-right-synchronized i ens)
    (<= (uav-id-fix i) (uav-id-fix j)))
   (RIGHT-SYNCHRONIZED-p j ens)))

(defthm all-gte-right-synchronized-flip-on-event-invariant
  (implies
   (and
    (wf-escort-p ens)
    (all-have-met-right ens)
    (all-gte-are-right-synchronized i ens))
   (all-gte-are-right-synchronized i (flip-on-events ens)))
    :hints (("Goal" :do-not-induct t
             :induct (all-gte-are-right-synchronized i ens))))

(defthm all-gte-right-synchronized-update-location-all-invariant
  (implies
   (and
    (wf-escort-p ens)
    (all-have-met-right ens)
    (lte-min-time-to-impending-impact-event dt ens)
    (all-gte-are-right-synchronized i ens))
   (all-gte-are-right-synchronized i (update-location-all dt ens)))
    :hints (("Goal" :do-not-induct t
             :induct (all-gte-are-right-synchronized i ens))))

(defthm right-synchronized-p-flip-on-events-invariant-strong
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-right ens)
    (all-gte-are-right-synchronized i ens))
   (right-synchronized-p i (flip-on-events ens)))
  :hints (("Goal" :do-not-induct t
           :cases ((uav-id-equiv i (+ -1 (N)))))))

(defthm right-synchronized-p-step-time-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-right ens)
    (all-gte-are-right-synchronized i ens))
   (right-synchronized-p i (step-time dt ens)))
  :hints (("Goal" :do-not-induct t
           :induct (step-time dt ens))))

(defthm all-gte-right-synchronized-step-time-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-right ens)
    (all-gte-are-right-synchronized i ens))
   (all-gte-are-right-synchronized i (step-time dt ens)))
  :hints (("Goal" :do-not-induct t
           :induct (step-time dt ens))))

(in-theory (disable all-gte-are-right-synchronized))

(def::und one ()
  (declare (xargs :signature (() nnrat-p)))
  (segment-length))

;; ==================================================================
;; Proof development for time-to-LEFT-SYNCHRONIZED
;; ==================================================================

(encapsulate
    (
     ((not-LEFT-SYNCHRONIZED-p * *) => *)
     )

  (local
   (def::un not-LEFT-SYNCHRONIZED-p (j ens)
     (declare (xargs :fty ((uav-id uav-list) bool)))
     (and
      (<= 1 (UAV-ID-FIX J))
      (or
         ;;
         ;; |--------|--------| ;; J won't turn around until it reaches its right boarder.
         ;;     >  ^  >
         ;;           J
         ;;
         ;; |--------|--------| ;; After J's event, it will continue until it reaches its right boarder.
         ;;     >  ^  <
         ;;           J
         ;;
         ;; |--------|--------| ;; J won't turn around until it reaches its right boarder.
         ;; <      ^      >
         ;;               J
         ;;
         ;; |--------|--------| ;; After J's event, it will continue until it reaches its right boarder.
         ;; <      ^      <
         ;;               J
         (and (< (AVERAGE (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
                          (UAV->LOCATION (ITH-UAV J ENS)))
                 (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))
              (or
               (< 0 (UAV->DIRECTION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))
               (equal (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
                      (uav-left-boundary (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))))
         ;;
         ;; |--------|--------|--------|
         ;; <          ^          <
         ;;                       J
         (and
          (<= (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
              (AVERAGE (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
                       (UAV->LOCATION (ITH-UAV J ENS))))
          (equal (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS))
                 (uav-left-boundary (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)))
          (< (UAV->DIRECTION (ITH-UAV J ENS)) 0)
          (< (UAV->DIRECTION (ITH-UAV (+ -1 (UAV-ID-FIX J)) ENS)) 0)
          )))))

   (encapsulate
       ()

     (local (in-theory (enable have-met-LEFT-P LEFT-SYNCHRONIZED-P)))

     (defthmd not-left-synchronized-p-direction-implies-event
       (implies
        (and
         (not-LEFT-SYNCHRONIZED-p (+ 1 (UAV-ID-FIX J)) ens)
         (< (UAV->DIRECTION (ITH-UAV J ENS)) 0)
         (all-have-met-left ens)
         (all-lte-are-left-synchronized j ens)
         (wf-ensemble ens))
        (and
         (event-for-uav j ens)
         (equal (UAV->LOCATION (ITH-UAV J ENS))
                (uav-left-boundary (ITH-UAV J ENS)))))
       :hints ('(:in-theory (disable all-have-met-left-implication)
                            :use (:instance all-have-met-left-implication
                                            (i j))
                            :expand (all-lte-are-left-synchronized j ens))
               (average-hint)))

     (defthmd not-left-synchronized-p-implies-within-segment
       (implies
        (and
         (not-LEFT-SYNCHRONIZED-p (+ 1 (uav-id-fix j)) ens)
         (wf-ensemble ens)
         (all-have-met-left ens)
         (all-lte-are-left-synchronized j ens))
        (and (< (UAV->LOCATION (ITH-UAV J ENS))
                (uav-right-boundary (ITH-UAV J ENS)))
             (<= (uav-left-boundary (ITH-UAV J ENS))
                 (UAV->LOCATION (ITH-UAV J ENS)))))
       :hints ('(:in-theory (disable all-have-met-left-implication)
                            :use (:instance all-have-met-left-implication
                                            (i j))
                            :expand (all-lte-are-left-synchronized j ens))
               (average-hint))
       :rule-classes (:linear))

     (defthmd not-LEFT-SYNCHRONIZED-p-property
       (implies
        (and
         (wf-ensemble ens)
         (all-have-met-left ens)
         (all-lte-are-left-synchronized j ens))
        (iff (LEFT-SYNCHRONIZED-p (+ 1 (uav-id-fix j)) ens)
             (not (not-LEFT-SYNCHRONIZED-p (+ 1 (uav-id-fix j)) ens))))
       :rule-classes ((:rewrite :corollary
                                (implies
                                 (and
                                  (syntaxp (symbolp ens))
                                  (in-conclusion-check (LEFT-SYNCHRONIZED-p (+ 1 (uav-id-fix j)) ens) :top :negated)
                                  (wf-ensemble ens)
                                  (all-have-met-left ens)
                                  (all-lte-are-left-synchronized j ens))
                                 (iff (LEFT-SYNCHRONIZED-p (+ 1 (uav-id-fix j)) ens)
                                      (not (not-LEFT-SYNCHRONIZED-p (+ 1 (uav-id-fix j)) ens))))))
       :hints ('(:in-theory (disable all-have-met-left-implication)
                            :use (:instance all-have-met-left-implication
                                            (i j))
                            :expand (all-lte-are-left-synchronized j ens))
               (average-hint)))

     ))


(encapsulate
    (
     ((not-RIGHT-SYNCHRONIZED-p * *) => *)
     )

  (local
   (def::un not-RIGHT-SYNCHRONIZED-p (j ens)
     (declare (xargs :fty ((uav-id uav-list) bool)))
     (and
      (< (UAV-ID-FIX J) (+ -1 (N)))
      (or
       ;;
       ;; |--------|--------|
       ;;        <  ^  <
       ;;        J
       ;;
       ;; |--------|--------|
       ;;        >  ^  <
       ;;        J
       ;;
       ;; |--------|--------|
       ;;     <      ^      >
       ;;     J
       ;;
       ;; |--------|--------|
       ;;     >      ^      >
       ;;     J
       (and (< (UAV-LEFT-BOUNDARY (ITH-UAV (+ 1 (UAV-ID-FIX J)) ENS))
               (AVERAGE (UAV->LOCATION (ITH-UAV (+ 1 (UAV-ID-FIX J)) ENS))
                        (UAV->LOCATION (ITH-UAV J ENS))))
            (or
             (< (UAV->DIRECTION (ITH-UAV (+ 1 (UAV-ID-FIX J)) ENS)) 0)
             (equal (UAV->LOCATION (ITH-UAV (+ 1 (UAV-ID-FIX J)) ENS))
                    (uav-right-boundary (ITH-UAV (+ 1 (UAV-ID-FIX J)) ENS)))))
       ;;
       ;; |--------|--------|--------|
       ;;      >          ^          >
       ;;      J
       (and
        (<= (AVERAGE (UAV->LOCATION (ITH-UAV (+ 1 (UAV-ID-FIX J)) ENS))
                     (UAV->LOCATION (ITH-UAV J ENS)))
            (UAV-LEFT-BOUNDARY (ITH-UAV (+ 1 (UAV-ID-FIX J)) ENS)))
        (equal (UAV->LOCATION (ITH-UAV (+ 1 (UAV-ID-FIX J)) ENS))
               (uav-right-boundary (ITH-UAV (+ 1 (UAV-ID-FIX J)) ENS)))
        (< 0 (UAV->DIRECTION (ITH-UAV J ENS)))
        (< 0 (UAV->DIRECTION (ITH-UAV (+ 1 (UAV-ID-FIX J)) ENS)))
        )))))

  (with-arithmetic
   (defthmd not-RIGHT-SYNCHRONIZED-p-property
     (implies
      (and
       (< 0 (UAV-ID-FIX J))
       (wf-ensemble ens)
       (all-have-met-right ens)
       (all-gte-are-right-synchronized j ens))
      (iff (RIGHT-SYNCHRONIZED-p (+ -1 (uav-id-fix j)) ens)
           (not (not-RIGHT-SYNCHRONIZED-p (+ -1 (uav-id-fix j)) ens))))
     :rule-classes ((:rewrite :corollary
                                (implies
                                 (and
                                  (syntaxp (symbolp ens))
                                  (in-conclusion-check (RIGHT-SYNCHRONIZED-p (+ -1 (uav-id-fix j)) ens) :top :negated)
                                  (< 0 (UAV-ID-FIX J))
                                  (wf-ensemble ens)
                                  (all-have-met-right ens)
                                  (all-gte-are-right-synchronized j ens))
                                 (iff (RIGHT-SYNCHRONIZED-p (+ -1 (uav-id-fix j)) ens)
                                      (not (not-RIGHT-SYNCHRONIZED-p (+ -1 (uav-id-fix j)) ens))))))
     :hints ('(:do-not-induct t
               :in-theory (e/d (have-met-RIGHT-P right-synchronized-p) (all-gte-are-right-synchronized all-have-met-right-implication))
               :use (:instance all-have-met-right-implication
                               (i j))
               :expand ((all-gte-are-right-synchronized j ens)))
             (average-hint))))


  (defthmd not-right-synchronized-p-direction-implies-event
    (implies
     (and
      (not-right-synchronized-p (+ -1 (uav-id-fix j)) ens)
      (< 0 (UAV->DIRECTION (ITH-UAV J ENS)))
      (wf-ensemble ens)
      (< 0 (UAV-ID-FIX J))
      (all-have-met-right ens)
      (all-gte-are-right-synchronized j ens))
     (and (event-for-uav j ens)
          (equal (uav->location (ith-uav j ens))
                 (uav-right-boundary (ith-uav j ens)))))
    :hints ('(:in-theory (e/d (right-synchronized-p have-met-left-p) (all-have-met-right-implication))
                         :expand (all-gte-are-right-synchronized j ens))
            (average-hint)
            ))

  (defthmd not-right-synchronized-p-implies-within-segment
    (implies
     (and
      (not-RIGHT-SYNCHRONIZED-p (+ -1 (uav-id-fix j)) ens)
      (wf-ensemble ens)
      (all-have-met-right ens)
      (all-gte-are-right-synchronized j ens)
      (< 0 (UAV-ID-FIX J)))
     (and (<= (UAV->LOCATION (ITH-UAV J ENS))
              (uav-right-boundary (ITH-UAV J ENS)))
          (< (uav-left-boundary (ITH-UAV J ENS))
             (UAV->LOCATION (ITH-UAV J ENS)))))
    :hints ('(:in-theory (e/d (right-synchronized-p have-met-left-p) (all-have-met-right-implication))
                         :expand (all-gte-are-right-synchronized j ens))
            (average-hint)
            )
    :rule-classes (:linear))

  )

;; We saw this before .. ACL2 either just isn't tring very
;; hard .. or it is losing track of the fact that
;; some genequiv holds ..

;; Hopefully normalize-additive-constants-under-< fixed this (?)

(defthm why?
  (equal (have-met-LEFT-P (UAV-ID-FIX J) ENS)
         (have-met-LEFT-P J ENS))
  :hints (("Goal" :in-theory (disable have-met-left-p))))

(defthm again-why?
  (equal (LEFT-SYNCHRONIZED-P (UAV-ID-FIX J) ENS)
         (LEFT-SYNCHRONIZED-P J ENS))
  :hints (("Goal" :in-theory (disable LEFT-SYNCHRONIZED-P))))

(defthm arithmetic-fact
  (equal (+ x (* -1 x)) 0))

(defthm retain-variables
  (hide (always-true i))
  :hints (("Goal" :in-theory (enable hide)))
  :rule-classes nil)

;; We are writing this from the perspective of
;; the most recently left synchronized uav.

;;
;; This does some sort of magic to admit time-to-left-synchronized ..
;;
(def::linear width-of-segment-is-segment-length
  (equal (- (uav-right-boundary (ith-uav j ens))
            (uav-left-boundary (ith-uav j ens)))
         (segment-length))
  :hints (("Goal" :in-theory (enable uav-right-boundary
                                     uav-left-boundary))))

(def::un time-to-left-synchronized (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (if (equal i (+ -1 (N))) 0
    (if (left-synchronized-p (+ 1 (uav-id-fix i)) ens) 0
      (if (< (UAV->DIRECTION (ITH-UAV i ENS)) 0)
          ;; we are on our left boundary ..
          ;; there is an event ..
          ;; we flip, then travel to the right boundary
          ;; - which is equal to (one)
          ;; - which is lte (time-to-event)
          (- (uav-right-boundary (ith-uav i ens))
             (uav-left-boundary (ith-uav i ens)))
        ;; we are heading right .. as soon as we
        ;; get to the right boundary, the predicate
        ;; will be true (for sure) .. maybe
        ;; sooner.
        (nnrat-fix
         (- (uav-right-boundary (ith-uav i ens))
            (uav->location (ith-uav i ens))))))))

(defthmd time-to-left-synchronized-upper-bound
  (implies
   (and
    (wf-ensemble ens)
    (all-have-met-left ens)
    (all-lte-are-left-synchronized i ens))
   (<= (time-to-left-synchronized i ens) (one)))
  :rule-classes :rewrite
  :hints (("Goal" :in-theory (e/d (one
                                   not-LEFT-SYNCHRONIZED-p-property
                                   not-left-synchronized-p-implies-within-segment)
                                  (REWRITE-LEFT-BOUNDARY-TO-RIGHT-BOUNDARY
                                   have-met-left-p left-synchronized-p)))))

(def::un time-to-right-synchronized (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (if (equal i 0) 0
    (if (right-synchronized-p (+ -1 (uav-id-fix i)) ens) 0
      (if (< 0 (UAV->DIRECTION (ITH-UAV i ENS)))
          ;; we are on our right boundary ..
          ;; there is an event ..
          ;; we flip, then travel to the left boundary
          ;; - which is equal to (one)
          ;; - which is lte (time-to-event)
          (- (uav-right-boundary (ith-uav i ens))
             (uav-left-boundary (ith-uav i ens)))
        ;; we are heading left .. as soon as we
        ;; get to the left boundary, the predicate
        ;; will be true (for sure) .. maybe
        ;; sooner.
        (nnrat-fix
         (- (uav->location (ith-uav i ens))
            (uav-left-boundary (ith-uav i ens))))))))

(defthmd time-to-right-synchronized-upper-bound
  (implies
   (and
    (wf-ensemble ens)
    (all-have-met-right ens)
    (all-gte-are-right-synchronized i ens))
   (<= (time-to-right-synchronized i ens) (one)))
  :rule-classes :rewrite
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (one
                            nnrat-fix
                            not-RIGHT-SYNCHRONIZED-p-property
                            not-right-synchronized-p-implies-within-segment)
                           (REWRITE-LEFT-BOUNDARY-TO-RIGHT-BOUNDARY
                            have-met-right-p right-synchronized-p)))))

(in-theory (disable width-of-segment-is-segment-length))

(in-theory (disable time-to-left-synchronized time-to-right-synchronized))

(defthm right-boundary-flip-on-events-invariant
  (equal (uav-right-boundary (ith-uav i (flip-on-events ens)))
         (uav-right-boundary (ith-uav i ens))))

(defthm right-boundary-update-location-all-invariant
  (equal (uav-right-boundary (ith-uav i (update-location-all dt ens)))
         (uav-right-boundary (ith-uav i ens))))

(defthm right-boundary-step-time
  (equal (uav-right-boundary (ith-uav i (step-time dt ens)))
         (uav-right-boundary (ith-uav i ens)))
  :hints (("Goal" :expand (STEP-TIME DT ENS)
           :induct (step-time dt ens))))

(defthm left-boundary-step-time
  (implies
   (wf-ensemble ens)
   (equal (uav-left-boundary (ith-uav i (step-time dt ens)))
          (uav-left-boundary (ith-uav i ens)))))

(local-preamble

 (defthm goal-3
   ;; This uses STEP-TO-RIGHT-BOUNDARY
   (IMPLIES (AND (WF-ESCORT-P ENS)
                 (STEP-TIME-ALWAYS-TERMINATES)
                 (ALL-have-met-LEFT ENS)
                 (ALL-LTE-ARE-LEFT-SYNCHRONIZED I ENS)
                 (<= (+ 2 (UAV-ID-FIX I)) (N))
                 (< (UAV-ID-FIX I) (+ -1 (N)))
                 (NOT (LEFT-SYNCHRONIZED-P (+ 1 (UAV-ID-FIX I)) ENS))
                 (EQUAL (UAV->DIRECTION (ITH-UAV I ENS))
                        1)
                 )
            (LEFT-SYNCHRONIZED-P (+ 1 (UAV-ID-FIX I))
                  (STEP-TIME (+ (UAV-RIGHT-BOUNDARY (ITH-UAV I ENS))
                                (* -1 (UAV->LOCATION (ITH-UAV I ENS))))
                             ENS)))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable
                        not-left-synchronized-p-property
                        not-left-synchronized-p-implies-within-segment
                        )
            :do-not '(fertilize)
            :use ((:instance location-linear
                             (i i)
                             (j (+ 1 (uav-id-fix i)))
                             (ens (STEP-TIME (+ (UAV-RIGHT-BOUNDARY (ITH-UAV I ENS))
                                                (* -1 (UAV->LOCATION (ITH-UAV I ENS))))
                                             ENS)))))
           (and stable-under-simplificationp
                '(:expand (:free (dt ens) (LEFT-SYNCHRONIZED-p (+ 1 (UAV-ID-FIX I)) (step-time dt ens)))))
           (average-hint)
           ))

 ;;
 ;; I think you could prove this using (left-boundary ) and then
 ;; turn off left->right in the final proof.  That would simplify
 ;; things.
 ;;
 (with-arithmetic
  (with-average-theory
   (defthm goal-2
   ;; This uses FLIP-STEP-TO-RIGHT-BOUNDARY
   (IMPLIES (AND (WF-ESCORT-P ENS)
                 (STEP-TIME-ALWAYS-TERMINATES)
                 (ALL-have-met-LEFT ENS)
                 (ALL-LTE-ARE-LEFT-SYNCHRONIZED I ENS)
                 (<= (+ 2 (UAV-ID-FIX I)) (N))
                 (< (UAV-ID-FIX I) (+ -1 (N)))
                 (NOT (LEFT-SYNCHRONIZED-P (+ 1 (UAV-ID-FIX I)) ENS))
                 (< (UAV->DIRECTION (ITH-UAV I ENS)) 0))
            (LEFT-SYNCHRONIZED-P (+ 1 (UAV-ID-FIX I))
                  (STEP-TIME (+ (UAV-RIGHT-BOUNDARY (ITH-UAV I ENS))
                                (* -1 (UAV-LEFT-BOUNDARY (ITH-UAV I ENS))))
                             ens)))
   :hints (("Goal" :do-not-induct t
            :do-not '(fertilize)
            :in-theory (e/d (NNRAT-P
                             nnrat-fix
                             DEGENERATE-ITH-UAV
                             NOT-LEFT-SYNCHRONIZED-P-PROPERTY
                             not-LEFT-SYNCHRONIZED-p-property
                             not-left-synchronized-p-direction-implies-event
                             not-left-synchronized-p-implies-within-segment)
                            (REWRITE-LEFT-BOUNDARY-TO-RIGHT-BOUNDARY
                             EVENT-FOR-UAV-RIGHT EVENT-FOR-UAV-left))
            :use ((:instance location-linear
                             (i i)
                             (j (+ 1 (uav-id-fix i)))
                             (ens (STEP-TIME (+ (UAV-RIGHT-BOUNDARY (ITH-UAV I ENS))
                                                (* -1 (UAV-LEFT-BOUNDARY (ITH-UAV I ENS))))
                                             ens)))))
           (and stable-under-simplificationp
                '(:expand (:free (ens) (LEFT-SYNCHRONIZED-p (+ 1 (UAV-ID-FIX I)) ens))))
           (and stable-under-simplificationp
                '(:in-theory (enable REWRITE-LEFT-BOUNDARY-TO-RIGHT-BOUNDARY)))
           ))))

 (defthm left-synchronized-p-time-to-left-synchronized
   (IMPLIES (AND (WF-ESCORT-P ENS)
                 (STEP-TIME-ALWAYS-TERMINATES)
                 (ALL-have-met-LEFT ENS)
                 (ALL-LTE-ARE-LEFT-SYNCHRONIZED I ENS)
                 (<= (+ 2 (UAV-ID-FIX I)) (N)))
            (LEFT-SYNCHRONIZED-P (+ 1 (UAV-ID-FIX I))
                  (STEP-TIME (TIME-TO-LEFT-SYNCHRONIZED I ENS) ENS)))
   :otf-flg t
   :hints (("Goal" :in-theory (e/d (;;try
                                    time-to-left-synchronized)
                                   (REWRITE-LEFT-BOUNDARY-TO-RIGHT-BOUNDARY

                                    ))
            :do-not-induct t)))

 )

(local-preamble

 (defthm goal-2
   ;; This uses step-to-left-boundary
   (IMPLIES
    (AND (WF-ESCORT-P ENS)
         (STEP-TIME-ALWAYS-TERMINATES)
         (ALL-have-met-RIGHT ENS)
         (ALL-GTE-ARE-RIGHT-SYNCHRONIZED I ENS)
         (<= 1 (UAV-ID-FIX I))
         (NOT (RIGHT-SYNCHRONIZED-P (+ -1 (UAV-ID-FIX I)) ENS))
         (EQUAL (UAV->DIRECTION (ITH-UAV I ENS))
                -1))
    (RIGHT-SYNCHRONIZED-P
     (+ -1 (UAV-ID-FIX I))
     (STEP-TIME (+ (UAV->LOCATION (ITH-UAV I ENS))
                   (* -1
                      (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX I)) ENS))))
                ENS)))
   :hints (("Goal" :do-not-induct t
            :do-not '(fertilize)
            :in-theory (enable not-RIGHT-SYNCHRONIZED-p-property
                               not-right-synchronized-p-implies-within-segment)
            :use ((:instance location-linear
                             (i (+ -1 (uav-id-fix i)))
                             (j i)
                             (ens (STEP-TIME (+ (UAV->LOCATION (ITH-UAV I ENS))
                                                (* -1
                                                   (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX I)) ENS))))
                                             ENS)))))
           (and stable-under-simplificationp
                '(:expand (:free (dt ens) (RIGHT-SYNCHRONIZED-p (+ -1 (UAV-ID-FIX I)) (step-time dt ens)))))
           (average-hint)
           )
   )

 (with-arithmetic
  (with-average-theory
   (defthm goal-1
     ;; This uses flip-step-to-left-boundary
     (IMPLIES
      (AND (WF-ESCORT-P ENS)
           (STEP-TIME-ALWAYS-TERMINATES)
           (ALL-have-met-RIGHT ENS)
           (ALL-GTE-ARE-RIGHT-SYNCHRONIZED I ENS)
           (<= 1 (UAV-ID-FIX I))
           (NOT (RIGHT-SYNCHRONIZED-P (+ -1 (UAV-ID-FIX I)) ENS))
           (EQUAL (UAV->DIRECTION (ITH-UAV I ENS))
                  1))
      (RIGHT-SYNCHRONIZED-P
       (+ -1 (UAV-ID-FIX I))
       (STEP-TIME (+ (UAV-RIGHT-BOUNDARY (ITH-UAV I ENS))
                     (* -1
                        (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX I)) ENS))))
                  ENS)))
     :hints (;; Note: we don't want to open "event-for-uav" ..
             ("Goal" :in-theory (e/d (nnrat-fix
                                      not-RIGHT-SYNCHRONIZED-p-property
                                      not-right-synchronized-p-direction-implies-event
                                      not-right-synchronized-p-implies-within-segment
                                      )
                                     (EVENT-FOR-UAV-RIGHT EVENT-FOR-UAV-left))
              :use ((:instance location-linear
                               (i (+ -1 (uav-id-fix i)))
                               (j i)
                               (ens (STEP-TIME (+ (UAV-RIGHT-BOUNDARY (ITH-UAV I ENS))
                                                  (* -1
                                                     (UAV-RIGHT-BOUNDARY (ITH-UAV (+ -1 (UAV-ID-FIX I)) ENS))))
                                               ENS))))
              :expand (:free (dt ens) (RIGHT-SYNCHRONIZED-P (+ -1 (UAV-ID-FIX I)) (STEP-TIME dt ens))))
             ))))

 (defthm right-synchronized-p-time-to-right-synchronized
   (IMPLIES (AND (uav-id-equiv J (+ -1 (UAV-ID-FIX I)))
                 (WF-ESCORT-P ENS)
                 (STEP-TIME-ALWAYS-TERMINATES)
                 (ALL-have-met-RIGHT ENS)
                 (ALL-GTE-ARE-RIGHT-SYNCHRONIZED I ENS)
                 (<= 1 (UAV-ID-FIX I)))
            (RIGHT-SYNCHRONIZED-P J (STEP-TIME (TIME-TO-RIGHT-SYNCHRONIZED I ENS) ENS)))
   :otf-flg t
   :hints (("Goal" :in-theory (e/d (time-to-right-synchronized)
                                   nil)
            :do-not-induct t))
   )

 )

(defthm time-to-left-synchronized-upper-bound-all
  (implies
   (and
    (wf-ensemble ens)
    (all-have-met-left ens)
    (ALL-LTE-ARE-LEFT-SYNCHRONIZED J ENS))
   (<= (time-to-left-synchronized j ens) (one)))
  :hints ('(:in-theory (enable time-to-left-synchronized-upper-bound)))
  :rule-classes :linear)

(defthm time-to-right-synchronized-upper-bound-all
  (implies
   (and
    (wf-ensemble ens)
    (all-have-met-right ens)
    (ALL-GTE-ARE-RIGHT-SYNCHRONIZED J ENS))
   (<= (time-to-right-synchronized j ens) (one)))
  :hints ('(:in-theory (enable time-to-right-synchronized-upper-bound)))
  :rule-classes :linear)

;; If a variable is ignored, you should not
;; fix it (!)

(defthm all-lte-left-synchronized-time-to-left-synchronized
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens)
    (all-lte-are-left-synchronized i ens)
    (uav-id-equiv j (+ 1 (uav-id-fix i))))
   (all-lte-are-left-synchronized j (step-time (time-to-LEFT-SYNCHRONIZED i ens) ens)))
  :otf-flg t
  :hints (("Goal" :do-not-induct t
           :expand (:free (ens) (ALL-LTE-ARE-LEFT-SYNCHRONIZED (+ 1 (UAV-ID-FIX I)) ens)))))

(local-preamble

 (defthm weird
   (implies
    (and
     (not (equal (N) 1))
     (ALL-GTE-ARE-RIGHT-SYNCHRONIZED 0 ENS))
    (ALL-GTE-ARE-RIGHT-SYNCHRONIZED 1 ENS))
   :hints (("Goal" :expand (ALL-GTE-ARE-RIGHT-SYNCHRONIZED 0 ENS))))

 (defthm all-gte-right-synchronized-time-to-right-synchronized
   (implies
    (and
     (wf-escort-p ens)
     (step-time-always-terminates)
     (all-have-met-right ens)
     (all-gte-are-right-synchronized i ens)
     (uav-id-equiv j (+ -1 (uav-id-fix i))))
    (all-gte-are-right-synchronized j (step-time (time-to-RIGHT-SYNCHRONIZED i ens) ens)))
   :otf-flg t
   :hints (("Goal" :do-not-induct t
            :expand ((:free (ens) (ALL-GTE-ARE-RIGHT-SYNCHRONIZED (+ -1 (UAV-ID-FIX I)) ens))))))
 )

(def::un time-to-left-synchronized-all-rec (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)
                  :measure (uav-id-fix i)))
  (if (zp i) (time-to-LEFT-SYNCHRONIZED i ens)
    (let ((time (time-to-left-synchronized-all-rec (1- i) ens)))
      (let ((dt  (time-to-LEFT-SYNCHRONIZED i (step-time time ens))))
        (seq2 dt time)))))

(def::un time-to-right-synchronized-all-rec (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)
                  :measure (nfix (- (N) (uav-id-fix i)))))
  (if (equal i (+ -1 (N))) (time-to-right-synchronized i ens)
    (let ((time (time-to-right-synchronized-all-rec (1+ i) ens)))
      (let ((dt (time-to-right-synchronized i (step-time time ens))))
        (seq2 dt time)))))

(defthm all-lte-left-synchronized-helper
  (implies
   (and
    (< 0 (uav-id-fix i))
    (left-synchronized-p i ens)
    (all-lte-are-left-synchronized (+ -1 (uav-id-fix i)) ens))
   (all-lte-are-left-synchronized i ens))
  :hints (("Goal" :expand (all-lte-are-left-synchronized i ens))))

(defthm all-gte-right-synchronized-helper
  (implies
   (and
    (< (uav-id-fix i) (+ -1 (N)))
    (right-synchronized-p i ens)
    (all-gte-are-right-synchronized (+ 1 (uav-id-fix i)) ens))
   (all-gte-are-right-synchronized i ens))
  :hints (("Goal" :expand (all-gte-are-right-synchronized i ens))))

(defthm left-synchronized-p-all-rec
  (implies
   (and
    (step-time-always-terminates)
    (wf-escort-p ens)
    (all-have-met-left ens)
    (< (uav-id-fix i) (+ -1 (N)))
    (uav-id-equiv j (+ 1 (uav-id-fix i))))
   (all-lte-are-left-synchronized j (step-time (time-to-left-synchronized-all-rec i ens) ens)))
  :hints (("Goal" :in-theory (enable all-lte-are-left-synchronized))))

(defthm all-gte-right-synchronized-N-1
  (all-gte-are-right-synchronized (+ -1 (N)) ens)
  :hints (("Goal" :expand (all-gte-are-right-synchronized (+ -1 (N)) ens))))

(defthm right-synchronized-p-all-rec
  (implies
   (and
    (step-time-always-terminates)
    (wf-escort-p ens)
    (all-have-met-right ens)
    (< 0 (uav-id-fix i))
    (uav-id-equiv j (+ -1 (uav-id-fix i))))
   (all-gte-are-right-synchronized j (step-time (time-to-right-synchronized-all-rec i ens) ens)))
  :hints (("Goal'" :induct (time-to-right-synchronized-all-rec i ens)
           :do-not-induct t)
          (pattern::hint
           (not (ALL-GTE-ARE-RIGHT-SYNCHRONIZED dt ens))
           :expand ((ALL-GTE-ARE-RIGHT-SYNCHRONIZED dt ens)))
          ))

(defthm time-to-left-synchronized-all-upper-bound
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens)
    )
   (<= (time-to-left-synchronized-all-rec i ens)
       (* (+ 1 (uav-id-fix i)) (one))))
  :hints (("Goal" :induct (time-to-left-synchronized-all-rec i ens)
           :in-theory (enable all-lte-are-left-synchronized seq2)
           :do-not-induct t
           :nonlinearp t))
  :rule-classes (:linear))

(defthm time-to-right-synchronized-all-upper-bound
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-right ens)
    )
   (<= (time-to-right-synchronized-all-rec i ens)
       (+ (* (N) (one)) (* -1 (uav-id-fix i) (one)))))
  :hints (("Goal" :induct (time-to-right-synchronized-all-rec i ens)
           :in-theory (enable all-gte-are-right-synchronized seq2)
           :do-not-induct t
           :nonlinearp t))
  :rule-classes (:linear))

(defthm time-to-left-synchronized-all-upper-bound-alt
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens)
    (< 0 (uav-id-fix i)))
   (<= (time-to-left-synchronized-all-rec (+ -1 (uav-id-fix i)) ens)
       (* (uav-id-fix i) (one))))
  :rule-classes (:linear))

(with-arithmetic
 (defthm time-to-right-synchronized-all-upper-bound-alt
   (implies
    (and
     (wf-escort-p ens)
     (step-time-always-terminates)
     (all-have-met-right ens)
     (< (uav-id-fix i) (+ -1 (N))))
    (<= (time-to-right-synchronized-all-rec (+ 1 (uav-id-fix i)) ens)
        (+ (* (N) (one))
           (* -1 (uav-id-fix i) (one))
           (* -1 (one)))))
   :rule-classes (:linear)))

(def::un time-to-left-synchronized-all (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (if (or (equal (uav-id-fix i) 0) (equal (N) 1)) 0
    (time-to-left-synchronized-all-rec (+ -1 (uav-id-fix i)) ens)))

(def::un time-to-right-synchronized-all (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (if (or (equal (uav-id-fix i) (+ -1 (N))) (equal (N) 1)) 0
    (time-to-right-synchronized-all-rec (+ 1 (uav-id-fix i)) ens)))

(with-arithmetic
 (defthmd TEE-reduction
   (equal (TEE) (* (N) (one)))
   :hints (("Goal" :in-theory (enable SEGMENT-LENGTH
                                      RIGHT-PERIMETER-BOUNDARY
                                      LEFT-PERIMETER-BOUNDARY
                                      TEE one))))
 )

(defthm uav-id-fix-upper-bound
  (< (uav-id-fix i) (N))
  :rule-classes :linear)

(with-arithmetic
 (defthm upper-bound-on-time-to-left-synchronized-all
   (implies
    (and
     (wf-escort-p ens)
     (step-time-always-terminates)
     (all-have-met-left ens))
    (<= (time-to-left-synchronized-all i ens) (- (TEE) (one))))
   :rule-classes (:linear)
   :hints (("Goal" :in-theory (enable TEE-reduction)
            :nonlinearp t)))
 )

(with-arithmetic
 (defthm upper-bound-on-time-to-right-synchronized-all
   (implies
    (and
     (wf-escort-p ens)
     (step-time-always-terminates)
     (all-have-met-right ens))
    (<= (time-to-right-synchronized-all i ens) (- (TEE) (one))))
   :rule-classes (:linear)
   :hints (("Goal" :in-theory (enable TEE-reduction)
            :nonlinearp t)))
 )

(defthm left-synchronized-p-time-to-left-synchronized-all
  (implies
   (and
    (wf-escort-p ens)
    (all-have-met-left ens)
    (step-time-always-terminates))
   (all-lte-are-left-synchronized i (step-time (time-to-left-synchronized-all i ens) ens)))
  :hints ((pattern::hint
           (:or (:and (not (ALL-LTE-ARE-LEFT-SYNCHRONIZED 0 ENS))
                      (:bind (i 0)))
                (:and (equal (N) 1)
                      (:literally i ens)))
           :expand ((ALL-LTE-ARE-LEFT-SYNCHRONIZED I ENS)))
          ))

(defthm right-synchronized-p-time-to-right-synchronized-all
  (implies
   (and
    (wf-escort-p ens)
    (all-have-met-right ens)
    (step-time-always-terminates))
   (all-gte-are-right-synchronized i (step-time (time-to-right-synchronized-all i ens) ens)))
  :hints ((pattern::hint
           (:and (equal (N) 1)
                 (:literally i ens))
           :expand ((ALL-GTE-ARE-RIGHT-SYNCHRONIZED I ENS)))
          ))

(in-theory (disable time-to-left-synchronized-all time-to-right-synchronized-all))

(local-preamble
 (with-arithmetic
 (defthm time-to-left-synchronized-step-time-reduction
   (implies
    (and
     (wf-escort-p ens)
     (wf-escort-p ens)
     (all-have-met-left ens)
     (step-time-always-terminates))
    (equal (step-time (+ (TEE) (* -1 (one))) ens)
           (step-time
            (- (- (TEE) (one)) (time-to-left-synchronized-all i ens))
            (step-time (time-to-left-synchronized-all i ens) ens))))
   :hints (("Goal" :in-theory (enable nnrat-fix NNRAT-P STEP-TIME-COMPOSITION))))
 )

(defthmd all-lte-left-synchronized-time-to-left-synchronized-all
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens))
   (all-lte-are-left-synchronized i (step-time (+ (TEE) (* -1 (one))) ens)))
  :hints (("Goal" :do-not-induct t)))
)

(local-preamble
 (with-arithmetic
  (defthm time-to-right-synchronized-step-time-reduction
    (implies
     (and
      (wf-escort-p ens)
      (wf-escort-p ens)
      (all-have-met-right ens)
      (step-time-always-terminates))
     (equal (step-time (+ (TEE) (* -1 (one))) ens)
            (step-time
             (- (- (TEE) (one)) (time-to-right-synchronized-all i ens))
             (step-time (time-to-right-synchronized-all i ens) ens))))
    :hints (("Goal" :in-theory (enable nnrat-fix NNRAT-P STEP-TIME-COMPOSITION))))
  )

 (defthmd all-gte-right-synchronized-time-to-right-synchronized-all
   (implies
    (and
     (wf-escort-p ens)
     (step-time-always-terminates)
     (all-have-met-right ens))
    (all-gte-are-right-synchronized i (step-time (+ (TEE) (* -1 (one))) ens)))
   :hints (("Goal" :do-not-induct t)))
 )

(defthm left-synchronized-p-tee-1
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens))
   (left-synchronized-p i (step-time (+ (TEE) (* -1 (one))) ens)))
  :hints (("Goal" :use all-lte-left-synchronized-time-to-left-synchronized-all)))

(defthm right-synchronized-p-tee-1
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-right ens))
   (right-synchronized-p i (step-time (+ (TEE) (* -1 (one))) ens)))
  :hints (("Goal" :use all-gte-right-synchronized-time-to-right-synchronized-all)))

(defun-sk all-left-synchronized (ens)
  (forall (i) (LEFT-SYNCHRONIZED-p i ens))
  :strengthen t)

(quant::congruence all-left-synchronized (ens)
  (forall (i) (LEFT-SYNCHRONIZED-p i ens))
  :congruences ((ens uav-list-equiv)))

(in-theory (disable all-left-synchronized))

(defthm all-left-synchronized-implies
  (implies
   (all-left-synchronized ens)
   (left-synchronized-p i ens)))

(defthm all-left-synchronized-implies-all-lte-are-left-synchronized
  (implies
   (all-left-synchronized ens)
   (all-lte-are-left-synchronized i ens))
  :hints (("Goal" :in-theory (enable all-lte-are-left-synchronized))))

(defthm all-left-synchronized-flip-on-events-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens)
    (all-left-synchronized ens))
   (all-left-synchronized (flip-on-events ens)))
  :hints (("GOal" :expand (all-left-synchronized (flip-on-events ens))
           :do-not-induct t)))

(defthm all-left-synchronized-step-time-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens)
    (all-left-synchronized ens))
   (all-left-synchronized (step-time dt ens)))
  :hints (("GOal" :expand (all-left-synchronized (step-time dt ens))
           :do-not-induct t)))

(defthm all-left-synchronized-time-to-left-synchronized-all
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-left ens))
   (all-left-synchronized (step-time (+ (TEE) (* -1 (one))) ens)))
  :hints (("Goal" :in-theory (e/d (all-left-synchronized) nil))))

(defun-sk all-right-synchronized (ens)
  (forall (i) (RIGHT-SYNCHRONIZED-p i ens))
  :strengthen t)

(quant::congruence all-right-synchronized (ens)
  (forall (i) (RIGHT-SYNCHRONIZED-p i ens))
  :congruences ((ens uav-list-equiv)))

(in-theory (disable all-right-synchronized))

(defthm all-right-synchronized-implies
  (implies
   (all-right-synchronized ens)
   (right-synchronized-p i ens)))

(defthm all-right-synchronized-implies-all-gte-are-right-synchronized
  (implies
   (all-right-synchronized ens)
   (all-gte-are-right-synchronized i ens))
  :hints (("Goal" :in-theory (enable all-gte-are-right-synchronized))))

(defthm all-right-synchronized-flip-on-events-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-right ens)
    (all-right-synchronized ens))
   (all-right-synchronized (flip-on-events ens)))
  :hints (("GOal" :expand (all-right-synchronized (flip-on-events ens))
           :do-not-induct t)))

(defthm all-right-synchronized-step-time-invariant
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-right ens)
    (all-right-synchronized ens))
   (all-right-synchronized (step-time dt ens)))
  :hints (("GOal" :expand (all-right-synchronized (step-time dt ens))
           :do-not-induct t)))

(defthm all-right-synchronized-time-to-right-synchronized-all
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates)
    (all-have-met-right ens))
   (all-right-synchronized (step-time (+ (TEE) (* -1 (one))) ens)))
  :hints (("Goal" :in-theory (e/d (all-right-synchronized) nil))))

(with-arithmetic
 (defthm one-is-lte-tee
   (<= (one) (TEE))
   :rule-classes (:linear)
   :hints (("Goal" :in-theory (enable
                               segment-length
                               LEFT-PERIMETER-BOUNDARY
                               RIGHT-PERIMETER-BOUNDARY
                               one tee))))
 )
(with-arithmetic
 (defthm when-one-is-lt-tee
   (implies
    (< 1 (N))
    (< (one) (TEE)))
   :rule-classes (:linear)
   :hints (("Goal" :in-theory (enable
                               segment-length
                               LEFT-PERIMETER-BOUNDARY
                               RIGHT-PERIMETER-BOUNDARY
                               one tee))))
 )

(def::un 2TEE-1 ()
  (declare (xargs :signature (() nnrat-p)))
  (seq2 (- (TEE) (one)) (TEE)))

(with-arithmetic
 (defthm TEE-<-2TEE-1
   (implies
    (< 1 (N))
    (< (TEE) (2TEE-1)))
   :hints (("Goal" :in-theory (enable RIGHT-PERIMETER-BOUNDARY
                                      LEFT-PERIMETER-BOUNDARY
                                      SEGMENT-LENGTH
                                      seq2
                                      tee
                                      one)))
   :rule-classes (:linear)))

(defthm one-uav-is-already-synchronized
  (implies
   (and
    (wf-escort-p ens)
    (equal (N) 1))
   (and (ALL-have-met-LEFT ENS)
        (ALL-have-met-RIGHT ENS)
        (ALL-LEFT-SYNCHRONIZED ENS)
        (ALL-RIGHT-SYNCHRONIZED ENS)))
  :hints (("Goal" :in-theory (enable ALL-have-met-LEFT
                                     have-met-LEFT-P
                                     ALL-have-met-RIGHT
                                     have-met-RIGHT-P
                                     ALL-LEFT-SYNCHRONIZED
                                     ALL-RIGHT-SYNCHRONIZED))))

(defthm left-synchronization-helper
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates))
   (all-left-synchronized (step-time (2TEE-1) ens)))
  :hints (("Goal" :cases ((< 1 (N)))
           :in-theory (e/d (introduce-flip-on-events-generic)
                           (step-time-flip-on-events))
           :restrict ((introduce-flip-on-events-generic ((ens (STEP-TIME (TEE) ENS))))))
          ))

(with-arithmetic
 (defthm left-synchronization
   (implies
    (and
     (wf-escort-p ens)
     (step-time-always-terminates))
    (all-left-synchronized (step-time (- (* 2 (TEE)) (one)) ens)))
   :hints (("Goal" :in-theory (e/d (seq2) (STEP-TIME-SEQ2))
            :use left-synchronization-helper)))
)

(defthm right-synchronization-helper
  (implies
   (and
    (wf-escort-p ens)
    (step-time-always-terminates))
   (all-right-synchronized (step-time (2TEE-1) ens)))
  :hints (("Goal" :cases ((< 1 (N)))
           :in-theory (e/d (introduce-flip-on-events-generic)
                                  (step-time-flip-on-events))
           :restrict ((introduce-flip-on-events-generic ((ens (STEP-TIME (TEE) ENS))))))
          ))

(with-arithmetic
 (defthm right-synchronization
   (implies
    (and
     (wf-escort-p ens)
     (step-time-always-terminates))
    (all-right-synchronized (step-time (- (* 2 (TEE)) (one)) ens)))
   :hints (("Goal" :in-theory (e/d (seq2) (STEP-TIME-SEQ2))
            :use right-synchronization-helper)))
)

(in-theory (disable REWRITE-LEFT-BOUNDARY-TO-RIGHT-BOUNDARY))

(defthm synchronized-event-left
  (implies
   (and
    (< (uav->direction (ith-uav i ens)) 0)
    (equal (uav->location (ith-uav i ens))
           (uav-left-boundary (ith-uav i ens)))
    (wf-ensemble ens)
    (all-have-met-left ens)
    (all-have-met-right ens)
    (all-left-synchronized ens)
    (all-right-synchronized ens))
   (event-for-uav i ens)))

(defthm synchronized-event-right
  (implies
   (and
    (< 0 (uav->direction (ith-uav i ens)))
    (equal (uav->location (ith-uav i ens))
           (uav-right-boundary (ith-uav i ens)))
    (wf-ensemble ens)
    (all-have-met-left ens)
    (all-have-met-right ens)
    (all-left-synchronized ens)
    (all-right-synchronized ens))
   (event-for-uav i ens)))

(in-theory (disable LOCAL-SYNCHRONIZED-EVENT))

(defthm synchronized-double-containment
  (implies
   (and
    (wf-ensemble ens)
    (all-have-met-left ens)
    (all-have-met-right ens)
    (all-left-synchronized ens)
    (all-right-synchronized ens))
   (and
    (<= (uav-left-boundary (ith-uav i ens))
        (uav->location (ith-uav i ens)))
    (<= (uav->location (ith-uav i ens))
        (uav-right-boundary (ith-uav i ens)))))
  :rule-classes :linear)

(in-theory (disable local-synchronized-double-containment))

(defun step-time-termination (ens)
  (declare (ignore ens))
  (step-time-always-terminates))

(defthm step-time-termination-rule
  (implies
   (step-time-always-terminates)
   (step-time-termination ens))
  :rule-classes (:type-prescription))

(defthm step-time-termination-forward
  (implies
   (step-time-termination ens)
   (step-time-always-terminates))
  :rule-classes (:forward-chaining))

(defun synchronized (ens)
  (and (step-time-termination ens)
       (wf-ensemble ens)
       (escort-condition ens)
       (all-have-met-left ens)
       (all-have-met-right ens)
       (all-left-synchronized ens)
       (all-right-synchronized ens)))

(defthm fully-synchronized-in-2T-1
  (implies
   (and
    (step-time-always-terminates)
    (wf-escort-p ens))
   (synchronized (step-time (2TEE-1) ens)))
  :hints (("GOal" :cases ((< 1 (N)))
           :in-theory (disable (2TEE-1) 2TEE-1))))

;; You might be able to generalize a
;; macro like this to accept parameterized
;; types.
(def::type-properties synchronized (ens)
  :rewrite t)

(defun id-equiv (x y)
  (equal (uav->id x)
         (uav->id y)))

(defequiv id-equiv)

(defcong id-equiv equal (uav->id x) 1)

(in-theory (disable id-equiv))

(include-book "centaur/misc/universal-equiv" :dir :system)

(def-universal-equiv ith-uav-id-equiv
  :qvars (i)
  :equiv-terms ((id-equiv (ith-uav i x))))

(defcong ith-uav-id-equiv id-equiv (ith-uav i x) 2
  :hints (("Goal" :use (:instance ith-uav-id-equiv-necc
                                  (x x)
                                  (y x-equiv)))))

(defcong id-equiv equal (uav-left-boundary uav) 1
  :hints (("Goal" :in-theory (enable uav-left-boundary))))

(defcong id-equiv equal (uav-right-boundary uav) 1
  :hints (("Goal" :in-theory (enable uav-right-boundary))))

(defthm ith-uav-id-equiv-flip-on-events
  (ith-uav-id-equiv (flip-on-events ens)
                    ens)
  :hints (("Goal" :in-theory (enable ith-uav-id-equiv ID-EQUIV))))

(defthm ith-uav-id-equiv-update-location-all
  (ith-uav-id-equiv (update-location-all dt ens)
                    ens)
  :hints (("Goal" :in-theory (enable ith-uav-id-equiv ID-EQUIV))))

(defthm ith-uav-id-equiv-uav-list-fix
  (ITH-UAV-ID-EQUIV (UAV-LIST-FIX ENS)
                    ENS)
  :hints (("Goal" :in-theory (enable ith-uav-id-equiv ID-EQUIV))))

(defthm ith-uav-id-equiv-step-time
  (ith-uav-id-equiv (step-time dt ens)
                    ens)
  :hints (("Goal" :induct (step-time dt ens)
           :expand (step-time dt ens))))

(in-theory (disable synchronized))

(defun seq-fn (args)
  (if (not (consp args)) 0
    (if (not (consp (cdr args))) (car args)
      `(seq2 ,(seq-fn (cdr args))
             ,(car args)))))

(defmacro seq (&rest args)
  (seq-fn args))

(def::un home-to-left-time (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (let ((uav (ith-uav i ens)))
    (nnrat-fix (- (uav->location uav)
                  (uav-left-boundary uav)))))

(def::un right-to-left-time (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (let ((uav (ith-uav i ens)))
    (nnrat-fix (- (uav-right-boundary uav)
                  (uav-left-boundary uav)))))

(def::un right-to-home-time (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (let ((uav (ith-uav i ens)))
    (nnrat-fix (- (uav-right-boundary uav)
                  (uav->location uav)))))

(def::un step-to-left (dt ens)
  (declare (xargs :fty ((nnrat uav-list) uav-list)))
  (flip-on-events (step-time dt ens)))

(defthm ith-uav-id-equiv-step-to-left
  (ith-uav-id-equiv (step-to-left dt ens)
                    ens))

(def::signature step-to-left (t synchronized) synchronized)

(def::un left-to-home-time (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (let ((uav (ith-uav i ens)))
    (nnrat-fix (- (uav->location uav)
                  (uav-left-boundary uav)))))

(def::un home-to-right-time (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (let ((uav (ith-uav i ens)))
    (nnrat-fix (- (uav-right-boundary uav)
                  (uav->location uav)))))

(def::un left-to-right-time (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (let ((uav (ith-uav i ens)))
    (nnrat-fix (- (uav-right-boundary uav)
                  (uav-left-boundary uav)))))

(def::un step-to-right (dt ens)
  (declare (xargs :fty ((nnrat uav-list) uav-list)))
  (flip-on-events (step-time dt ens)))

(defthm ith-uav-id-equiv-step-to-right
  (ith-uav-id-equiv (step-to-right dt ens)
                    ens))

(def::signature step-to-right (t synchronized) synchronized)

(include-book "tools/trivial-ancestors-check" :dir :system)
(use-trivial-ancestors-check)

(defthm location-step-to-right
  (implies
   (and
    (synchronized ens)
    (case-split
     (and
      (< 0 (uav->direction (ith-uav i ens)))
      (<= (nnrat-fix dt) (double-rewrite (home-to-right-time i ens))))))
   (equal (uav->location (ith-uav i (step-to-right dt ens)))
          (+ (uav->location (ith-uav i ens))
             (nnrat-fix dt)))))


(defthm direction-step-to-right
  (implies
   (and
    (synchronized ens)
    (case-split
     (and
      (or (< 0 (uav->direction (ith-uav i ens)))
          ;; DAG -- this would be the better rule.
          ;; Let's bag it for now.
          #+joe
          (equal (uav->location (ith-uav i ens))
                 (uav-left-boundary (ith-uav i ens))))
      (<= (nnrat-fix dt) (double-rewrite (home-to-right-time i ens))))))
   (equal (uav->direction (ith-uav i (step-to-right dt ens)))
          (if (equal (nnrat-fix dt) (home-to-right-time i ens))
              -1
            1))))

(defthm construct-step-to-right
  (implies
   (syntaxp (member (car dt) '(left-to-home-time home-to-right-time left-to-right-time)))
   (equal (flip-on-events (step-time dt ens))
          (step-to-right dt ens))))

(defthm construct-step-to-right-location
  (implies
   (syntaxp (member (car dt) '(left-to-home-time home-to-right-time left-to-right-time)))
   (equal (uav->location (ith-uav i (step-time dt ens)))
          (uav->location (ith-uav i (step-to-right dt ens))))))

(in-theory (disable step-to-right))

(defthm location-step-to-left
  (implies
   (and
    (synchronized ens)
    (case-split
     (and
      (< (uav->direction (ith-uav i ens)) 0)
      (<= (nnrat-fix dt) (double-rewrite (home-to-left-time i ens))))))
   (equal (uav->location (ith-uav i (step-to-left dt ens)))
          (+ (uav->location (ith-uav i ens))
             (- (nnrat-fix dt)))))
  :hints (("Goal" :do-not-induct t)))

(defthm direction-step-to-left
  (implies
   (and
    (synchronized ens)
    (case-split
     (and
      (< (uav->direction (ith-uav i ens)) 0)
      (<= (nnrat-fix dt) (double-rewrite (home-to-left-time i ens))))))
   (equal (uav->direction (ith-uav i (step-to-left dt ens)))
          (if (equal (nnrat-fix dt) (home-to-left-time i ens))
              1
            -1))))

(defthm construct-step-to-left
  (implies
   (syntaxp (member (car dt) '(right-to-home-time home-to-left-time right-to-left-time)))
   (equal (flip-on-events (step-time dt ens))
          (step-to-left dt ens))))

(defthm construct-step-to-left-location
  (implies
   (syntaxp (member (car dt) '(right-to-home-time home-to-left-time right-to-left-time)))
   (equal (uav->location (ith-uav i (step-time dt ens)))
          (uav->location (ith-uav i (step-to-left dt ens))))))

(in-theory (disable step-to-left))

(def::und converged-period (i ens)
  (declare (xargs :fty ((uav-id uav-list) nnrat)))
  (let ((uav (ith-uav i ens)))
    (cond
     ((equal (uav->location uav)
             (uav-left-boundary uav))
      (seq (home-to-right-time i ens)
           (right-to-left-time i ens)
           (left-to-home-time  i ens)))
     ((equal (uav->location uav)
             (uav-right-boundary uav))
      (seq (home-to-left-time i ens)
           (left-to-right-time i ens)
           (right-to-home-time i ens)))
     ((< 0 (uav->direction uav))
      (seq (home-to-right-time i ens)
           (right-to-left-time i ens)
           (left-to-home-time  i ens)))
     (t
      (seq (home-to-left-time i ens)
           (left-to-right-time i ens)
           (right-to-home-time i ens))))))

(with-arithmetic
 (defthmd converged-period-length
   (implies
    (synchronized ens)
    (equal (converged-period i ens)
           (* 2 (one))))
   :hints (("Goal" :in-theory (enable
                               converged-period
                               width-of-segment-is-segment-length
                               one nnrat-p nnrat-fix seq2)))))

(defthm introduce-flip-on-events-after-step-time
  (implies
   (and
    (syntaxp (equal (car ens) 'step-time))
    (synchronized ens))
   (equal (step-time dt ens)
          (if (equal (nnrat-fix dt) 0)
              ens
            (step-time dt (flip-on-events ens))))))

(in-theory (disable step-time-flip-on-events))

(defthm equal-seq-2-zero
  (iff (equal (seq2 a b) 0)
       (equal (+ (nnrat-fix a) (nnrat-fix b)) 0))
  :hints (("Goal" :in-theory (enable seq2))))

(defthm equal-ith-uav-to-uav-equiv
  (iff (equal (ith-uav i ens1) (ith-uav j ens2))
       (uav-equiv (ith-uav i ens1) (ith-uav j ens2)))
  :hints (("Goal" :in-theory (enable uav-equiv))))

(in-theory (enable left-boundary-is-smaller))

#+joe
(local-preamble

 (with-arithmetic
  (defthmd ith-uav-step-time-location-converged-period-helper
    (implies
     (synchronized ens)
     (equal (UAV->location (ith-uav i (step-time (converged-period i ens) ens)))
            (UAV->location (ith-uav i ens))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (converged-period)
                             (home-to-right-time
                              right-to-left-time left-to-home-time
                              home-to-left-time left-to-right-time right-to-home-time
                              ith-uav-flip-on-events)))
            (pattern::hint
             (:either (equal (LEFT-TO-HOME-TIME I ENS) 0))
             :name expand-left-to-home
             :expand ((LEFT-TO-HOME-TIME I ENS)))
            (pattern::hint
             (:either (equal (RIGHT-TO-LEFT-TIME I ENS) 0))
             :name expand-right-to-left
             :expand ((RIGHT-TO-LEFT-TIME I ENS)))
            )))

 (defthmd ith-uav-step-time-location-converged-period
   (implies
    (synchronized ens)
    (equal (UAV->location (ith-uav i (step-time (* 2 (one)) ens)))
           (UAV->location (ith-uav i ens))))
    :hints (("Goal" :use ith-uav-step-time-converged-period-helper
            :in-theory (enable converged-period-length))))
 )

(local-preamble

 (with-arithmetic
  (defthmd ith-uav-step-time-converged-period-helper
    (implies
     (synchronized ens)
     (equal (ith-uav i (flip-on-events (step-time (converged-period i ens) (flip-on-events ens))))
            (ith-uav i (flip-on-events ens))))
    :hints (("Goal" :do-not-induct t
             :in-theory (e/d (converged-period)
                             (home-to-right-time
                              right-to-left-time left-to-home-time
                              home-to-left-time left-to-right-time right-to-home-time
                              ith-uav-flip-on-events)))
            (and stable-under-simplificationp
                 '(:in-theory (current-theory :here)))
            (and stable-under-simplificationp
                 '(:in-theory (enable uav-extensionality))))))

 (defthmd ith-uav-step-time-converged-period
   (implies
    (synchronized ens)
    (equal (ith-uav i (flip-on-events (step-time (* 2 (one)) (flip-on-events ens))))
           (ith-uav i (flip-on-events ens))))
   :hints (("Goal" :use ith-uav-step-time-converged-period-helper
            :in-theory (enable converged-period-length))))
 )

(defun-sk dpss-convergence (ens)
  (forall (i)
    (equal (ith-uav i (flip-on-events (step-time (* 2 (one)) (flip-on-events ens))))
           (ith-uav i (flip-on-events ens)))))

(local-preamble

 (defthm dpss-convergence-after-2T-1-helper-1
   (implies
    (and
     (wf-escort-p ens)
     (step-time-always-terminates))
    (dpss-convergence (step-time (2TEE-1) ens)))
   :hints (("Goal" :in-theory '(FULLY-SYNCHRONIZED-IN-2T-1
                                ITH-UAV-STEP-TIME-CONVERGED-PERIOD
                                dpss-convergence))))

 (defthm more-explicit-time
   (equal (+ (* 2 (TEE)) (* -1 (ONE)))
          (2TEE-1))
   :hints (("GOal" :in-theory (enable seq2))))

 (defthm dpss-convergence-after-2T-1-helper
   (implies
    (and
     (wf-ensemble ens)
     (step-time-always-terminates))
    (dpss-convergence (step-time (- (* 2 (TEE)) (ONE)) ens)))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (introduce-flip-on-events-symbolp)
                            (2TEE-1 (2TEE-1)
                                    dpss-convergence)))
           (pattern::hint
            (equal (2TEE-1) 0)
            :in-theory (enable ONE))
           ))

 (defthm dpss-convergence-after-2T-1
   (implies
    (and
     (wf-ensemble ens)
     (step-time-always-terminates))
    (dpss-convergence (step-time (- (* 2 (TEE)) (ONE)) ens)))
   :hints (("Goal" :in-theory '(dpss-convergence-after-2T-1-helper))))

 )

(defun-sk dpss-location-convergence (ens)
  (forall (i)
    (equal (UAV->location (ith-uav i (step-time (* 2 (one)) ens)))
           (UAV->location (ith-uav i ens)))))

(local-preamble

 (defthmd UAV->location-flip-on-events-irrelevant
   (implies
    (syntaxp (equal (car ens) 'step-time))
    (equal (UAV->location (ith-uav i ens))
           (UAV->location (ith-uav i (flip-on-events ens))))))

 (defthm flip-flip
   (implies
    (wf-ensemble ens)
    (equal (flip-on-events (flip-on-events ens))
           (flip-on-events ens))))

 (defthm dpss-location-convergence-after-2T-1-helper
   (implies
    (and
     (wf-ensemble ens)
     (step-time-always-terminates))
    (dpss-location-convergence (step-time (- (* 2 (TEE)) (ONE)) ens)))
   :hints (("Goal" :in-theory '(flip-flip
                                dpss-convergence-after-2T-1
                                T-WF-ENSEMBLE-IMPLIES-WF-ENSEMBLE-STEP-TIME
                                STEP-TIME-FLIP-ON-EVENTS
                                UAV->location-flip-on-events-irrelevant
                                dpss-location-convergence)
            :use (:instance dpss-convergence-necc
                            (i (DPSS-LOCATION-CONVERGENCE-WITNESS (STEP-TIME (- (* 2 (TEE)) (ONE)) ENS)))
                            (ens (step-time (- (* 2 (TEE)) (ONE)) ens))))
           (pattern::hint
            (EQUAL (NNRAT-FIX (* 2 (ONE))) 0)
            :in-theory (enable ONE))
           ))

 (defthm dpss-location-convergence-after-2T-1
   (implies
    (and
     (wf-ensemble ens)
     (step-time-always-terminates))
    (dpss-location-convergence (step-time (- (* 2 (TEE)) (ONE)) ens)))
   :hints (("Goal" :in-theory '(dpss-location-convergence-after-2T-1-helper))))

 )



