;;
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "../Base/flip")
(include-book "../Base/step")

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

(local (in-theory (disable rewrite-<-into-average
                           rewrite-<-into-average-alt-1
                           double-average-is-just-sum
                           reconstruct-average
                           rewrite-equality-into-just-average
                           reconstruct-average-difference
                           rewrite-equality-into-average
                           )))

;; I ran experiments with and without this:
;;
;; (local (in-average-theory))
;;
;; in  average theory: 1210s
;; in standard theory:  547s
;;
(defun initially-synchronized-p (i ens)
  (let* ((i   (uav-id-fix i))
         (uav (ith-uav i ens)))
    ;;      L     R
    ;; .....|.....|....
    ;;         x
    ;;
    (and
     (implies
      ;;
      ;; If a UAV is inside of its segment moving left then it is
      ;; synchronized with its right neighbor until it reaches
      ;; its left segment boundary.
      ;;
      (and
       (< i (1- (N)))
       (< (uav->direction uav) 0)
       (< (uav-left-boundary uav) (uav->location uav))
       (< (uav->location uav) (uav-right-boundary uav)))
      (and
       (< 0 (uav->direction (ith-uav (1+ i) ens)))
       (equal (- (uav-right-boundary uav) (uav->location uav))
              (- (uav->location (ith-uav (1+ i) ens)) (uav-right-boundary uav)))))
     (implies
      ;;
      ;; If a UAV is inside of its segment moving right then it is
      ;; is synchronized with its left neighbor until it reaches
      ;; its right segment boundary
      ;;
      (and
       (< 0 i)
       (< 0 (uav->direction uav))
       (< (uav-left-boundary uav) (uav->location uav))
       (< (uav->location uav) (uav-right-boundary uav)))
      (and
       (< (uav->direction (ith-uav (1- i) ens)) 0)
       (equal (- (uav->location uav) (uav-left-boundary uav))
              (- (uav-left-boundary uav) (uav->location (ith-uav (1- i) ens))))))
     (implies
      ;;
      ;; If a UAV is approaching its segment from the left, it is
      ;; being escorted by its left neighbor.  When departing its left
      ;; boundary and entering the segment, it is co-incident with its
      ;; left neighbor.
      ;;
      (and
       (< 0 i)
       (< 0 (uav->direction uav))
       (<= (uav->location uav) (uav-left-boundary uav)))
      (and
       (implies
        (< (uav->location uav) (uav-left-boundary uav))
        (< 0 (uav->direction (ith-uav (1- i) ens))))
       (equal (uav->location uav)
              (uav->location (ith-uav (1- i) ens)))))
     (implies
      ;;
      ;; If a UAV is approaching its segment from the right, it is
      ;; being escorted by its right neighbor.  When departing its right
      ;; boundary and entering the segment, it is co-incident with its
      ;; right neighbor.
      ;;
      (and
       (< i (1- (N)))
       (< (uav->direction uav) 0)
       (<= (uav-right-boundary uav) (uav->location uav)))
      (and
       (implies
        (< (uav-right-boundary uav) (uav->location uav))
        (< (uav->direction (ith-uav (1+ i) ens)) 0))
       (equal (uav->location uav)
              (uav->location (ith-uav (1+ i) ens)))))
     )))

;;(in-theory (disable FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))

(defun-sk initial-synchronization (ens)
  (forall (i) (initially-synchronized-p i ens)))

(in-theory (disable initial-synchronization))

(defthm initial-synchronization-implies-initially-synchronized-p
  (implies
   (initial-synchronization ens)
   (initially-synchronized-p i ens))
  :hints (("Goal" :in-theory (disable initially-synchronized-p))))

(encapsulate
    ()

  (local (in-theory (disable EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV)))

  (defthm degenerate-alpha-0
    (iff (equal 1 (+ (* 1/2 (N)) (* -1/2 (UAV-ID-FIX I))))
         (if (uav-id-p (+ -2 (N)))
             (uav-id-equiv I (+ -2 (N)))
           nil))
    :hints (("Goal" :in-theory (enable natp
                                       uav-id-equiv
                                       uav-id-p
                                       uav-id-fix))))

  (defthm degenerate-alpha-1
    (iff (UAV-ID-EQUIV 0 1)
         (equal (N) 1))
    :hints (("Goal" :in-theory (enable uav-id-equiv
                                       uav-id-p
                                       uav-id-fix))))

  )

(encapsulate
    ()

  (local (include-arithmetic))

  (defthmd alt-right-perimeter-boundary
    (equal (right-perimeter-boundary)
           (* (N) (segment-length)))
    :hints (("GOal" :in-theory (enable right-perimeter-boundary segment-length))))

  )

(encapsulate
    ()

  (defthm initially-synchronized-p-flip-on-events-helper
    (implies
     (and
      (wf-ensemble ens)
      (escort-condition ens)
      (initially-synchronized-p i ens))
     (initially-synchronized-p i (flip-on-events ens)))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable flip-uav))
            (pattern::hint*
             ordering-rule
             balanced-average
             location-pinching-rule
             escort-condition-implies
             )
            (average-hint)
            ))

  (defthm initial-synchronization-flip-on-events
    (implies
     (and
      (wf-ensemble ens)
      (escort-condition ens)
      (initial-synchronization ens))
     (initial-synchronization (flip-on-events ens)))
    :hints (("Goal" :do-not-induct t
             :in-theory (disable initially-synchronized-p)
             :expand (initial-synchronization (flip-on-events ens)))))


  )

(in-theory (disable chasing-neighbor))

;; Painfully slow .. Subgoal 197.17.3.2
;; it would be nice to figure out what is going on (?)
;;
;;

(encapsulate
    ()

  (local
   (without-subsumption
    (defthmd initially-synchronized-p-update-location-all-helper
      (implies
       (and
        (wf-ensemble ens)
        (escort-condition ens)
        ;; (implies
        ;;  (< (uav-id-fix i) (+ -1 (N)))
        ;;  (escort-condition-p i (+ 1 (uav-id-fix i)) ens))
        ;; (implies
        ;;  (< 0 (uav-id-fix i))
        ;;  (escort-condition-p (+ -1 (uav-id-fix i)) i ens))
        (lte-min-time-to-impending-impact-event dt ens)
        (implies
          (and
           (not (chasing-neighbor (+ -1 (uav-id-fix I)) ens))
           (< 0 (uav-id-fix I)))
          (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV (+ -1 (uav-id-fix I)) ENS)))
         (implies
          (and
           (not (chasing-neighbor (+ 1 (uav-id-fix I)) ens))
           (< (uav-id-fix I) (+ -1 (N))))
          (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV (+ 1 (uav-id-fix I)) ENS)))
         (implies
          (not (chasing-neighbor i ens))
          (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
         (initially-synchronized-p i ens))
        (initially-synchronized-p i (update-location-all dt ens)))
      :hints (("Goal" :do-not-induct t
               :in-theory (disable CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV))
              ;;(except "Subgoal 200.17.3.2" :print nil)
              ;;(except "Subgoal 197.17.3.2" :print nil)
              ;;(and stable-under-simplificationp
              ;;     '(:do-not '(preprocess)))
              (pattern::hint*
               ordering-rule
               expand-chasing-neighbor
               expand-min-time-to-impact-for-uav
               ;;balanced-average
               location-pinching-rule
               escort-condition-implies
               )

              )))
  )

  (defthm initially-synchronized-p-update-location
    (implies
     (and
      (wf-ensemble ens)
      (escort-condition ens)
      (lte-min-time-to-impending-impact-event dt ens)
      (initially-synchronized-p i ens))
     (initially-synchronized-p i (update-location-all dt ens)))
    :hints (("Goal" :do-not-induct t
             :use initially-synchronized-p-update-location-all-helper
             :in-theory (e/d (CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV)
                             (initially-synchronized-p)))
            ))
  )

(defthm event-for-uav-ensures-initially-synchronized-p
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (event-for-uav i ens))
   (initially-synchronized-p i (flip-on-events ens)))
  :hints (("Goal" :do-not-induct t)
          (and stable-under-simplificationp
               '(:in-theory (enable flip-uav
                                    ESCORT-EVENT-FOR-UAV
                                    impact-event-for-uav)))
          (pattern::hint*
           escort-condition-implies
           ordering-rule
           )))


