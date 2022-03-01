;;
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")
(include-book "../Base/step-time")

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

;; ===================================================================
;;
;; This file provides a formalization of the two main invariants in
;; the Avigad/van Doorn proof of DPSS-A convergnece time relative to
;; our base model of DPSS-A.
;;
;; ===================================================================

;; ===================================================================
;;
;; Have Met (left)
;;
;; From the hand proof:
;;
;; "We say that [two drones] 'have met' by time t if either they
;;  started together, moving in the same direction, or they have been
;;  involved in a meet or bounce event"
;;
;; Technically, this property really says that two UAVs have
;; sychronized on their shared boundary.  To the point: an escort
;; event is not sufficient to guarantee have-met-Left-p; an actual
;; event is required.
;;
;; ===================================================================
(def::un have-met-Left-p (i ens)
  (declare (xargs :fty ((uav-id uav-list) bool)))
  (let ((uavi  (ith-uav i ens))
        (right (ith-uav (+ i 1) ens)))
    (implies
      (and
       ;;
       ;; Consider all but the rightmost UAV ..
       ;;
       (< i (+ -1 (N)))
       ;;
       ;; If UAVi is moving left ..
       ;;
       (< (UAV->direction uavi) 0))
      (and
       (implies
        ;;
        ;; .. if it is right of its rightmost boundary ..
        ;;
        (< (UAV-right-boundary uavi) (UAV->location uavi))
        (and
         ;;
         ;; .. then the right UAV is escorting UAVi back
         ;; to their shared boundary (ie: they have the same
         ;; direction and location).
         ;;
         ;;     I
         ;; |--------|--------|
         ;;             <<
         (< (UAV->direction right) 0)
         (equal (UAV->location uavi) (UAV->location right))))
       (implies
        ;;
        ;; .. If the UAV is in its segment but not on the
        ;; left boundary ..
        ;;
        (and (<= (UAV->location uavi) (UAV-right-boundary uavi))
             (<  (UAV-left-boundary uavi) (UAV->location uavi)))
        (and
         ;;
         ;; Then the right UAV is moving right if it is left of
         ;; our right boundary ..
         ;;
         (implies
          (< (UAV->location uavi) (UAV-right-boundary uavi))
          (< 0 (UAV->direction right)))
         ;;
         ;; .. and it is the same distance from the shared boarder
         ;; as the right UAV.
         ;;
         ;;
         ;;     I
         ;; |--------|--------|
         ;;       <  ^  >
         (equal (average (UAV->location uavi) (UAV->location right))
                (UAV-right-boundary uavi))))
       ))))

(def::un have-met-Right-p (i ens)
  (declare (xargs :fty ((uav-id uav-list) bool)))
  (let ((uavi  (ith-uav i ens))
        (left  (ith-uav (+ -1 i) ens)))
    (and
     (implies
      (and
       ;;
       ;; Consider all but the leftmost UAV ..
       ;;
       (< 0 i)
       ;;
       ;; If UAVi is moving right ..
       ;;
       (< 0 (UAV->direction uavi))
       ;;
       ;; .. and it is left of its leftmost boundary ..
       ;;
       (< (UAV->location uavi) (UAV-left-boundary uavi) ))
      (and
       ;;
       ;; .. then the left UAV is escorting UAVi back
       ;; to their shared boundary (ie: they have the same
       ;; direction and location).
       ;;
       ;;     I
       ;; |--------|--------|
       ;;             <<
       (< 0 (UAV->direction left))
       (equal (UAV->location uavi) (UAV->location left))))
     (implies
      (and
       ;;
       ;; Consider all but the leftmost UAV ..
       ;;
       (< 0 i)
       ;;
       ;; If UAVi is moving right ..
       ;;
       (< 0 (UAV->direction uavi))
       ;;
       ;; If the UAV is in its segment but not on the
       ;; right boundary ..
       ;;
       (and (<   (UAV->location uavi) (UAV-right-boundary uavi))
            (<=  (UAV-left-boundary uavi) (UAV->location uavi)))
       )
      (and
       ;;
       ;; Then the left UAV is moving left if we are right
       ;; of our left boundary.
       ;;
       (implies
        (< (UAV-left-boundary uavi) (UAV->location uavi))
        (< (UAV->direction left) 0))
       ;;
       ;; .. and the left UAV is the same distance from the shared boarder.
       ;;
       ;;
       ;;     I
       ;; |--------|--------|
       ;;       <  ^  >
       (equal (average (UAV->location uavi) (UAV->location left))
              (UAV-left-boundary uavi))))
     )))

(defthm event-for-uav-ensures-have-met-Left-p
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (event-for-uav i ens))
   (have-met-Left-p i (flip-on-events ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable ESCORT-EVENT-FOR-UAV
                              IMPACT-EVENT-FOR-UAV
                              flip-uav))
          (pattern::hint*
           escort-condition-implies
           ordering-rule
           )))

(defthm event-for-uav-ensures-have-met-Right-p
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (event-for-uav i ens))
   (have-met-Right-p i (flip-on-events ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable ESCORT-EVENT-FOR-UAV
                              IMPACT-EVENT-FOR-UAV
                              flip-uav))
          (pattern::hint*
           escort-condition-implies
           ordering-rule
           )))

(without-subsumption
(defthm have-met-Left-p-flip-on-events
    (implies
     (and
      (wf-ensemble ens)
      (escort-condition ens)
      (have-met-Left-p i ens))
     (have-met-Left-p i (flip-on-events ens)))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable flip-uav))
            (pattern::hint*
             balanced-average
             escort-condition-implies
             right-perimeter-escort-condition-implies
             )
            )))

(without-subsumption
(defthm have-met-Right-p-flip-on-events
    (implies
     (and
      (wf-ensemble ens)
      (escort-condition ens)
      (have-met-Right-p i ens))
     (have-met-Right-p i (flip-on-events ens)))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable flip-uav))
            (pattern::hint*
             escort-condition-implies
             right-perimeter-escort-condition-implies
             )
            (average-hint)
            )))

(defthm lte-min-time-to-impending-impact-event-bounded-by-location-left-zero
  (implies
   (and
    (lte-min-time-to-impending-impact-event dt ens)
    (wf-ensemble ens)
    (< (uav->direction (ith-uav i ens)) 0))
   (<= (nnrat-fix dt)
       (uav->location (ith-uav i ens))))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :use lte-min-time-to-impending-impact-event-bounded-by-location-left
           :in-theory (e/d (left-perimeter-boundary)
                           (lte-min-time-to-impending-impact-event-bounded-by-location-left)))))


(local-preamble

 (with-average-theory
  (without-subsumption
   (defthmd have-met-Left-p-update-location-all-helper
     (implies
      (and
       (wf-ensemble ens)
       (escort-condition ens)
       (lte-min-time-to-impending-impact-event dt ens)
       (implies
        (not (chasing-neighbor i ens))
        (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
       (implies
        (and
         (< (uav-id-fix I) (+ -1 (N)))
         (not (chasing-neighbor (+ 1 (uav-id-fix i)) ens)))
        (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV (+ 1 (uav-id-fix i)) ENS)))
       (have-met-Left-p i ens))
      (have-met-Left-p i (update-location-all dt ens)))
     :hints (("Goal" :do-not-induct t
              :in-theory (e/d ()
                              (have-met-Left-p
                               CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV))
              :expand (have-met-Left-p i (update-location-all dt ens))
              )
             (and stable-under-simplificationp
                  '(:in-theory (disable CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV)))
             ;;(average-hint)
             (pattern::hint*
              expand-chasing-neighbor
              expand-min-time-to-impact-for-uav
              escort-condition-implies
              )
             ))))

 (defthm have-met-Left-p-update-location-all-invariant
   (implies
    (and
     (wf-ensemble ens)
     (escort-condition ens)
     (lte-min-time-to-impending-impact-event dt ens)
     (have-met-Left-p i ens))
    (have-met-Left-p i (update-location-all dt ens)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable have-met-Left-p)
            :use have-met-Left-p-update-location-all-helper
            )))

 )

(local-preamble

 (with-average-theory
  (without-subsumption
   (defthmd have-met-Right-p-update-location-all-helper
      (implies
       (and
       (wf-ensemble ens)
       (escort-condition ens)
       (lte-min-time-to-impending-impact-event dt ens)
       (implies
        (not (chasing-neighbor i ens))
        (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
       (implies
        (and
         (< 0 (uav-id-fix I))
         (not (chasing-neighbor (+ -1 (uav-id-fix i)) ens)))
        (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV (+ -1 (uav-id-fix i)) ENS)))
       (have-met-Right-p i ens))
      (have-met-Right-p i (update-location-all dt ens)))
     :hints (("Goal" :do-not-induct t
              :in-theory (e/d ()
                              (have-met-Right-p
                               CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV))
              :expand (have-met-Right-p i (update-location-all dt ens))
              )
             (and stable-under-simplificationp
                  '(:in-theory (disable CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV)))
             ;;(average-hint)
             (pattern::hint*
              expand-chasing-neighbor
              expand-min-time-to-impact-for-uav
              escort-condition-implies
              )
             ))))

 (defthm have-met-Right-p-update-location-all-invariant
   (implies
    (and
     (wf-ensemble ens)
     (escort-condition ens)
     (lte-min-time-to-impending-impact-event dt ens)
     (have-met-Right-p i ens))
    (have-met-Right-p i (update-location-all dt ens)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable have-met-Right-p)
            :use have-met-Right-p-update-location-all-helper
            )))

 )

;;
;; Jen's left synchronized definition
;;
(defun JS-p (j ens)
  (let ((j (uav-id-fix j)))
    (and
     (<= (UAV-left-boundary (ith-uav j ens)) (UAV->location (ith-uav j ens)))
     (implies
      (< 0 j)
      (or
       ;;              J
       ;; |--------|--------|
       ;;            x<
       (and
        (< (UAV->direction (ith-uav j ens)) 0)
        (equal (UAV->location (ith-uav j ens))
               (UAV->location (ith-uav (+ -1 j) ens))))
       ;;              J
       ;; |--------|--------|
       ;;        >    ^    <
       (and
        (not (equal (UAV->direction (ith-uav j ens))
                    (UAV->direction (ith-uav (+ -1 j) ens))))
        (<= (abs (- (UAV-left-boundary (ith-uav j ens)) (UAV->location (ith-uav (+ -1 j) ens))))
            (- (UAV->location (ith-uav j ens)) (UAV-left-boundary (ith-uav j ens)))))
       ;;              J
       ;; |--------|--------|
       ;;        >         >
       (and
        (< 0 (UAV->direction (ith-uav j ens)))
        (< 0 (UAV->direction (ith-uav (+ -1 j) ens)))))))))

(with-arithmetic
 (defthm JS-p-definition
  (implies
   (wf-ensemble ens)
   (equal (JS-p j ens)
          (let ((j (uav-id-fix j)))
            (and
            (<= (UAV-left-boundary (ith-uav j ens)) (UAV->location (ith-uav j ens)))
            (implies
             (< 0 j)
             (or
              (and
               (< (UAV->direction (ith-uav j ens)) 0)
               (equal (UAV->location (ith-uav j ens))
                      (UAV->location (ith-uav (+ -1 j) ens))))
              (and
               (not (equal (UAV->direction (ith-uav j ens))
                           (UAV->direction (ith-uav (+ -1 j) ens))))
               (<= (UAV-left-boundary (ith-uav j ens))
                   (average (UAV->location (ith-uav (+ -1 j) ens))
                            (UAV->location (ith-uav j ens)))))
              (and
               (< 0 (UAV->direction (ith-uav j ens)))
               (< 0 (UAV->direction (ith-uav (+ -1 j) ens))))))))))
  :hints (("Goal" :in-theory (e/d (average)
                                  (rewrite-<-into-average
                                   double-average-is-just-sum
                                   reconstruct-average
                                   rewrite-equality-into-just-average
                                   reconstruct-average-difference
                                   rewrite-equality-into-average))))
  :rule-classes (:definition)))

(in-theory (disable JS-p))


(defthm degenerate-uav-id-equiv--3-0
  (iff (UAV-ID-EQUIV (+ -3 (N)) 0)
       (<= (N) 3))
  :hints (("Goal" :in-theory (e/d (uav-id-equiv)
                                  (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV)))))

;; Where was this rule?
(defthm average-same
  (implies
   (rationalp x)
   (equal (average x x) x))
  :hints (("Goal" :in-theory (e/d (average)
                                  (rewrite-<-into-average
                                   double-average-is-just-sum
                                   reconstruct-average
                                   rewrite-equality-into-just-average
                                   reconstruct-average-difference
                                   rewrite-equality-into-average)))))

;; We might try enabling this ..
;; zp-min-time-to-impact-event-is-impact-event

(encapsulate
    ()

  (defthm JS-p-0
    (implies
     (wf-ensemble ens)
     (JS-p 0 ens)))

  (local (in-theory (disable have-met-Left-p JS-p-definition)))
  (local (in-theory (enable zp-min-time-to-impact-event-is-impact-event)))

  (with-average-theory
   (defthmd JS-p-flip-on-events-helper
     (implies
      (and
       ;;(hide (always-true j))
       (< 0 (uav-id-fix j))
       (wf-ensemble ens)
       (escort-condition ens)
       ;;(homogenous-escort-direction ens)
       (have-met-Left-p (+ -1 (uav-id-fix j)) ens)
       (JS-p (+ -1 (uav-id-fix j)) ens)
       (JS-p j ens))
      (JS-p j (flip-on-events ens)))
     :hints (("Goal" :do-not-induct t
              :do-not '(fertilize)
              :expand (:free (ens) (JS-p j ens))
              :in-theory (e/d (flip-uav
                               wf-ensemble)
                              nil))
             (pattern::hint*
              ordering-rule
              escort-condition-implies
              )
             (and stable-under-simplificationp
                  '(:in-theory (enable have-met-Left-p JS-P-definition)))
             ;;(average-hint)
             )))


  )

(local-preamble
 (with-average-theory
 (local
  (without-subsumption
   (defthm JS-p-update-location-all-helper
     (implies
      (and
       (wf-ensemble ens)
       (escort-condition ens)
       ;;(homogenous-escort-direction ens)
       ;;(not (exists-uav-with-event ens))
       ;;(not (event-for-uav i ens))
       (< 0 (uav-id-fix I))
       (lte-min-time-to-impending-impact-event dt ens)
       (implies
        (not (chasing-neighbor (+ -1 (uav-id-fix i)) ens))
        (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV (+ -1 (uav-id-fix I)) ENS)))
       (implies
        (not (chasing-neighbor i ens))
        (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
       (have-met-Left-p (+ -1 (uav-id-fix I)) ens)
       (JS-p (+ -1 (uav-id-fix I)) ens)
       (JS-p I ens)
       )
      (JS-p I (update-location-all dt ens)))
     :hints (("Goal" :in-theory (disable have-met-Left-p
                                         JS-p-definition
                                         CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV)
              :expand (:Free (ens) (JS-p I ens))
              :do-not-induct t)

             (pattern::hint*
              location-pinching-rule
              ordering-rule
              escort-condition-implies
              right-perimeter-escort-condition-implies
              left-perimeter-escort-condition-implies
              expand-chasing-neighbor
              expand-min-time-to-impact-for-uav
              )

             (and stable-under-simplificationp
                  '(:in-theory (enable have-met-Left-p JS-p-definition)))

             ))
   ))

 (defthm JS-p-update-location-all-invariant
   (implies
    (and
     (wf-ensemble ens)
     (escort-condition ens)
     ;;(homogenous-escort-direction ens)
     ;;(not (exists-uav-with-event ens))
     (< 0 (uav-id-fix I))
     (lte-min-time-to-impending-impact-event dt ens)
     (have-met-Left-p (+ -1 (uav-id-fix I)) ens)
     (JS-p (+ -1 (uav-id-fix I)) ens)
     (JS-p I ens)
     )
    (JS-p I (update-location-all dt ens)))
   :hints (("Goal" :do-not-induct t
            :use JS-p-update-location-all-helper
            :in-theory (disable JS-P-definition have-met-Left-p)
            )))
 ))

;; ===================================================================
;;
;; Left Synchronized
;;
;; From the hand proof:
;;
;; ".. a drone is 'left synchronized' at time t if beyond that point
;;  it never goes to the left of its left endpoint"
;;
;; ===================================================================


(def::un LEFT-SYNCHRONIZED-p (j ens)
  (declare (xargs :fty ((uav-id uav-list) bool)))
  (implies
   ;;
   ;; For all UAV's greater than zero ..
   ;;
   (< 0 j)
   (and
    ;;
    ;; Their average loction with their left neighbor
    ;; is not less than their left boundary.
    ;;
    ;;              J
    ;; |--------|--------|
    ;;       x    ^    x
    (<= (UAV-left-boundary (ith-uav j ens))
        (average (UAV->location (ith-uav (+ -1 j) ens))
                 (UAV->location (ith-uav j ens))))
    (implies
     (and
      (< (UAV->direction (ith-uav j ens)) 0)
      (not (equal (UAV->location (ith-uav j ens))
                  (UAV->location (ith-uav (+ -1 j) ens)))))
     ;;
     ;; If they are moving left ..
     ;; and they are not co-incident with their left neighbor ..
     ;; .. then the left neighbor is moving right.
     ;;
     ;;              J
     ;; |--------|--------|
     ;;       >    ^    <
     (< 0 (UAV->direction (ith-uav (+ -1 j) ens)))))))

(def::un RIGHT-SYNCHRONIZED-p (j ens)
  (declare (xargs :fty ((uav-id uav-list) bool)))
  (implies
   ;;
   ;; For all UAV's less than N-1 ..
   ;;
   (< j (+ -1 (N)))
   (and
    ;;
    ;; Their average loction with their right neighbor
    ;; is not greater than their right boundary.
    ;;
    ;;       J
    ;;  |--------|--------|
    ;;    x    ^    x
    (<= (average (UAV->location (ith-uav (+ 1 j) ens))
                 (UAV->location (ith-uav j ens)))
        (UAV-right-boundary (ith-uav j ens)))
    (implies
     (and
      ;;
      ;; If they are moving right ..
      ;; and they are not co-incident with their right neighbor ..
      ;;
      (< 0 (UAV->direction (ith-uav j ens)))
      (not (equal (UAV->location (ith-uav j ens))
                  (UAV->location (ith-uav (+ 1 j) ens)))))
     ;;
     ;; .. then the right neighbor is moving left.
     ;;
     ;;     J
     ;; |--------|--------|
     ;;   >    ^    <
     (< (UAV->direction (ith-uav (+ 1 j) ens)) 0)))))

;; LS is stronger than JS
(defthmd LEFT-SYNCHRONIZED-implies-JS
  (implies
   (and
    (wf-ensemble ens)
    (escort-condition ens)
    (LEFT-SYNCHRONIZED-p j ens))
   (JS-p j ens))
  :hints ((average-hint)))


(with-average-theory
 (without-subsumption
  (defthm LEFT-SYNCHRONIZED-P-flip-on-events-invariant
    (implies
     (and
      (wf-ensemble ens)
      (escort-condition ens)
      (have-met-Left-p (+ -1 (uav-id-fix i)) ens)
      (LEFT-SYNCHRONIZED-p (+ -1 (uav-id-fix i)) ens)
      (LEFT-SYNCHRONIZED-P i ens))
     (LEFT-SYNCHRONIZED-P i (flip-on-events ens)))
    :hints (("Goal" :do-not-induct t
             :do-not '(fertilize)
             :cases ((< 0 (uav-id-fix i)))
             :in-theory (enable flip-uav
                                wf-ensemble))
            (pattern::hint*
             escort-condition-implies
             )
            ))))

(with-average-theory
 (without-subsumption
  (defthm RIGHT-SYNCHRONIZED-P-flip-on-events-invariant
    (implies
     (and
      (wf-ensemble ens)
      (escort-condition ens)
      (have-met-Right-p (+ 1 (uav-id-fix i)) ens)
      (RIGHT-SYNCHRONIZED-p (+ 1 (uav-id-fix i)) ens)
      (RIGHT-SYNCHRONIZED-P i ens))
     (RIGHT-SYNCHRONIZED-P i (flip-on-events ens)))
    :hints (("Goal" :do-not-induct t
             :cases ((< (uav-id-fix i) (+ -1 (N))))
             :do-not '(fertilize)
             :in-theory (enable flip-uav
                                wf-ensemble))
            (pattern::hint*
             escort-condition-implies
             )
            ))))


(local-preamble
 (with-average-theory
  (without-subsumption
   (defthm LEFT-SYNCHRONIZED-P-update-location-all-helper
     (implies
      (and
       (wf-ensemble ens)
       (escort-condition ens)
       (lte-min-time-to-impending-impact-event dt ens)
       (implies
        (not (chasing-neighbor (+ -1 (uav-id-fix I)) ens))
        (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV (+ -1 (uav-id-fix I)) ENS)))
       (implies
        (not (chasing-neighbor i ens))
        (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
       (have-met-Left-p (+ -1 (uav-id-fix I)) ens)
       (LEFT-SYNCHRONIZED-p (+ -1 (uav-id-fix I)) ens)
       (LEFT-SYNCHRONIZED-P I ens)
       )
      (LEFT-SYNCHRONIZED-P I (update-location-all dt ens)))
     :hints (("Goal" :do-not-induct t
              :cases ((< 0 (uav-id-fix I)))
              :in-theory (disable have-met-Left-p
                                  JS-p-definition
                                  CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV))
             (pattern::hint*
              expand-chasing-neighbor
              expand-min-time-to-impact-for-uav
              escort-condition-implies
              )
             (and stable-under-simplificationp
                  '(:in-theory (enable have-met-Left-p JS-p-definition)))
             ))
   ))

 (defthm LEFT-SYNCHRONIZED-P-update-location-all-invariant
   (implies
    (and
     (wf-ensemble ens)
     (escort-condition ens)
     (lte-min-time-to-impending-impact-event dt ens)
     (have-met-Left-p (+ -1 (uav-id-fix I)) ens)
     (LEFT-SYNCHRONIZED-p (+ -1 (uav-id-fix I)) ens)
     (LEFT-SYNCHRONIZED-P I ens)
     )
    (LEFT-SYNCHRONIZED-P I (update-location-all dt ens)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable LEFT-SYNCHRONIZED-P have-met-Left-p JS-p-definition)
            :use LEFT-SYNCHRONIZED-P-update-location-all-helper
            )))

 )

(local-preamble
 (with-average-theory
  (without-subsumption
   (defthm RIGHT-SYNCHRONIZED-P-update-location-all-helper
     (implies
      (and
       (wf-ensemble ens)
       (escort-condition ens)
       (lte-min-time-to-impending-impact-event dt ens)
       (implies
        (not (chasing-neighbor (+ 1 (uav-id-fix I)) ens))
        (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV (+ 1 (uav-id-fix I)) ENS)))
       (implies
        (not (chasing-neighbor i ens))
        (<= (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
       (have-met-Right-p (+ 1 (uav-id-fix I)) ens)
       (RIGHT-SYNCHRONIZED-p (+ 1 (uav-id-fix I)) ens)
       (RIGHT-SYNCHRONIZED-P I ens)
       )
      (RIGHT-SYNCHRONIZED-P I (update-location-all dt ens)))
     :hints (("Goal" :do-not-induct t
              :cases ((< (uav-id-fix I) (+ -1 (N))))
              :in-theory (disable have-met-Left-p
                                  JS-p-definition
                                  CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV))
             (pattern::hint*
              expand-chasing-neighbor
              expand-min-time-to-impact-for-uav
              escort-condition-implies
              )
             (and stable-under-simplificationp
                  '(:in-theory (enable have-met-Left-p JS-p-definition)))
             ))
   ))

 (defthm RIGHT-SYNCHRONIZED-P-update-location-all-invariant
   (implies
    (and
     (wf-ensemble ens)
     (escort-condition ens)
     (lte-min-time-to-impending-impact-event dt ens)
     (have-met-Right-p (+ 1 (uav-id-fix I)) ens)
     (RIGHT-SYNCHRONIZED-p (+ 1 (uav-id-fix I)) ens)
     (RIGHT-SYNCHRONIZED-P I ens)
     )
    (RIGHT-SYNCHRONIZED-P I (update-location-all dt ens)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable RIGHT-SYNCHRONIZED-P have-met-Right-p JS-p-definition)
            :use RIGHT-SYNCHRONIZED-P-update-location-all-helper
            )))

 )

(with-average-theory
 (defthm local-synchronized-double-containment
   (implies
    (and
     (wf-ensemble ens)
     (have-met-Left-p i ens)
     (have-met-Right-p i ens)
     (RIGHT-SYNCHRONIZED-P i ens)
     (LEFT-SYNCHRONIZED-P i ens))
    (and
     (<= (uav-left-boundary (ith-uav i ens))
         (uav->location (ith-uav i ens)))
     (<= (uav->location (ith-uav i ens))
         (uav-right-boundary (ith-uav i ens)))))
   ))

(with-average-theory
 (defthm local-synchronized-event
   (implies
    (and
     (wf-ensemble ens)
     (have-met-Left-p i ens)
     (have-met-Right-p i ens)
     (RIGHT-SYNCHRONIZED-P i ens)
     (LEFT-SYNCHRONIZED-P i ens))
    (and
     (implies
      (and
       (< 0 (uav->direction (ith-uav i ens)))
       (equal (uav->location (ith-uav i ens))
              (uav-right-boundary (ith-uav i ens))))
      (event-for-uav i ens))
     (implies
      (and
       (< (uav->direction (ith-uav i ens)) 0)
       (equal (uav->location (ith-uav i ens))
              (uav-left-boundary (ith-uav i ens))))
      (event-for-uav i ens))))
   :hints (("Goal" :in-theory (enable
                               have-met-Left-p
                               have-met-Right-p
                               RIGHT-SYNCHRONIZED-P
                               LEFT-SYNCHRONIZED-p)))))






