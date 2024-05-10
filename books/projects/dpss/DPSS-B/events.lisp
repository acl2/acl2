;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "dpss")

(defthm UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION-to-RIGHT-MOVING-UAV-SPLIT-LOCATION
  (equal (UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION (GET-UAV I ENS))
         (RIGHT-MOVING-UAV-SPLIT-LOCATION I ENS))
  :hints (("Goal" :in-theory (enable RIGHT-MOVING-UAV-SPLIT-LOCATION))))

(theory-invariant (incompatible (:rewrite UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION-to-RIGHT-MOVING-UAV-SPLIT-LOCATION)
                                (:definition RIGHT-MOVING-UAV-SPLIT-LOCATION)))

(defthm UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-to-LEFT-MOVING-UAV-SPLIT-LOCATION
  (equal (UAV->LEFT-MOVING-UAV-SPLIT-LOCATION (GET-UAV I ENS))
         (LEFT-MOVING-UAV-SPLIT-LOCATION I ENS))
  :hints (("Goal" :in-theory (enable LEFT-MOVING-UAV-SPLIT-LOCATION))))

(theory-invariant (incompatible (:rewrite UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-to-LEFT-MOVING-UAV-SPLIT-LOCATION)
                                (:definition LEFT-MOVING-UAV-SPLIT-LOCATION)))

(defthm UAV->xx-to-current-location
  (equal (UAV->xx (get-uav i ens))
         (current-location i ens))
  :hints (("Goal" :in-theory (enable current-location))))

(theory-invariant (incompatible (:rewrite UAV->xx-to-current-location)
                                (:definition current-location)))

(defthmd UAV->dx-to-left-moving-p
  (equal (< (UAV->DX (GET-UAV I ENS)) 0)
         (left-moving-p i ens))
  :hints (("Goal" :in-theory (enable left-moving-p))))

(defthmd UAV->dx-to-right-moving-p
  (equal (< 0 (UAV->DX (GET-UAV I ENS)))
         (right-moving-p i ens))
  :hints (("Goal" :in-theory (enable left-moving-p))))

(defthmd UAV->dx-to-not-left-moving-p
  (equal (EQUAL (UAV->DX (GET-UAV I ENS)) 1)
         (not (left-moving-p i ens)))
  :hints (("Goal" :in-theory (enable left-moving-p))))

(theory-invariant (incompatible (:rewrite UAV->dx-to-left-moving-p)
                                (:definition left-moving-p)))

(theory-invariant (incompatible (:rewrite UAV->dx-to-not-left-moving-p)
                                (:definition left-moving-p)))

(theory-invariant (incompatible (:rewrite UAV->dx-to-right-moving-p)
                                (:definition left-moving-p)))

(in-theory (enable UAV->dx-to-left-moving-p
                   UAV->dx-to-not-left-moving-p
                   UAV->dx-to-right-moving-p))

(defthm UAV->LC-to-LeftCountGuess
  (equal (UAV->LC (GET-UAV i ens))
         (LeftCountGuess i ens))
  :hints (("Goal" :in-theory (enable LeftCountGuess))))

(theory-invariant (incompatible (:rewrite UAV->LC-to-LeftCountGuess)
                                (:definition LeftCountGuess)))

(defthm UAV->RC-to-RightCountGuess
  (equal (UAV->RC (GET-UAV i ens))
         (RightCountGuess i ens))
  :hints (("Goal" :in-theory (enable RightCountGuess))))

(theory-invariant (incompatible (:rewrite UAV->RC-to-RightCountGuess)
                                (:definition RightCountGuess)))


(defthm UAV->LP-to-LeftPerimeterGuess
  (equal (UAV->LP (GET-UAV i ens))
         (LeftPerimeterGuess i ens))
  :hints (("Goal" :in-theory (enable LeftPerimeterGuess))))

(theory-invariant (incompatible (:rewrite UAV->LP-to-LeftPerimeterGuess)
                                (:definition LeftPerimeterGuess)))

(defthm UAV->RP-to-RightPerimeterGuess
  (equal (UAV->RP (GET-UAV i ens))
         (RightPerimeterGuess i ens))
  :hints (("Goal" :in-theory (enable RightPerimeterGuess))))

(theory-invariant (incompatible (:rewrite UAV->RP-to-RightPerimeterGuess)
                                (:definition RightPerimeterGuess)))

(def::un chasing-neighbor (i ens)
  (declare (xargs :fty ((nat ens) bool)))
  (let ((i (ensemble-index i ens)))
    (if (< (uav->dx (get-uav i ens)) 0)
        (and (not (equal i 0))
             (< (uav->dx (get-uav (+ -1 i) ens)) 0)
             (not
              (equal (UAV->xx (get-uav (+ -1 i) ens))
                     (UAV->xx (get-uav i ens)))))
      (and (not (equal i (max-ens-index ens)))
           (< 0 (uav->dx (get-uav (+ 1 i) ens)))
           (not
            (equal (UAV->xx (get-uav i ens))
                   (UAV->xx (get-uav (+ 1 i) ens))))))))
  
(def::un impending-impact-event-for-uav (i ens)
  (declare (xargs :fty ((nat ens) bool)))
  (let ((uav (get-uav i ens))
        (i   (ensemble-index i ens)))
    (if (< (uav->dx uav) 0)
        ;; Moving left
        (or (equal i 0)
            (let* ((left (get-uav (+ -1 i) ens)))
              (if (< 0 (uav->dx left))
                  ;; Moving right
                  t ;; (<= avg (UAV-left-boundary uav))
                ;; Moving left
                (and (equal (UAV->xx uav)
                            (UAV->xx left))
                     (<= (UAV->left-moving-uav-split-location uav) (UAV->xx uav))))))
      ;; Moving right
      (or (equal i (max-ens-index ens))
          (let* ((right (get-uav (+ 1 i) ens)))
            (if (< (uav->dx right) 0)
                ;; Moving left
                t ;; (<= (UAV-right-boundary uav) avg)
              ;; Moving right
              (and (equal (UAV->xx uav)
                          (UAV->xx right))
                   (<= (UAV->xx uav) (UAV->right-moving-uav-split-location uav)))))))))

(defthm impending-impact-event-for-uav-ensemble-index
  (equal (impending-impact-event-for-uav (ensemble-index i ens) ens)
         (impending-impact-event-for-uav i ens))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :corollary
                  (implies
                   (impending-impact-event-for-uav (ensemble-index i ens) ens)
                   (impending-impact-event-for-uav i ens)))))

(defthm IMPENDING-IMPACT-EVENT-FOR-UAV-ensemble-index-equiv-congruence
  (implies
   (and
    (IMPENDING-IMPACT-EVENT-FOR-UAV J ENS)
    (EQUAL (ENSEMBLE-INDEX J ENS) I))
   (IMPENDING-IMPACT-EVENT-FOR-UAV I ENS))
  :rule-classes (:forward-chaining))

(defthmd chasing-neighbor-is-not-impending-impact-event-for-uav
  (implies
   (and
    (uav-state-p ens)
    (pre-move-invariant ens))
   (iff (chasing-neighbor i ens)
        (not (impending-impact-event-for-uav i ens))))
  :hints ((pattern-hint
           (:and
            (pre-move-invariant ens)
            (equal (current-location i ens)
                   (current-location j ens)))
           :use ((:instance pre-move-invariant-implication
                            (ens ens)
                            (i i)
                            (j j))))))

(in-theory (disable chasing-neighbor))

(def::un min-time-to-impact-for-uav (i ens)
  (declare (xargs :fty ((nat ens) rational)))
  (let* ((uav  (get-uav i ens))
         (i    (ensemble-index i ens)))
    (cond
     ;; UAV is moving left ..
     ((< (UAV->dx uav) 0)
      (cond
       ;; Leftmost UAV heading towards left boundary
       ((equal i 0)
        (- (UAV->xx uav)
           (ActualLeftPerimeter)))
       (t
        (let ((left (get-uav (+ -1 i) ens)))
          ;; Abnormal condition
          (if (< (UAV->xx uav) (UAV->xx left)) 0
            (let ((avg (average (UAV->xx left) (UAV->xx uav) )))
              ;;
              ;; |--------|--------|--------|
              ;;       L  | x   <U
              ;;
              ;; This has to be conditional based on escort.
              ;;
              (cond
               ((and (equal (UAV->xx left)
                            (UAV->xx uav))
                     (< (UAV->dx left) 0))
                ;; escort condition ..
                (if (<= (UAV->left-moving-uav-split-location uav) (UAV->xx uav))
                    (- (UAV->xx uav) (UAV->left-moving-uav-split-location uav))
                  0))
               (t
                (- (UAV->xx uav) avg)))))))))
     ;; UAV is moving right ..
     (t
      (cond
       ((equal i (max-ens-index ens))
        (- (ActualRightPerimeter)
           (UAV->xx uav)))
       (t
        (let ((right (get-uav (+ 1 i) ens)))
          ;; Abnormal conditon
          (if (< (UAV->xx right) (UAV->xx uav)) 0
            (let ((avg (average (UAV->xx uav) (UAV->xx right))))
              ;;
              ;; |--------|--------|--------|
              ;;       U> | x    R
              ;;
              (cond
               ((and (equal (UAV->xx uav)
                            (UAV->xx right))
                     (< 0 (UAV->dx right)))
                ;; escort condition ..
                (if (<= (UAV->xx uav) (UAV->right-moving-uav-split-location uav))
                    (- (UAV->right-moving-uav-split-location uav) (UAV->xx uav))
                  0))
               (t
                (- avg (UAV->xx uav)))))))))))))

(defthm MIN-TIME-TO-IMPACT-FOR-UAV-ENSEMBLE-INDEX
  (equal (MIN-TIME-TO-IMPACT-FOR-UAV (ENSEMBLE-INDEX I ENS) ENS)
         (MIN-TIME-TO-IMPACT-FOR-UAV I ENS))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((MIN-TIME-TO-IMPACT-FOR-UAV (ENSEMBLE-INDEX I ENS) ENS)))))

(defthm MIN-TIME-TO-IMPACT-FOR-UAV-ENSEMBLE-INDEX-equiv-linear
  (implies
   (EQUAL (ENSEMBLE-INDEX J ENS) I)
   (equal (MIN-TIME-TO-IMPACT-FOR-UAV J ENS)
          (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
  :rule-classes ((:linear :trigger-terms ((MIN-TIME-TO-IMPACT-FOR-UAV J ENS)))))

(defthm rationalp-min-time-to-impact-for-uav
  (rationalp (min-time-to-impact-for-uav i ens))
  :rule-classes (:type-prescription))

(with-arithmetic
 (defthm nneg-min-time-to-impact-for-uav
   (implies
    (uav-state-p ens)
    (<= 0 (min-time-to-impact-for-uav i ens)))
   :rule-classes (:rewrite :linear))
 )

(def::un distance-to-perimeter (i ens)
  (declare (xargs :fty ((nat ens) rational)))
  (if (left-moving-p i ens)
      (- (current-location i ens) (ActualLeftPerimeter))
    (- (actualRightPerimeter) (current-location i ens))))

(defun-sk lte-min-time-to-impending-impact-event (dt ens)
  (declare (xargs :guard t))
  (forall (i)
    (and (<= (nnrat-fix dt) (distance-to-perimeter (nfix i) (ens-fix ens)))
         (implies (impending-impact-event-for-uav (nfix i) (ens-fix ens))
                  (<= (nnrat-fix dt) (min-time-to-impact-for-uav (nfix i) (ens-fix ens))))))
  :strengthen t)

(in-theory (disable impending-impact-event-for-uav min-time-to-impact-for-uav))

(encapsulate
    ()

  (local (in-theory (disable distance-to-perimeter)))
  
  (quant::congruence lte-min-time-to-impending-impact-event (dt ens)
    (forall (i)
      (and (<= (nnrat-fix dt) (distance-to-perimeter (nfix i) (ens-fix ens)))
           (implies (impending-impact-event-for-uav (nfix i) (ens-fix ens))
                    (<= (nnrat-fix dt) (min-time-to-impact-for-uav (nfix i) (ens-fix ens))))))
    :congruences ((dt nnrat-equiv)
                  (ens ens-equiv)))

  )
  
(in-theory (disable lte-min-time-to-impending-impact-event))

(defthm lte-min-time-to-impending-impact-event-implication-left-0
  (implies
   (and
    (lte-min-time-to-impending-impact-event dt ens)
    (left-moving-p i ens))
   (<= (nnrat-fix dt) (- (current-location i ens) (ActualLeftPerimeter))))
  :hints (("Goal" :use lte-min-time-to-impending-impact-event-necc))
  :rule-classes ((:linear :trigger-terms ((current-location i ens)))))

(defthm lte-min-time-to-impending-impact-event-implication-right-0
  (implies
   (and
    (lte-min-time-to-impending-impact-event dt ens)
    (not (left-moving-p i ens)))
   (<= (nnrat-fix dt) (- (ActualRightPerimeter) (current-location i ens))))
  :hints (("Goal" :use lte-min-time-to-impending-impact-event-necc))
  :rule-classes ((:linear :trigger-terms ((current-location i ens)))))

(defthm lte-min-time-to-impending-impact-event-implication-1
  (implies
   (and
    (impending-impact-event-for-uav i ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))
  :hints (("Goal" :use lte-min-time-to-impending-impact-event-necc))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthmd lte-min-time-to-impending-impact-event-implication-chasing-neighbor
  (implies
   (and
    (not (chasing-neighbor i ens))
    (uav-state-p ens)
    (pre-move-invariant ens)
    ;;(escort-condition ens)
    ;;(wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))
  :hints (("Goal" :in-theory (enable chasing-neighbor-is-not-impending-impact-event-for-uav)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm lte-min-time-to-impending-impact-event-implication-2
  (implies
   (and
    (impending-impact-event-for-uav i ens)
    (lte-min-time-to-impending-impact-event (double-rewrite dt) ens)
    (force
     (and
      (rationalp dt)
      (<= 0 dt))))
   (<= dt (min-time-to-impact-for-uav i ens)))
  :hints (("Goal" :use lte-min-time-to-impending-impact-event-necc))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm lte-min-time-to-impending-impact-event-lt-chaining
  (implies
   (and
    (impending-impact-event-for-uav dt ens)
    (< (nnrat-fix dt) z)
    (rationalp z)
    (lte-min-time-to-impending-impact-event z ens))
   (lte-min-time-to-impending-impact-event dt ens))
  :hints (("Goal" :expand ((lte-min-time-to-impending-impact-event dt ens)
                           (nnrat-fix z))
           :in-theory (disable  LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-IMPLICATION-1
                                LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-IMPLICATION-2)
           :use (:instance lte-min-time-to-impending-impact-event-implication-1
                           (dt z)
                           (i (LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-WITNESS DT ENS))))))

(defthm lte-min-time-to-impending-impact-event-chaining
  (implies
   (and
    (lte-min-time-to-impending-impact-event dt ens)
    (<= (nnrat-fix dx) (nnrat-fix dt)))
   (lte-min-time-to-impending-impact-event dx ens))
  :hints (("GOal"
           :expand (lte-min-time-to-impending-impact-event dx ens)
           :use (:instance lte-min-time-to-impending-impact-event-implication-1
                           (i (LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-WITNESS DX ENS)))
           :in-theory (disable lte-min-time-to-impending-impact-event-implication-1))))

;; (defthmd left-moving-p-ensemble-index-congruence
;;   (implies
;;    (and
;;     (equal (ENSEMBLE-INDEX I ENS) 0)
;;     (syntaxp (not (quotep i))))
;;    (iff (LEFT-MOVING-P I ENS)
;;         (LEFT-MOVING-P 0 ENS)))
;;   :hints (("Goal" :in-theory (disable left-moving-p-ensemble-index))
;;           (pattern-hint
;;            (:and
;;             (left-moving-p i ens)
;;             (not (left-moving-p j ens)))
;;            :use ((:instance LEFT-MOVING-P-ENSEMBLE-INDEX-forward
;;                             (i i)
;;                             (j j))))))

(defthm converging-uav-separation
  (implies
   (and (lte-min-time-to-impending-impact-event dt ens)
        (left-moving-p i ens)
        (not (left-moving-p (+ -1 (ensemble-index i ens)) ens))
        (uav-state-p ens))
   (<= (+ (* 2 (nnrat-fix dt)) (current-location (+ -1 (ensemble-index i ens)) ens))
       (current-location i ens)))
  :rule-classes ((:linear :trigger-terms ((current-location i ens))))
  :hints (("goal" ;; :cases ((equal (ensemble-index i ens) 0))
           :in-theory (e/d (impending-impact-event-for-uav
                            min-time-to-impact-for-uav)
                           (lte-min-time-to-impending-impact-event-implication-1
                            lte-min-time-to-impending-impact-event-implication-2
                            ))
           :use (:instance lte-min-time-to-impending-impact-event-implication-1))))
;;
;;
;;
;;

#+joe
(encapsulate
    ()

  (local
   (encapsulate
       ()
     
     (encapsulate
         ()
       
       (defun next-right-moving-left (i ens)
         (declare (xargs :measure (nfix i)))
         (let* ((i (ensemble-index i ens))
                (j (+ -1 i)))
           (if (< j 0) i
             (if (< 0 (uav->dx  (get-uav j ens))) j
               (next-right-moving-left j ens)))))
       
       (defthm next-right-moving-left-upper-bound
         (<= (next-right-moving-left i ens)
             (ensemble-index i ens))
         :hints (("Goal" :induct (next-right-moving-left i ens)
                  ;;:expand (ensemble-index i ens)))
                  ))
         :rule-classes :linear)
       
       ;;(local (in-theory (disable  LESS-THAN-ZERO-TO-UAV-ID-EQUIV)))
       
       (defthmd next-right-moving-left-is-usually-bigger
         (iff (< (next-right-moving-left i ens) (ensemble-index i ens))
              (not (equal (ensemble-index i ens) 0))))
       
       (def::signature next-right-moving-left (t t) natp)
       
       (defthmd next-right-moving-left-direction-raw
         (implies
          (< (uav->dx (get-uav i ens)) 0)
          (if (< (uav->dx (get-uav (next-right-moving-left i ens) ens)) 0)
              (equal (next-right-moving-left i ens) 0)
            (and (< 0 (uav->dx (get-uav (next-right-moving-left i ens) ens)))
                 (< (uav->dx (get-uav (+ 1 (next-right-moving-left i ens)) ens)) 0))))
         :hints (("Goal" :induct (next-right-moving-left i ens)
                  :expand (next-right-moving-left i ens))
                 (and stable-under-simplificationp
                      '(:in-theory nil))
                 (and stable-under-simplificationp
                      '(:in-theory (e/d (left-moving-ensemble-index!)
                                        (;IFIX-NFIX-LINEAR-RELATION
                                         ;NFIX-ENSEMBLE-INDEX
                                         ))))))
       
       )
     
     (defthmd next-right-moving-left-direction
       (implies
        (left-moving-p i ens)
        (if (left-moving-p (next-right-moving-left i ens) ens)
            (equal (next-right-moving-left i ens) 0)
          (and (not (left-moving-p (next-right-moving-left i ens) ens))
               (left-moving-p (+ 1 (next-right-moving-left i ens)) ens))))
       :hints (("Goal" :use next-right-moving-left-direction-raw
                :in-theory (e/d (left-moving-p)
                                (UAV->DX-TO-LEFT-MOVING-P
                                 UAV->DX-TO-NOT-LEFT-MOVING-P
                                 UAV->DX-TO-RIGHT-MOVING-P
                                 )))))
     
     (defthm impending-impact-event-next-right-moving-left
       (implies
        (and
         (uav-state-p ens)
         (left-moving-p i ens))
        (and (<= (next-right-moving-left i ens) (nfix i))
             (impending-impact-event-for-uav (next-right-moving-left i ens) ens)))
       :hints (("Goal" :do-not-induct t
                :use next-right-moving-left-direction
                :in-theory (enable impending-impact-event-for-uav))))
     
     (defthm left-moving-next-right-moving-left
       (implies
        (and
         (left-moving-p i ens)
         (left-moving-p (next-right-moving-left i ens) ens))
        (equal (next-right-moving-left i ens) 0))
       :hints (("Goal" :use next-right-moving-left-direction)))
     
     (defthm next-right-moving-left-directions
       (implies
        (and
         (left-moving-p i ens)
         (not (left-moving-p (next-right-moving-left i ens) ens)))
        (and (not (left-moving-p (next-right-moving-left i ens) ens))
             (left-moving-p (+ 1 (next-right-moving-left i ens)) ens)))
       :hints (("Goal" :use next-right-moving-left-direction)))
     
     (defthm next-right-moving-left-is-max-scenario
       (iff (equal (next-right-moving-left i ens) (max-ens-index ens))
            (equal (len ens) 1))
       :hints (("Goal" :do-not-induct t
                :expand (next-right-moving-left i ens)
                :in-theory (enable ensemble-index))))
     
     (defthm equal-next-right-moving-ensemble-index
       (iff (EQUAL (NEXT-RIGHT-MOVING-LEFT I ENS) (ENSEMBLE-INDEX I ENS))
            (equal (ENSEMBLE-INDEX I ENS) 0)))
     
     (defthmd next-right-moving-left-ensemble-index!
       (implies
        (syntaxp (symbolp i))
        (equal (next-right-moving-left i ens)
               (next-right-moving-left (ensemble-index i ens) ens)))
       :hints (("Goal" :in-theory (enable ensemble-index nfix)
                :expand ((next-right-moving-left i ens)
                         (next-right-moving-left (ensemble-index i ens) ens)))))
     
     (defthm next-next-right-moving-left-<=-current-index
       (implies
        (and
         (uav-state-p ens)
         (left-moving-p i ens)
         (not (left-moving-p (next-right-moving-left i ens) ens)))
        (<= (+ 1 (next-right-moving-left i ens))
            (ensemble-index i ens)))
       :rule-classes ((:linear :trigger-terms ((next-right-moving-left i ens))))
       :hints (("Goal" :do-not-induct t
                :in-theory (enable left-moving-ensemble-index!
                                   next-right-moving-left-ensemble-index!))))

     ))
     
  (defthm lte-min-time-to-impending-impact-event-bounded-by-location-left
    (implies
     (and
      (left-moving-p i ens)
      (lte-min-time-to-impending-impact-event dt ens)
      (uav-state-p ens))
     (<= (ActualLeftPerimeter)
         (+ (current-location i ens) (- (nnrat-fix dt)))))
    :rule-classes ((:linear :trigger-terms ((current-location i ens)))
                   :rewrite)
    :hints (("Goal" :in-theory (e/d (MIN-TIME-TO-IMPACT-FOR-UAV)
                                    (max-ens-index
                                     lte-min-time-to-impending-impact-event-implication-1
                                     lte-min-time-to-impending-impact-event-implication-2))
             :use ((:instance lte-min-time-to-impending-impact-event-implication-1
                              (i (next-right-moving-left i ens)))))
            (pattern-hint
             (equal (len ens) 1)
             :in-theory (enable LEFT-MOVING-ENSEMBLE-INDEX!))))

  )
        
(defthm distance-to-perimeter-ensemble-index
  (equal (distance-to-perimeter (ensemble-index i ens) ens)
         (distance-to-perimeter i ens))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((distance-to-perimeter (ensemble-index i ens) ens)))))

(defthm min-time-to-impact-for-uav-ensemble-index
  (equal (min-time-to-impact-for-uav (ensemble-index i ens) ens)
         (min-time-to-impact-for-uav i ens))
  :hints (("Goal" :in-theory (enable min-time-to-impact-for-uav)))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((min-time-to-impact-for-uav (ensemble-index i ens) ens)))))

(def::un min-time-to-impending-impact-event-rec (i ens)
  (declare (xargs :fty ((nat ens) rational)))
  (let ((i (ensemble-index i ens)))
    (if (zp i) (min (min-time-to-impact-for-uav i ens) (distance-to-perimeter i ens))
      (min (min (min-time-to-impact-for-uav i ens) (distance-to-perimeter i ens))
           (min-time-to-impending-impact-event-rec (1- i) ens)))))

(defthm distance-to-perimeter-ensemble-index-linear
  (implies
   (equal (ENSEMBLE-INDEX J ENS) I)
   (equal (DISTANCE-TO-PERIMETER J ENS)
          (DISTANCE-TO-PERIMETER I ENS)))
  :rule-classes ((:linear :trigger-terms ((DISTANCE-TO-PERIMETER J ENS)))))

(defthmd LEFT-MOVING-UAV-SPLIT-LOCATION-ensemble-index-linear
  (implies
   (equal (ENSEMBLE-INDEX J ENS) I)
   (equal (LEFT-MOVING-UAV-SPLIT-LOCATION J ENS)
          (LEFT-MOVING-UAV-SPLIT-LOCATION I ENS)))
  :rule-classes ((:linear :trigger-terms ((LEFT-MOVING-UAV-SPLIT-LOCATION J ENS)))
                 (:forward-chaining :trigger-terms ((LEFT-MOVING-UAV-SPLIT-LOCATION J ENS)))))

(defthmd RIGHT-MOVING-UAV-SPLIT-LOCATION-ensemble-index-linear
  (implies
   (equal (ENSEMBLE-INDEX J ENS) I)
   (equal (RIGHT-MOVING-UAV-SPLIT-LOCATION J ENS)
          (RIGHT-MOVING-UAV-SPLIT-LOCATION I ENS)))
  :rule-classes ((:linear :trigger-terms ((right-MOVING-UAV-SPLIT-LOCATION J ENS)))
                 (:forward-chaining :trigger-terms ((right-MOVING-UAV-SPLIT-LOCATION J ENS)))))
  
;; (defthmd equal-zero-to-equal-ensemble-index-1
;;   (implies
;;    (EQUAL (ENSEMBLE-INDEX J ENS) 0)
;;    (EQUAL (ENSEMBLE-INDEX J ENS) (ENSEMBLE-INDEX 0 ENS)))
;;   :rule-classes (:forward-chaining))


;; (defthmd equal-zero-to-equal-ensemble-index-2
;;   (implies
;;    (EQUAL 0 (ENSEMBLE-INDEX J ENS))
;;    (EQUAL (ENSEMBLE-INDEX J ENS) (ENSEMBLE-INDEX 0 ENS)))
;;   :rule-classes (:forward-chaining))

;; (defthmd heavy-sigh
;;   (implies
;;    (and
;;     (EQUAL 0 (ENSEMBLE-INDEX I ENS))
;;     (EQUAL (ENSEMBLE-INDEX J ENS) 0))
;;    (equal (ENSEMBLE-INDEX I ENS) (ENSEMBLE-INDEX J ENS)))
;;   :rule-classes (:forward-chaining))

;; (defthmd double-sigh
;;   (implies
;;    (equal (ENSEMBLE-INDEX I ENS) (ENSEMBLE-INDEX J ENS))
;;    (equal (ENSEMBLE-INDEX J ENS) (ENSEMBLE-INDEX I ENS)))
;;   :rule-classes (:forward-chaining))
   
(defthm MIN-TIME-TO-IMPACT-FOR-UAV-ensemble-index-linear
  (implies
   (equal (ENSEMBLE-INDEX J ENS) I)
   (equal (MIN-TIME-TO-IMPACT-FOR-UAV J ENS)
          (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)))
  :rule-classes ((:linear :trigger-terms ((MIN-TIME-TO-IMPACT-FOR-UAV J ENS)))))

(in-theory (disable distance-to-perimeter))

(defthm p1
  (implies
   (<= (ensemble-index i ens) (ensemble-index j ens))
   (<= (min-time-to-impending-impact-event-rec j ens) (DISTANCE-TO-PERIMETER I ENS))))


(defthm p2
  (IMPLIES
   (and
    (<= (ensemble-index i ens) (ensemble-index j ens))
    (IMPENDING-IMPACT-EVENT-FOR-UAV i ens))
   (<= (min-time-to-impending-impact-event-rec j ens)
       (MIN-TIME-TO-IMPACT-FOR-UAV i ens))))

(defthm positive-distance-to-perimeter
  (implies
   (uav-state-p ens)
   (<= 0 (distance-to-perimeter i ens)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable distance-to-perimeter))))

(defthm nnrat-p-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-REC
  (implies
   (uav-state-p ens)
   (nnrat-p (MIN-TIME-TO-IMPENDING-IMPACT-EVENT-REC I ENS)))
  :hints (("Goal" :in-theory (enable nnrat-p)
           :induct (MIN-TIME-TO-IMPENDING-IMPACT-EVENT-REC I ENS)
           :expand (MIN-TIME-TO-IMPACT-FOR-UAV 0 ENS))))

(def::un min-time-to-impending-impact-event (ens)
  (declare (xargs :fty ((ens) rational)))
  (min-time-to-impending-impact-event-rec (max-ens-index ens) ens))

(defthm lte-min-time-to-impending-impact-event-min-time-to-impending-impact-event
  (implies
   (uav-state-p ens)
   (lte-min-time-to-impending-impact-event (min-time-to-impending-impact-event ens) ens))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable lte-min-time-to-impending-impact-event))))

(in-theory (disable min-time-to-impending-impact-event))


(defun any-impending-events (i ens)
  (let ((i (ensemble-index i ens)))
    (if (zp i) (impending-impact-event-for-uav i ens)
      (or (impending-impact-event-for-uav i ens)
          (any-impending-events (1- i) ens)))))

(defun all-right-moving (i ens)
  (let ((i (ensemble-index i ens)))
    (if (zp i) (right-moving-p i ens)
      (and (right-moving-p i ens)
           (all-right-moving (1- i) ens)))))

(defthm all-right-moving-implication
  (implies
   (all-right-moving i ens)
   (not (left-moving-p i ens)))
  :rule-classes (:rewrite :forward-chaining))

(defthm no-impending-events-implies-all-right-moving
  (implies
   (not (any-impending-events i ens))
   (all-right-moving i ens))
  :hints (("Goal" :induct (any-impending-events i ens)
           :expand ((IMPENDING-IMPACT-EVENT-FOR-UAV 0 ENS)
                    (IMPENDING-IMPACT-EVENT-FOR-UAV I ens)))))

(defthm no-impending-events-implies-right-moving-index
  (implies
   (not (any-impending-events i ens))
   (not (left-moving-p i ens))))
  
(def::un min-time-to-impending-impact-event-rec-index (i ens)
  (declare (xargs :fty ((nat ens) nat)))
  (let ((i (ensemble-index i ens)))
    (if (zp i) 0
      (let ((j (min-time-to-impending-impact-event-rec-index (1- i) ens)))
        (if (not (impending-impact-event-for-uav j ens)) i
          (if (not (impending-impact-event-for-uav i ens)) j
            (if (< (min-time-to-impact-for-uav j ens) (min-time-to-impact-for-uav i ens)) j i)))))))

(defthm min-time-to-impending-impact-event-rec-index-lower-bound
  (<= 0 (min-time-to-impending-impact-event-rec-index i ens))
  :rule-classes (:linear))

(defthm min-time-to-impending-impact-event-rec-index-upper-bound
  (<= (min-time-to-impending-impact-event-rec-index i ens) (ensemble-index i ens))
  :rule-classes ((:linear :trigger-terms ((min-time-to-impending-impact-event-rec-index i ens)))))

(defthm no-impending-events-consequence
  (implies
   (not (any-impending-events i ens))
   (equal (min-time-to-impending-impact-event-rec-index i ens)
          (ensemble-index i ens)))
  :hints (("Goal" :induct (any-impending-events i ens)
           :expand (min-time-to-impending-impact-event-rec-index i ens))))

(defthm right-moving-min-time-to-impending-impact-event-rec-index
  (implies
   (not (any-impending-events i ens))
   (not (left-moving-p (min-time-to-impending-impact-event-rec-index i ens) ens))))

(defthm impending-events-implies-impending-impact-event
  (implies
   (and
    (IMPENDING-IMPACT-EVENT-FOR-UAV J ENS)
    (<= (ensemble-index j ens) (ensemble-index i ens)))
   (impending-impact-event-for-uav (min-time-to-impending-impact-event-rec-index i ens) ens))
  :hints (("Goal" :induct (min-time-to-impending-impact-event-rec-index i ens))))

;; (defthm ensemble-index-pinching-lemma
;;   (implies
;;    (and
;;     (< (ENSEMBLE-INDEX (+ -1 (ENSEMBLE-INDEX I ENS)) ENS)
;;        (ENSEMBLE-INDEX J ENS))
;;     (<= (ENSEMBLE-INDEX J ENS)
;;         (ENSEMBLE-INDEX I ENS)))
;;    (equal (ENSEMBLE-INDEX J ENS)
;;           (ENSEMBLE-INDEX I ENS)))
;;   :hints (("Goal" :in-theory (enable ENSEMBLE-INDEX)))
;;   :rule-classes nil)

;; (defthm impending-impact-event-implies-any-impending-events
;;   (implies
;;    (and
;;     (IMPENDING-IMPACT-EVENT-FOR-UAV J ENS)
;;     (<= (ENSEMBLE-INDEX J ENS)
;;         (ENSEMBLE-INDEX I ENS)))
;;    (any-impending-events i ens))
;;   :hints ((stable-p :use ensemble-index-pinching-lemma))
;;   :rule-classes (:forward-chaining
;;                  (:rewrite
;;                   :corollary
;;                   (implies
;;                    (and
;;                     (IMPENDING-IMPACT-EVENT-FOR-UAV J ENS)
;;                     (<= (ENSEMBLE-INDEX J ENS)
;;                         (ENSEMBLE-INDEX I ENS)))
;;                    (any-impending-events i ens)))))
                   

(defthm min-min-time-to-impact
  (implies
   (and
    (IMPENDING-IMPACT-EVENT-FOR-UAV j ENS)
    (<= (ensemble-index j ens) (ensemble-index i ens)))
   (<= (min-time-to-impact-for-uav (min-time-to-impending-impact-event-rec-index i ens) ens)
       (min-time-to-impact-for-uav j ens)))
  :hints (("Goal" :induct (min-time-to-impending-impact-event-rec-index i ens))
          (stable-p :cases ((equal (ENSEMBLE-INDEX J ENS) (ENSEMBLE-INDEX I ENS))))
          ))
  
(defthm any-impending-events-implies-impending-impact-event
  (implies
   (and
    (any-impending-events j ens)
    (<= (ensemble-index j ens) (ensemble-index i ens)))
   (impending-impact-event-for-uav (min-time-to-impending-impact-event-rec-index i ens) ens)))

(def::und min-time-to-impending-impact-event-index (ens)
  (declare (xargs :fty ((ens) nat)))
  (min-time-to-impending-impact-event-rec-index (max-ens-index ens) ens))

(defthm right-moving-max-index-has-an-impending-event
  (implies
   (not (left-moving-p (max-ens-index ens) ens))
   (IMPENDING-IMPACT-EVENT-FOR-UAV (MAX-ENS-INDEX ENS) ens))
  :hints (("Goal" :in-theory (enable IMPENDING-IMPACT-EVENT-FOR-UAV))))

(defthm impending-impact-event-for-uav-min-time-to-impending-impact-event-index
  (impending-impact-event-for-uav (min-time-to-impending-impact-event-index ens) ens)
  :hints (("Goal" :expand (min-time-to-impending-impact-event-index ens)
           :cases ((any-impending-events (MAX-ENS-INDEX ENS) ens)))))

(def::linear least-min-time-to-impact-for-uav
  (implies
   (and
    (syntaxp (symbolp j))
    (IMPENDING-IMPACT-EVENT-FOR-UAV j ENS))
   (<= (min-time-to-impact-for-uav (min-time-to-impending-impact-event-index ens) ens)
       (min-time-to-impact-for-uav j ens)))
  :hints (("Goal" :in-theory (enable min-time-to-impending-impact-event-index))))

(def::un min-distance-to-perimeter-rec-index (i ens)
  (declare (xargs :fty ((nat ens) nat)))
  (let ((i (ensemble-index i ens)))
    (if (zp i) i
      (let ((k (min-distance-to-perimeter-rec-index (1- i) ens)))
        (if (< (distance-to-perimeter k ens) (distance-to-perimeter i ens)) k
          i)))))

(defthm min-distance-to-perimeter-rec-index-lower-bound
  (<= 0 (min-distance-to-perimeter-rec-index i ens))
  :rule-classes :linear)

(defthm min-distance-to-perimeter-rec-index-upper-bound
  (<= (min-distance-to-perimeter-rec-index i ens) (max-ens-index ens))
  :rule-classes ((:linear :trigger-terms ((min-distance-to-perimeter-rec-index i ens)))))

(defthm min-distance-to-perimeter-rec-index-fundamental-property
  (implies
   (<= (ensemble-index j ens) (ensemble-index i ens))
   (<= (distance-to-perimeter (min-distance-to-perimeter-rec-index i ens) ens)
       (distance-to-perimeter j ens))))

(def::un min-distance-to-perimeter-index (ens)
  (declare (xargs :fty ((ens) nat)))
  (min-distance-to-perimeter-rec-index (max-ens-index ens) ens))

(def::linear min-distance-to-perimeter-index-fundamental-property
  (implies
   (syntaxp (symbolp j))
   (<= (distance-to-perimeter (min-distance-to-perimeter-index ens) ens)
       (distance-to-perimeter j ens))))
;; :rule-classes ((:linear :trigger-terms ((distance-to-perimeter j ens)))))

(in-theory (disable min-distance-to-perimeter-index))

(def::und min-min-time-to-impact-for-uav (ens)
  (declare (xargs :fty ((uav-state) nnrat)))
  (min (min-time-to-impact-for-uav (min-time-to-impending-impact-event-index ens) ens)
       (distance-to-perimeter (min-distance-to-perimeter-index ens) ens)))

(in-theory (disable (min-min-time-to-impact-for-uav)))

(defthm uav-state-fix-uav-state-p
  (implies
   (uav-state-p x)
   (equal (uav-state-fix x) (ens-fix x)))
  :hints (("Goal" :in-theory (enable uav-state-fix))))

(defthm min-min-time-to-impact-for-uav-property
  (implies
   (and
    (uav-state-p ens)
    (IMPENDING-IMPACT-EVENT-FOR-UAV j ENS))
   (<= (min-min-time-to-impact-for-uav ens)
       (min-time-to-impact-for-uav j ens)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable min-min-time-to-impact-for-uav))))

(def::linear min-distance-to-perimeter-property
  (implies
   (uav-state-p ens)
   (<= (min-min-time-to-impact-for-uav ens)
       (distance-to-perimeter j ens)))
  :hints (("Goal" :in-theory (enable min-min-time-to-impact-for-uav))))

(defthm lte-min-time-to-impending-impact-event-min-min-time-to-impact-for-uav
  (implies
   (uav-state-p ens)
   (lte-min-time-to-impending-impact-event
    (min-min-time-to-impact-for-uav ens)
    ens))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((min-min-time-to-impact-for-uav ens))))
  :hints (("goal" :in-theory (enable lte-min-time-to-impending-impact-event))))

(in-theory (disable all-right-moving all-right-moving-implication))
(in-theory (disable any-impending-events no-impending-events-implies-right-moving-index))


