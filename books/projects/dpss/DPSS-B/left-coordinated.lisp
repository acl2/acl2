;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "run")

(def::un UAV->left-coordinated-p (i ens)
  (declare (xargs :fty ((nat ens) bool)))
  (and
   (equal (leftperimeterguess i ens) (ActualLeftPerimeter))
   (equal (leftcountguess i ens) (ensemble-index i ens))))

(def::un UAV->right-coordinated-p (i ens)
  (declare (xargs :fty ((nat ens) bool)))
  (and
   (equal (rightperimeterguess i ens) (ActualRightPerimeter))
   (equal (rightcountguess i ens) (- (max-ens-index ens) (ensemble-index i ens)))))

(def::un UAV->locally-left-coordinated-p (i ens)
  (declare (xargs :fty ((nat ens) bool)))
  (let ((i (ensemble-index i ens)))
    (and
     (implies*
      (equal i 0)
      (and
       (equal (leftperimeterguess i ens) (ActualLeftPerimeter))
       (equal (leftcountguess i ens) 0)))
     (implies*
      (< 0 i)
      (and
       (equal (leftperimeterguess i ens) (leftperimeterguess (+ -1 i) ens))
       (equal (leftcountguess i ens) (+ 1 (leftcountguess (+ -1 i) ens))))))))

(def::un UAV->locally-right-coordinated-p (i ens)
  (declare (xargs :fty ((nat ens) bool)))
  (let ((i (ensemble-index i ens)))
    (and
     (implies*
      (equal i (max-ens-index ens))
      (and
       (equal (rightperimeterguess i ens) (ActualRightPerimeter))
       (equal (rightcountguess i ens) 0)))
     (implies*
      (< i (max-ens-index ens))
      (and
       (equal (rightperimeterguess i ens) (rightperimeterguess (+ 1 i) ens))
       (equal (rightcountguess i ens) (+ 1 (rightcountguess (+ 1 i) ens))))))))

(defthm LEFTPERIMETERGUESS-ENSEMBLE-INDEX-congruence
  (implies
   (and
    (EQUAL (ENSEMBLE-INDEX I ENS) X)
    (syntaxp (good-index-rewrite-order i x)))
   (equal (LEFTPERIMETERGUESS I ENS)
          (LEFTPERIMETERGUESS X ENS))))

(defthm LEFTcountGUESS-ENSEMBLE-INDEX-congruence
  (implies
   (and
    (EQUAL (ENSEMBLE-INDEX I ENS) X)
    (syntaxp (good-index-rewrite-order i x)))
   (equal (LEFTcountGUESS I ENS)
          (LEFTcountGUESS X ENS))))

(defthm RIGHTPERIMETERGUESS-ENSEMBLE-INDEX-congruence
  (implies
   (and
    (EQUAL (ENSEMBLE-INDEX I ENS) X)
    (syntaxp (good-index-rewrite-order i x)))
   (equal (RIGHTPERIMETERGUESS I ENS)
          (RIGHTPERIMETERGUESS X ENS))))

(defthm RIGHTcountGUESS-ENSEMBLE-INDEX-congruence
  (implies
   (and
    (EQUAL (ENSEMBLE-INDEX I ENS) X)
    (syntaxp (good-index-rewrite-order i x)))
   (equal (RIGHTcountGUESS I ENS)
          (RIGHTcountGUESS X ENS))))

(defthm not-zero-is-positive
  (implies
   (NOT (EQUAL (ENSEMBLE-INDEX I ENS) 0))
   (< 0 (ENSEMBLE-INDEX I ENS)))
  :rule-classes (:forward-chaining))

(defthm left-coordinated-implies-UAV->locally-left-coordinated-p
  (implies
   (and
    (UAV->left-coordinated-p i ens)
    (implies
     (< 0 (ensemble-index i ens))
     (UAV->left-coordinated-p (+ -1 (ensemble-index i ens)) ens)))
   (UAV->locally-left-coordinated-p i ens)))

(defthm right-coordinated-implies-UAV->locally-right-coordinated-p
  (implies
   (and
    (UAV->right-coordinated-p i ens)
    (implies
     (< (ensemble-index i ens) (max-ens-index ens))
     (UAV->right-coordinated-p (+ 1 (ensemble-index i ens)) ens)))
   (UAV->locally-right-coordinated-p i ens)))

(defthm UAV->left-coordinated-p-implies
  (implies
   (UAV->left-coordinated-p j ens)
   (and
    (equal (leftperimeterguess j ens) (ActualLeftPerimeter))
    (equal (leftcountguess j ens) (ensemble-index j ens)))))

(in-theory (disable UAV->left-coordinated-p))

(defun-sk left-coordinated-p (i ens)
  (declare (xargs :guard t))
  (forall (j) (implies (<= (ensemble-index j ens) (ensemble-index i ens)) (UAV->left-coordinated-p (nfix j) (ens-fix ens))))
  :strengthen t)

(in-theory (disable UAV->left-coordinated-p))

(quant::congruence left-coordinated-p (i ens)
  (forall (j) (implies (<= (ensemble-index j ens) (ensemble-index i ens)) (UAV->left-coordinated-p j ens)))
  :congruences ((i   nat-equiv)
                (ens ens-equiv)))


(in-theory (disable  left-coordinated-p))
           
(defthm left-coordinated-p-implies
  (implies
   (and
    (left-coordinated-p i ens)
    (<= (ensemble-index j ens) (ensemble-index i ens)))
   (UAV->left-coordinated-p j ens))
  :hints (("Goal" :use left-coordinated-p-necc)))

(defthm left-coordinated-p-move
  (implies
   (left-coordinated-p i ens)
   (left-coordinated-p i (move dt ens)))
  :hints (("Goal" :in-theory (enable UAV->LEFT-COORDINATED-P)
           :expand (left-coordinated-p i (move dt ens)))))

(defthm left-coordinated-p-share
  (implies
   (and
    (all-current-locations-bounded-p ens)
    (ALL-ORDERED-LOCATIONS ENS)
    (left-coordinated-p i ens))
   (left-coordinated-p i (share ens)))
  :hints (("Goal" :in-theory (enable UAV->LEFT-COORDINATED-P)
           :expand (left-coordinated-p i (share ens)))
          ))

(defthm left-coordinated-p-flip
  (implies
   (left-coordinated-p i ens)
   (left-coordinated-p i (flip ens)))
  :hints (("Goal" :in-theory (enable UAV->LEFT-COORDINATED-P)
           :expand (left-coordinated-p i (flip ens)))))

(defthm left-coordinated-p-next-step
  (implies
   (and
    (uav-state-p ens)
    (left-coordinated-p i ens))
   (left-coordinated-p i (val 1 (next-step dt ens))))
  :hints (("Goal" :in-theory (enable next-step))))
                  
(defthm left-coordinated-p-step-time
  (implies
   (and
    (uav-state-p ens)
    (left-coordinated-p i ens))
   (left-coordinated-p i (step-time dt ens))))
    
