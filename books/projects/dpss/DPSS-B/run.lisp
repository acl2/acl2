;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "step")
(include-book "coi/defung/defung" :dir :system)

(def::ung step-time (dt ens)
  (declare (xargs :signature ((t t) uav-state-p)
                  :verify-guards nil
                  ))
  (let ((dt  (nnrat-fix dt))
        (ens (uav-state-fix ens)))
    (if (<= dt 0) ens
      (metlist ((dt ens) (next-step dt ens))
        (step-time dt ens)))))

(encapsulate
    ()
  
  (local
   (defthmd step-time-definition-alt
     (equal (step-time dt ens)
            (if (not (step-time-domain dt ens)) (uav-state-fix ens)
              (let ((dt (nnrat-fix dt))
                    (ens (uav-state-fix ens)))
                (if (<= dt 0) ens
                  (metlist ((dt ens) (next-step dt ens))
                    (step-time dt ens))))))))
  
  (local
   (defthmd step-time-measure-alt
     (equal (step-time-measure dt ens)
            (if (not (step-time-domain dt ens)) 0
              (let ((dt (nnrat-fix dt))
                    (ens (uav-state-fix ens)))
                (if (<= dt 0) 0
                  (metlist ((dt ens) (next-step dt ens))
                    (+ 1 (step-time-measure dt ens)))))))))

  )

(defthm step-time-zero
  (equal (step-time 0 ens) (uav-state-fix ens))
  :hints (("Goal" :expand (step-time 0 ens))))

(verify-guards
 step-time-monadic
 :hints (("goal" :expand (step-time-0-domain dt ens))))

(verify-guards step-time)

(verify-guards step-time-domain)

(defthmd step-time-domain-uav-state-fix
  (implies
   (syntaxp (symbolp ens))
   (equal (step-time-domain dt ens)
          (step-time-domain dt (uav-state-fix ens))))
  :hints (("Goal" :expand (step-time-domain dt (uav-state-fix ens)))))

(defcong uav-state-equiv equal (step-time-domain dt ens) 2
  :hints (("Goal" :in-theory (enable step-time-domain-uav-state-fix))))

(defthmd step-time-domain-nnrat-fix
  (implies
   (syntaxp (symbolp dt))
   (equal (step-time-domain dt ens)
          (step-time-domain (nnrat-fix dt) ens)))
  :hints (("Goal" :expand (step-time-domain (nnrat-fix dt) ens))))

(defcong nnrat-equiv equal (step-time-domain dt ens) 1
  :hints (("Goal" :in-theory (enable step-time-domain-nnrat-fix))))

(defthmd step-time-measure-uav-state-fix
  (implies
   (syntaxp (symbolp ens))
   (equal (step-time-measure dt ens)
          (step-time-measure dt (uav-state-fix ens))))
  :hints (("Goal" :expand (step-time-measure dt (uav-state-fix ens)))))

(defcong uav-state-equiv equal (step-time-measure dt ens) 2
  :hints (("Goal" :in-theory (enable step-time-measure-uav-state-fix))))

(defthmd step-time-measure-nnrat-fix
  (implies
   (syntaxp (symbolp dt))
   (equal (step-time-measure dt ens)
          (step-time-measure (nnrat-fix dt) ens)))
  :hints (("Goal" :expand (step-time-measure (nnrat-fix dt) ens))))

(defcong nnrat-equiv equal (step-time-measure dt ens) 1
  :hints (("Goal" :in-theory (enable step-time-measure-nnrat-fix))))

(defthmd step-time-uav-state-fix
  (implies
   (syntaxp (symbolp ens))
   (equal (step-time dt ens)
          (step-time dt (uav-state-fix ens))))
  :hints (("Goal" :expand (step-time dt (uav-state-fix ens)))))

(defcong uav-state-equiv equal (step-time dt ens) 2
  :hints (("Goal" :in-theory (enable step-time-uav-state-fix))))

(defthmd step-time-nnrat-fix
  (implies
   (syntaxp (symbolp dt))
   (equal (step-time dt ens)
          (step-time (nnrat-fix dt) ens)))
  :hints (("Goal" :expand (step-time (nnrat-fix dt) ens))))

(defcong nnrat-equiv equal (step-time dt ens) 1
  :hints (("Goal" :in-theory (enable step-time-nnrat-fix))))

(defun-sk step-time-always-terminates ()
  (forall (dt ens) (step-time-domain dt ens)))

(defthm step-time-always-terminates-implication
  (implies
   (step-time-always-terminates)
   (step-time-domain dt ens))
  :hints (("Goal" :use step-time-always-terminates-necc)))

(in-theory (disable step-time-always-terminates))

(encapsulate
    ()

  (local
   (defthm MIN-MIN-TIME-TO-IMPACT-FOR-UAV-uav-state-fix
     (implies
      (syntaxp (symbolp ens))
      (equal (MIN-MIN-TIME-TO-IMPACT-FOR-UAV ENS)
             (MIN-MIN-TIME-TO-IMPACT-FOR-UAV (uav-state-fix ENS))))))
  
  (local (in-theory (disable UAV-STATE-EQUIV-1-IMPLIES-EQUAL-MIN-MIN-TIME-TO-IMPACT-FOR-UAV)))
  
  (defthm LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-MIN-MIN-TIME-TO-IMPACT-FOR-UAV-helper
    (implies
     (<= (nnrat-fix dt) (MIN-MIN-TIME-TO-IMPACT-FOR-UAV ENS))
     (LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT dt (uav-state-fix ENS))))

  )


(def::un next-step-dt (step ens)
  (declare (xargs :fty ((nnrat uav-state) uav-state)))
  (let ((step (min step (MIN-MIN-TIME-TO-IMPACT-FOR-UAV ENS))))
    (LET ((ENS (MOVE STEP ENS)))
         (LET ((ENS (SHARE ENS)))
              (FLIP ENS)))))

(defthmd val-0-next-step
  (equal (val 0 (next-step dt ens))
         (if (< (nnrat-fix dt) (MIN-MIN-TIME-TO-IMPACT-FOR-UAV ENS)) 0
           (- (nnrat-fix dt) (MIN-MIN-TIME-TO-IMPACT-FOR-UAV ENS))))
  :hints (("Goal" :in-theory (enable next-step))))

(defthmd val-1-next-step
  (equal (val 1 (next-step dt ens))
         (next-step-dt (min (nnrat-fix dt) (MIN-MIN-TIME-TO-IMPACT-FOR-UAV ENS)) ens))
  :hints (("Goal" :in-theory (enable next-step))))

(in-theory (disable next-step-dt))

(defthm step-time-less
  (implies
   (and
    (<= (nnrat-fix a) (MIN-MIN-TIME-TO-IMPACT-FOR-UAV ENS))
    (STEP-TIME-ALWAYS-TERMINATES))
   (equal (STEP-TIME A ens)
          (if (equal (nnrat-fix a) 0) (uav-state-fix ens)
            (NEXT-STEP-DT A ens))))
  :hints (("Goal" :in-theory (enable val-0-next-step val-1-next-step)
           :expand (STEP-TIME A ens))))

(defthm min-min-time-to-impact-for-uav-property-derived
  (implies
   (and
    (uav-state-p ens)
    (< (nnrat-fix dt) (MIN-MIN-TIME-TO-IMPACT-FOR-UAV ENS))
    (IMPENDING-IMPACT-EVENT-FOR-UAV j ENS))
   (< (nnrat-fix dt) (min-time-to-impact-for-uav j ens)))
  :rule-classes :linear)

(defthm current-location-ensemble-index-congruence
  (implies
   (and
    (equal (ENSEMBLE-INDEX X ENS) y)
    (syntaxp (good-index-rewrite-order x y)))
   (equal (current-location x ens)
          (current-location y ens))))

(defthm not-equal-is-less-than
  (implies
   (and
    (uav-state-p ens)
    (not (equal (current-location x ens) (current-location y ens))))
   (if (< (ENSEMBLE-INDEX X ENS) (ENSEMBLE-INDEX Y ENS))
       (< (current-location x ens) (current-location y ens))
     (< (current-location y ens) (current-location x ens))))
  :hints (("Goal" :in-theory (enable current-location-order)))
  :rule-classes nil)

(in-theory (disable CO-LOCATED-LEFT-INDEX-BOUNDS-ESCORT-LEFT-INDEX-FLIP
                    ESCORT-LEFT-INDEX-FLIP-UPPER-BOUND))

;;
;; What we are going to want are predicates that recognize
;; when (share ) and (flip ) have no effect.  Presumably
;; (share (share )) = (share )
;; (flip (flip )) = (flip )
;;
;; We already have the start of one such predicate (shared-state ens) for share.
;;

#+joe
(defthm share-move-commute
  (implies
   (and
    (< (nnrat-fix dt) (MIN-TIME-TO-IMPACT-FOR-UAV x ens))
    (uav-state-p ens))
   (equal (get-uav x (share (move dt ens)))
          (get-uav x (move dt (share ens)))))
  :hints (("Goal" :in-theory (enable move-uav share-uav))
          ("Subgoal 32.2.12" :by nil)
          ("Subgoal 32.2.11" :in-theory (enable MIN-TIME-TO-IMPACT-FOR-UAV))
          ))

#+joe
(skip-proofs
 (defthm MIN-MIN-TIME-TO-IMPACT-FOR-UAV-NEXT-STEP-DT
   (equal (MIN-MIN-TIME-TO-IMPACT-FOR-UAV (NEXT-STEP-DT B ENS))
          (- (MIN-MIN-TIME-TO-IMPACT-FOR-UAV ens) (nnrat-fix B)))))

#+joe
(defthm next-step-dt-composition
  (implies
   (<= (+ (NNRAT-FIX A) (NNRAT-FIX B)) (MIN-MIN-TIME-TO-IMPACT-FOR-UAV ENS))
   (equal (NEXT-STEP-DT A (NEXT-STEP-DT B ENS))
          (NEXT-STEP-DT (+ (NNRAT-FIX A) (NNRAT-FIX B)) ens))))

#|
(defthm okie-dokie
  (IMPLIES
   (AND
    (uav-state-p ens)
    (STEP-TIME-ALWAYS-TERMINATES)
    (not (equal (+ (NNRAT-FIX A) (NNRAT-FIX B)) 0)))
   (EQUAL (STEP-TIME (+ (NNRAT-FIX A)
                        (VAL 0 (NEXT-STEP B ENS)))
                     (VAL 1 (NEXT-STEP B ENS)))
          (STEP-TIME (+ (NNRAT-FIX A) (NNRAT-FIX B))
                     ens)))
  :hints (("Goal" :do-not-induct t
           :expand (STEP-TIME (+ (NNRAT-FIX A) (NNRAT-FIX B)) ens))))

(defthm step-time-composition
  (implies
   (and
    (uav-state-p ens)
    (step-time-always-terminates))
   (equal (step-time a (step-time b ens))
          (step-time (+ (nnrat-fix a) (nnrat-fix b)) ens)))
  :hints (("Goal" :induct (step-time b ens)
           :expand (step-time (+ (nnrat-fix a) (nnrat-fix b)) ens))))

|#
