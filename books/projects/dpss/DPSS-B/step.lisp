;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "dpss")
(include-book "events")
(include-book "equiv")

(in-theory (disable STRICTLY-LESS-MEANS-REDUCE-2))

;;
;; Move specification and invariance proof
;;

(def::und default-uav ()
  (declare (xargs :fty (() uav)))
  (UAV! :LP 0 :LC 0 :XX 0 :DX -1 :RC 0 :RP 0))

(in-theory (disable (default-uav)))

(defun default-field-p (x)
  (case-match x
    ((& x) (equal x '(default-uav)))
    (& nil)))

(defun all-default-value-list-p-fn (args)
  (if (not (consp args)) nil
    (cons `(default-field-p ,(car args))
          (all-default-value-list-p-fn (cdr args)))))
          
(defmacro all-default-value-list-p (&rest args)
  `(and ,@(all-default-value-list-p-fn args)))

(defthmd normalize-constructor-def-equiv
  (implies
   (not (default-field-p x))
   (UAV->XX-def-equiv (UAV LP LC XX DX RC RP)
                      (UAV LP LC (UAV->XX (default-uav)) DX RC RP))))

(defthmd normalize-constructor-use-equiv
  (implies
   (not (all-default-value-list-p LP LC DX RC RP))
   (UAV->XX-equiv (UAV LP LC XX DX RC RP)
                  (UAV* (default-uav) :xx XX))))

(def::un move-uav (dt uav)
  (declare (xargs :fty ((nnrat uav) uav)))
  (b* (((UAV* :xx xx :dx dx) uav))
    (UAV* uav :xx (+ xx (* dx dt)))))

(defthm uav->xx-move-uav
  (equal (UAV->xx (move-uav dt uav))
         (+ (UAV->xx uav) (* (nnrat-fix dt) (UAV->dx uav)))))

;; ---------------------------
;; Function specific def-equiv
;; - for each defined field
;; ---------------------------

;; The collection of all fields modified by the function
(defun move-uav-def-equiv (x y)
  (UAV->XX-def-equiv x y))

(defequiv move-uav-def-equiv)

;; Backchain to more specific (general) def-equiv
(defrefinement UAV->XX-def-equiv move-uav-def-equiv)

;; I don't think this is useful ..
(defrefinement move-uav-def-equiv UAV->LC-equiv)
(defrefinement move-uav-def-equiv UAV->RC-equiv)
(defrefinement move-uav-def-equiv UAV->dx-equiv)
(defrefinement move-uav-def-equiv UAV->LP-equiv)
(defrefinement move-uav-def-equiv UAV->RP-equiv)

(defthm UAV->xx-def-equiv-move-uav
  (UAV->XX-def-equiv (move-uav dt uav) uav))

;; -----------------------------------
;; function x field specific use-equiv
;; - for each defined field
;; -----------------------------------

;; The set of fields used to compute each defined field ..
(defun move-uav->XX-use-equiv (x y)
  (and (UAV->XX-equiv x y)
       (UAV->DX-equiv x y)))

(defequiv move-uav->XX-use-equiv)

;; I don't think this is useful ..
(defrefinement move-uav->XX-use-equiv UAV->XX-equiv)
(defrefinement move-uav->XX-use-equiv UAV->DX-equiv)

;; The set of primitive abstractions
(defrefinement UAV->LC-def-equiv move-uav->XX-use-equiv)
(defrefinement UAV->RC-def-equiv move-uav->XX-use-equiv)
(defrefinement UAV->LP-def-equiv move-uav->XX-use-equiv)
(defrefinement UAV->RP-def-equiv move-uav->XX-use-equiv)

(defcong move-uav->XX-use-equiv UAV->XX-equiv (move-uav dt uav) 2
  :hints (("Goal" :in-theory (enable move-uav))))

;; -------------------------------------

(in-theory (disable move-uav))

(encapsulate
    ()
  
  (local
   (defun update-RC (uav)
     (UAV* uav :RC 0)))
   
  (local
   (defthm frankie
     (UAV->RC-def-equiv (update-RC uav) uav)))

  (local (in-theory (disable update-RC)))

  (local
   (defthm zoom
     (equal (UAV->XX (move-uav dt (update-RC uav)))
            (UAV->XX (move-uav dt uav)))))
  
  (local
   (defthm uav-lc-move-uav
     (equal (UAV->LC (move-uav dt uav))
            (UAV->LC uav))))

  (defun buster (x) x)
  
  )

(def::un escort-move-spec (dt e)
  (declare (xargs :fty ((nnrat escort) escort)))
  (b* (((Escort* :xx xx :dx dx) e))
    (Escort* e :xx (+ xx (* dx dt)))))

(in-theory (disable escort-move-spec))

(def::un move-rec (dx i ens)
  (declare (xargs :fty ((nnrat nat any) ens)))
  (let ((uav (move-uav dx (get-uav i ens))))
    (if (zp i) (set-uav i uav ens)
      (set-uav i uav (move-rec dx (1- i) ens)))))

(encapsulate
    ()

  (local
   (defthm move-rec-ens-fix
     (implies
      (syntaxp (symbolp ens))
      (equal (move-rec dx i ens)
             (move-rec dx i (ens-fix ens))))))
  
  (defcong ens-equiv equal (move-rec dx i ens) 3
    :hints (("Goal" :do-not-induct t
             :in-theory (enable ens-equiv-to-ens-fix))))
    
  )

(defthm len-equiv-move-rec
  (len-equiv (move-rec dx i ens) ens))

(defthm all-uavs-move-rec
  (implies
   (and
    (consp ens)
    (all-uavs (double-rewrite ens)))
   (all-uavs (move-rec dx i ens))))

(defthm get-uav-move-rec
  (equal (get-uav j (move-rec dx i ens))
         (if (and (<= (ensemble-index j ens) (ensemble-index i ens))
                  (consp ens))
             (move-uav dx (get-uav j ens))
           (get-uav j ens)))
  :hints (("Goal" :in-theory (enable ensemble-index-strict-ordering-implies-index-strict-ordering-linear))
          (pattern-hint
           (not (EQUAL (MOVE-UAV DX (GET-UAV I ENS))
                       (MOVE-UAV DX (GET-UAV J ENS))))
           :use ((:instance get-uav-ensemble-index-congruence
                            (I I)
                            (J J))))))

(def::un move (dx ens)
  (declare (xargs :fty ((nnrat ens) ens)))
  (move-rec dx (len ens) ens))

(defthm len-equiv-move
  (len-equiv (move dx ens) ens))

(defthm all-uavs-move
  (implies
   (and
    (all-uavs ens)
    (consp (double-rewrite ens)))
   (all-uavs (move dx ens))))

(defthm ensemble-index-true-upper-bound
  (<= (ENSEMBLE-INDEX J ENS)
      (ENSEMBLE-INDEX (LEN ENS) ENS))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable ensemble-index))))

(defthm get-uav-move
  (equal (get-uav j (move dx ens))
         (if (not (consp ens))
             (get-uav j ens)
           (move-uav dx (get-uav j ens)))))

(in-theory (disable move))

(defun current-location-move (dx x est)
  (if (left-moving-p x est) (- (current-location x est) (nnrat-fix dx))
    (+ (current-location x est) (nnrat-fix dx))))

(defthm current-location-move-lemma
  (equal (current-location x (move dx ens))
         (if (consp ens)
             (current-location-move dx x ens)
           (current-location x ens)))
  :hints (("Goal" :in-theory (e/d (SIGN-P-IMPLIES-BODY move-uav LEFT-MOVING-P current-location)
                                  (UAV->DX-TO-LEFT-MOVING-P
                                   UAV->DX-TO-NOT-LEFT-MOVING-P
                                   UAV->DX-TO-RIGHT-MOVING-P
                                   UAV->xx-to-current-location))
           :cases ((equal (UAV->DX (GET-UAV X ENS)) -1)))))

;; These rules will require bounds on 'dx' ..

(defthm left-moving-p-move
  (equal (left-moving-p x (move dt ens))
         (left-moving-p x ens))
  :hints (("Goal" :in-theory (e/d (MOVE-UAV
                                   left-moving-p)
                                  (UAV->DX-TO-RIGHT-MOVING-P
                                   UAV->DX-TO-NOT-LEFT-MOVING-P
                                   UAV->DX-TO-LEFT-MOVING-P)))))

(defthm uav->dx-move-uav
  (equal (UAV->DX (MOVE-UAV dx uav))
         (UAV->DX uav)))

(defthm primitive-accessor-invariant-move
  (and (equal (LEFTPERIMETERGUESS x (MOVE DT ENS))
              (LEFTPERIMETERGUESS x ens))
       (equal (RightPERIMETERGUESS x (MOVE DT ENS))
              (RightPERIMETERGUESS x ens))
       (equal (LEFTCOUNTGUESS x (MOVE DT ENS))
              (LEFTCOUNTGUESS x  ens))
       (equal (RightCOUNTGUESS x (MOVE DT ENS))
              (RightCOUNTGUESS x  ens)))
  :hints (("Goal" :in-theory (e/d (LEFTCOUNTGUESS
                                   LEFTPERIMETERGUESS
                                   RightCOUNTGUESS
                                   RightPERIMETERGUESS
                                   )
                                  (
                                   UAV->LC-TO-LEFTCOUNTGUESS
                                   UAV->RC-TO-RIGHTCOUNTGUESS
                                   UAV->LP-TO-LEFTPERIMETERGUESS
                                   UAV->RP-TO-RIGHTPERIMETERGUESS
                                   )))))

(defthm signed-multiplication
  (implies
   (and (rationalp v) (sign-p s))
   (equal (* v s)
          (if (equal s 1) v (* -1 v)))))

(defthm equal-uav->dx--1-to-left-moving
  (equal (equal (uav->dx (get-uav i ens)) -1)
         (left-moving-p i ens))
  :hints (("Goal" :in-theory (e/d (left-moving-p)
                                  (UAV->DX-TO-LEFT-MOVING-P
                                   UAV->DX-TO-RIGHT-MOVING-P
                                   UAV->DX-TO-NOT-LEFT-MOVING-P)))))

(theory-invariant (incompatible (:rewrite equal-uav->dx--1-to-left-moving)
                                (:definition left-moving-p)))

(defthm escort-right-index-move
  (equal (escort-right-index j (move dx ens))
         (escort-right-index j ens))
  :hints (("Goal" :induct (escort-right-index j ens)
           :do-not-induct t)
          (stable-p :expand (ESCORT-RIGHT-INDEX J (MOVE DX ENS)))))

(defthm escort-left-index-move
  (equal (escort-left-index j (move dx ens))
         (escort-left-index j ens))
  :hints (("Goal" :induct (escort-left-index j ens)
           :do-not-induct t)
          (stable-p :expand (escort-left-index j (move dx ens)))))

(defthm get-escort-move-spec
  (equal (get-escort i (move dx est))
         (if (consp est)
             (escort-move-spec dx (get-escort i est))
           (get-escort i est)))
  :hints (("Goal" :in-theory (enable get-escort
                                     escort-move-spec))))

(defthm secondary-accessor-invariant-move
  (and (equal (meta-left-escort-count x (move dx est))
              (meta-left-escort-count x est))
       (equal (meta-right-escort-count x (move dx est))
              (meta-right-escort-count x est)))
  :hints ((stable-p :in-theory (enable escort-move-spec))))

(defthm all-current-locations-bounded-p-move-invariant
  (implies
   (and
    (uav-state-p ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (all-current-locations-bounded-p (move dt ens)))
  :hints (("goal" :in-theory (enable all-current-locations-bounded-p))))

(defthmd equal-bools-to-iff
  (implies
   (booleanp x)
   (iff (equal x y)
        (and (booleanp y)
             (iff x y)))))

(defthm all-within-escort-left-coordinated-p-move-invariant
  (implies (and (uav-state-p ens)
                (lte-min-time-to-impending-impact-event dt ens))
           (all-within-escort-left-coordinated-p (move dt ens)))
  :hints (("goal" :expand (all-within-escort-left-coordinated-p (move dt ens)))
          (pattern-hint
           (:term (all-within-escort-left-coordinated-p-witness ens))
           :use ((:instance all-within-escort-left-coordinated-p-consequence
                            (i (val 0 (all-within-escort-left-coordinated-p-witness ens)))
                            (x (val 1 (all-within-escort-left-coordinated-p-witness ens))))))
          ))

(defthm all-within-escort-right-coordinated-p-move-invariant
  (implies (and (uav-state-p ens)
                (lte-min-time-to-impending-impact-event dt ens))
           (all-within-escort-right-coordinated-p (move dt ens)))
  :hints (("goal" :expand (all-within-escort-right-coordinated-p (move dt ens)))
          (pattern-hint
           (:term (all-within-escort-right-coordinated-p-witness ens))
           :use ((:instance all-within-escort-right-coordinated-p-consequence
                            (i (val 0 (all-within-escort-right-coordinated-p-witness ens)))
                            (x (val 1 (all-within-escort-right-coordinated-p-witness ens))))))))

(with-arithmetic
 (defthm all-ordered-locations-move-invariant
   (implies
    (and (uav-state-p ens)
         (lte-min-time-to-impending-impact-event dt ens))
    (all-ordered-locations (move dt ens)))
   :hints (("goal" :expand (all-ordered-locations (move dt ens)))
           (pattern-hint
            (:term (all-ordered-locations-witness ens))
            :cases ((equal (ensemble-index (all-ordered-locations-witness ens) ens)
                           0)))))
 )

(defthm uav-equiv-move
  (implies
   (and
    (uav-state-p ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (uav-state-p (move dt ens)))
  :hints (("Goal" :do-not-induct t
           :expand (uav-state-p (move dt ens)))))

(defthm primitive-move-invariants-derived-1
  (and
   (equal (meta-left-neighbor-index x (move dt est))
          (meta-left-neighbor-index x est))
   (equal (meta-right-neighbor-index x (move dt est))
          (meta-right-neighbor-index x est))
   (equal (meta-escort-size x (move dt est))
          (meta-escort-size x est))
   )
  :hints (("goal" :in-theory (enable meta-escort-size
                                     meta-left-neighbor-index
                                     meta-right-neighbor-index
                                     escort-move-spec
                                     ))))

(defthm primitive-move-invariants-derived-2
  (equal (seg-size x (move dx est))
         (seg-size x est))
  :hints (("goal" :in-theory (enable seg-size
                                     UAV->SEG-SIZE))))

(in-theory (disable ESCORT-RIGHT-INDEX ESCORT-LEFT-INDEX))

(defthm times-unit-minus
  (equal (* -1 x) (- x)))

(with-arithmetic
 (defthm primitive-move-invariants-derived-3
   (implies
    (uav-state-p ens)
   (and
    (equal (right-moving-escort-split-location x (move dt ens))
           (right-moving-escort-split-location x ens))
    (equal (left-moving-escort-split-location x (move dt ens))
           (left-moving-escort-split-location x ens))
    (equal (right-moving-uav-split-location x (move dt ens))
           (right-moving-uav-split-location x ens))
    (equal (left-moving-uav-split-location x (move dt ens))
           (left-moving-uav-split-location x ens))
    ))
  :hints (("goal" :do-not-induct t
            :in-theory (e/d (seg-size
                             get-escort
                             escort->size
                             UAV->SEG-SIZE
                             ESCORT->SEG-SIZE
                             ESCORT->RIGHT-MOVING-ESCORT-SPLIT-LOCATION
                             ESCORT-MOVE-SPEC
                             RIGHT-MOVING-UAV-SPLIT-LOCATION
                             LEFT-MOVING-UAV-SPLIT-LOCATION
                             right-moving-escort-split-location
                             left-moving-escort-split-location
                             ALL-WITHIN-ESCORT-LEFT-COORDINATED-P-CONSEQUENCE
                             ALL-WITHIN-ESCORT-RIGHT-COORDINATED-P-CONSEQUENCE
                             ESCORT->LEFT-MOVING-ESCORT-SPLIT-LOCATION
                             UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION
                             UAV->LEFT-MOVING-UAV-SPLIT-LOCATION
                             move-uav
                             )
                            (seg-size-fn2
                             UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-TO-LEFT-MOVING-UAV-SPLIT-LOCATION
                             UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION-TO-RIGHT-MOVING-UAV-SPLIT-LOCATION
                             )))
          )))

(local
 (with-arithmetic
  (defthm primitive-move-invariants-derived-check
    (implies
     (uav-state-p ens)
     (and
      (equal (right-moving-escort-split-location x (move dt ens))
             (right-moving-escort-split-location x ens))
      (equal (left-moving-escort-split-location x (move dt ens))
             (left-moving-escort-split-location x ens))
      (equal (right-moving-uav-split-location x (move dt ens))
             (+ (leftperimeterguess x ens) (right-moving-uav-split-offset-fn (leftcountguess x ens) (seg-size x ens))))
      (equal (left-moving-uav-split-location x (move dt ens))
             (+ (leftperimeterguess x ens) (left-moving-uav-split-offset-fn (leftcountguess x ens) (seg-size x ens))))
      ))
    :rule-classes nil
    :hints (("goal" :do-not-induct t
            :in-theory (e/d (seg-size
                             get-escort
                             escort->size
                             UAV->SEG-SIZE
                             ESCORT->SEG-SIZE
                             ESCORT->RIGHT-MOVING-ESCORT-SPLIT-LOCATION
                             ESCORT-MOVE-SPEC
                             RIGHT-MOVING-UAV-SPLIT-LOCATION
                             LEFT-MOVING-UAV-SPLIT-LOCATION
                             right-moving-escort-split-location
                             left-moving-escort-split-location
                             ALL-WITHIN-ESCORT-LEFT-COORDINATED-P-CONSEQUENCE
                             ALL-WITHIN-ESCORT-RIGHT-COORDINATED-P-CONSEQUENCE
                             ESCORT->LEFT-MOVING-ESCORT-SPLIT-LOCATION
                             UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION
                             UAV->LEFT-MOVING-UAV-SPLIT-LOCATION
                             move-uav
                             )
                            (seg-size-fn2
                             UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-TO-LEFT-MOVING-UAV-SPLIT-LOCATION
                             UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION-TO-RIGHT-MOVING-UAV-SPLIT-LOCATION
                             )))))))

(def::und share-uav (lp lc rc rp uav)
  (declare (xargs :fty ((rational int int rational uav) uav)))
  (UAV* uav :LP lp :LC (nfix lc) :RC (nfix rc) :RP rp))

(def::un share-region (min max lp lc rc rp ens)
  (declare (xargs :fty ((nat nat rational int int rational ens) ens)
                  :measure (nfix max)))
  (let ((min (ensemble-index min ens))
        (max (ensemble-index max ens)))
    (if (<= max min) (set-uav min (share-uav lp lc rc rp (get-uav min ens)) ens)
      (let ((uav (get-uav max ens)))
        (let ((uav (share-uav lp lc rc rp uav)))
          (set-uav max uav (share-region min (1- max) lp (1- lc) (1+ rc) rp ens)))))))

(defthm len-equiv-share-region
  (len-equiv (share-region min max lp lc rc rp ens) ens))

(defthm all-uavs-share-region
  (implies
   (and
    (all-uavs ens)
    (consp (double-rewrite ens)))
   (all-uavs (share-region min max lp lc rc rp ens))))

;; move back
(defthm not-consp-set-uav-reduction
  (implies
   (not (consp ens))
   (equal (set-uav a uav ens) (list-fix ens)))
  :hints (("Goal" :in-theory (enable set-uav))))

(defthm not-consp-reduction
  (implies
   (not (consp ens))
   (equal (share-region min max lp lc rc rp ens) (list-fix ens))))

(defthm share-region-ensemble-index-min
  (equal (share-region (ensemble-index min ens) max lp lc rc rp ens)
         (share-region min max lp lc rc rp ens))
  :hints (("Goal" :expand ((share-region (ensemble-index min ens) max lp lc rc rp ens)
                           (share-region min max lp lc rc rp ens)))))

(defthm share-region-ensemble-index-max
  (equal (share-region min (ensemble-index max ens) lp lc rc rp ens)
         (share-region min max lp lc rc rp ens))
  :hints (("Goal" :expand ((share-region min (ensemble-index max ens) lp lc rc rp ens)
                           (share-region min max lp lc rc rp ens)))))

(in-theory (disable (:compound-recognizer CONSP-WHEN-UAV-P)))

(defthm current-location-share-region
  (equal (current-location x (share-region min max lp lc rc rp ens))
         (current-location x ens))
  :hints (("Goal" :in-theory (e/d (share-uav current-location)
                                  (UAV->XX-TO-CURRENT-LOCATION)))))


(defthm get-uav-share-region
  (implies
   (<= (ensemble-index min ens) (ensemble-index max ens))
   (equal (get-uav i (share-region min max lp lc rc rp ens))
          (if (not (consp ens)) (get-uav i ens)
            (let ((d1 (- (ensemble-index i ens) (ensemble-index min ens)))
                  (d2 (- (ensemble-index max ens) (ensemble-index i ens))))
              (if (and (<= 0 d1) (<= 0 d2))
                  (share-uav lp (- (ifix lc) d2) (+ (ifix rc) d2) rp (get-uav i ens))
                (get-uav i ens))))))
  :hints (("Goal" :induct (share-region min max lp lc rc rp ens)
           :do-not-induct t)
          (pattern-hint
           (NOT (EQUAL (ENSEMBLE-INDEX I ENS)
                       (ENSEMBLE-INDEX MAX ENS)))
           :in-theory (enable ensemble-index))
          (pattern-hint
           (not (EQUAL (SHARE-UAV LP LC RC RP (GET-UAV I ENS))
                       (SHARE-UAV LP LC RC RP (GET-UAV MAX ENS))))
           :in-theory (e/d (GET-UAV-ENSEMBLE-INDEX!)
                           (GET-UAV-ENSEMBLE-INDEX-REDUCTION)))))

(def::un bigger (x)
  (declare (xargs :fty ((rational) rational)))
  (1+ x))

(defthm bigger-is-bigger
  (< (rfix x) (bigger x))
  :rule-classes ((:linear :trigger-terms ((bigger x)))
                 (:forward-chaining :trigger-terms ((bigger x)))))

(in-theory (disable bigger (bigger)))

(def::un smaller (x)
  (declare (xargs :fty ((rational) rational)))
  (1- x))

(defthm smaller-is-smaller
  (< (smaller x) (rfix x))
  :rule-classes ((:forward-chaining :trigger-terms ((smaller x)))
                 (:linear :trigger-terms ((smaller x)))))

(in-theory (disable smaller (smaller)))

(def::un fix-max (LP RP)
  (declare (xargs :fty ((rational rational) rational)))
  (if (< LP RP) RP
    (bigger LP)))

(defthm fix-max-is-bigger
  (< (rfix LP) (fix-max LP RP))
  :rule-classes ((:forward-chaining :trigger-terms ((fix-max LP RP)))
                 (:linear :trigger-terms ((fix-max LP RP)))))

(defthm fix-max-reduction
  (implies
   (< (rfix LP) (rfix RP))
   (equal (fix-max LP RP) (rfix RP))))

(in-theory (disable fix-max (fix-max)))

(def::un fix-min (LP RP)
  (declare (xargs :fty ((rational rational) rational)))
  (if (< LP RP) LP
    (smaller RP)))

(defthm fix-min-is-smaller
  (< (fix-min LP RP) (rfix RP))
  :rule-classes ((:forward-chaining :trigger-terms ((fix-min LP RP)))
                 (:linear :trigger-terms ((fix-min LP RP)))))

(defthm fix-min-reduction
  (implies
   (< (rfix LP) (rfix RP))
   (equal (fix-min LP RP) (rfix LP))))

(in-theory (disable fix-min (fix-min)))

(def::un share-region-wrapper (min max ens)
  (declare (xargs :fty ((nat nat ens) ens)))
  (let ((min (ensemble-index min ens))
        (max (ensemble-index max ens)))
    (if (<= min max)
        (b* ((uavL (get-uav min ens))
             ((UAV* :xx Lxx :LP lp :LC lc) uavL)
             (uavR (get-uav max ens))
             ((UAV* :xx Rxx :RC rc :RP rp) uavR)
             ((mv lp lc rp) (if (equal Lxx (ActualLeftPerimeter))  (mv (ActualLeftPerimeter)  0 (fix-max (ActualLeftPerimeter) rp))  (mv lp lc rp)))
             ((mv rp rc lp) (if (equal Rxx (ActualRightPerimeter)) (mv (ActualRightPerimeter) 0 (fix-min lp (ActualRightPerimeter))) (mv rp rc lp)))
             (lc (+ lc (- max min))))
          (share-region min max lp lc rc rp ens))
      ens)))

(defthm share-region-wrapper-ensemble-index-min
  (equal (share-region-wrapper (ensemble-index min ens) max ens)
         (share-region-wrapper min max ens)))

(defthm share-region-wrapper-ensemble-index-max
  (equal (share-region-wrapper min (ensemble-index max ens) ens)
         (share-region-wrapper min max ens)))

(with-arithmetic
 (defthm get-uav-share-region-wrapper
   (equal (get-uav i (share-region-wrapper min max ens))
          (let ((i   (ensemble-index i ens))
                (max (ensemble-index max ens))
                (min (ensemble-index min ens)))
            (if (and (<= min max) (consp ens))
                (let ((d1 (- i min))
                      (d2 (- max i)))
                  (if (and (<= 0 d1) (<= 0 d2))
                      (b* ((uavL (get-uav min ens))
                           ((UAV* :xx Lxx :LP lp :LC lc) uavL)
                           (uavR (get-uav max ens))
                           ((UAV* :xx Rxx :RC rc :RP rp) uavR)
                           ((mv lp lc rp) (if (equal Lxx (ActualLeftPerimeter)) (mv (ActualLeftPerimeter) 0 (fix-max (ActualLeftPerimeter) rp)) (mv lp lc rp)))
                           ((mv rp rc lp) (if (equal Rxx (ActualRightPerimeter)) (mv (ActualRightPerimeter) 0 (fix-min lp (ActualRightPerimeter))) (mv rp rc lp)))
                           (lc (+ lc (- max min))))
                        (share-uav lp (- (ifix lc) d2) (+ (ifix rc) d2) rp (get-uav i ens)))
                    (get-uav i ens)))
              (get-uav i ens))))
  :hints (("Goal" :do-not-induct t)))
 )

(defthm len-equiv-share-region-wrapper
  (len-equiv (share-region-wrapper min max ens) ens))

(defthm all-uavs-share-region-wrapper
  (implies
   (and
    (all-uavs ens)
    (consp (double-rewrite ens)))
   (all-uavs (share-region-wrapper min max ens))))

(in-theory (disable share-region-wrapper))

(with-arithmetic
 (def::un co-located-right-index (i ens)
  (declare (xargs :fty ((nat ens) nat)
                  :measure (nfix (- (max-ens-index ens) (ensemble-index i   ens)))
                  :hints (("Goal" :in-theory (enable strictly-less-means-reduce-2 nfix)))))
  (let ((i (ensemble-index i   ens)))
    (if (<= (max-ens-index ens) i) (max-ens-index ens)
      (if (equal (current-location i ens)
                 (current-location (1+ i) ens))
          (co-located-right-index (1+ i) ens)
        i))))
 )

(defthm co-located-right-index-ensemble-index
  (equal (co-located-right-index (ensemble-index i ens) ens)
         (co-located-right-index i ens))
  :hints (("Goal" :expand ((co-located-right-index (ensemble-index i   ens) ens)
                           (co-located-right-index i ens))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((co-located-right-index (ensemble-index i ens) ens)))
                 (:forward-chaining :trigger-terms ((co-located-right-index (ensemble-index i ens) ens)))))
         
(defthm co-located-right-index-upper-bound
  (<= (co-located-right-index i ens) (max-ens-index ens))
  :rule-classes ((:linear :trigger-terms ((co-located-right-index i ens)))))

(defthm co-located-right-index-lower-bound
  (<= (ensemble-index i ens) (co-located-right-index i ens))
  :hints (("Goal" :in-theory (enable strictly-less-means-reduce-2)))
  :rule-classes ((:linear :trigger-terms ((co-located-right-index i ens)))))

(defthm ensemble-index-pinching-lemma-plus
  (implies
   (and
    (< (ENSEMBLE-INDEX K ENS)
       (ENSEMBLE-INDEX (+ 1 (ENSEMBLE-INDEX I ENS)) ENS))
    (<= (ENSEMBLE-INDEX I ENS)
        (ENSEMBLE-INDEX K ENS)))
   (equal (ENSEMBLE-INDEX I ENS)
          (ENSEMBLE-INDEX K ENS)))
  :hints (("Goal" :in-theory (enable ENSEMBLE-INDEX)))
  :rule-classes (:forward-chaining
                 (:linear :trigger-terms ((ENSEMBLE-INDEX I ENS)))))

(defthm ensemble-index-pinching-lemma-minus
  (implies
   (and
    (< (ENSEMBLE-INDEX (+ -1 (ENSEMBLE-INDEX I ENS)) ENS)
       (ENSEMBLE-INDEX K ENS))
    (<= (ENSEMBLE-INDEX K ENS)
        (ENSEMBLE-INDEX I ENS)))
   (equal (ensemble-index i ens)
          (ensemble-index k ens)))
  :hints (("Goal" :in-theory (enable ensemble-index)))
  :rule-classes (:forward-chaining
                 (:linear :trigger-terms ((ensemble-index i ens)))))


(defthmd co-located-right-index-fundamental-property
  (implies
   (and
    (<= (ensemble-index i ens) (ensemble-index k ens))
    (<= (ensemble-index k ens) (co-located-right-index i ens)))
   (equal (current-location k ens)
          (current-location i ens)))
  :hints (("Goal" ;;:in-theory (enable ensemble-index-equiv-implies-current-location-equal)
           :in-theory (ensemble-index-equiv-theory)
           :induct (co-located-right-index i ens))
          (stable-p :cases ((equal (ENSEMBLE-INDEX K ENS) (ENSEMBLE-INDEX I ENS))))))

(defthm co-located-right-index-within-range-linear
  (implies
   (and
    (not (equal (co-located-right-index k ens)
                (co-located-right-index i ens)))
    (<=  (ensemble-index i ens) (ensemble-index k ens)))
   (< (co-located-right-index i ens) (ensemble-index k ens)))
  :rule-classes ((:linear :trigger-terms ((co-located-right-index i ens))))
  :hints (("Goal" :induct (co-located-right-index i ens)
           :do-not-induct t
           ;;:in-theory (enable ensemble-index-equiv-implies-current-location-equal))
          )
          (stable-p :expand (CO-LOCATED-RIGHT-INDEX K ENS))
          ))

(defthmd co-located-right-index-within-range
  (implies
   (and
    (<= (ensemble-index i ens) (co-located-right-index k ens))
    (<=  (ensemble-index k ens) (ensemble-index i ens)))
   (iff (equal (co-located-right-index k ens)
               (co-located-right-index i ens)) t)))

(defthm escort-right-index-co-located-right-index-upper-bound
  (<= (escort-right-index i ens)
      (co-located-right-index i ens))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-2 escort-right-index)
           :do-not-induct t
           :expand (CO-LOCATED-right-INDEX I ENS)
           :induct (escort-right-index i ens))))

(defthm co-located-right-index-escort-right-index
  (equal (CO-LOCATED-right-INDEX (ESCORT-right-INDEX I ENS) ENS)
         (CO-LOCATED-right-INDEX I ENS))
  :hints (("Goal" :do-not-induct t
           :use (:instance CO-LOCATED-right-INDEX-WITHIN-RANGE
                           (i (ESCORT-right-INDEX I ENS))
                           (k i)))))

(defun weak-uav-state-p (ens)
  (and (consp ens)
       (all-uavs ens)
       (all-ordered-locations ens)
       (all-current-locations-bounded-p ens)))

(defthm weak-uav-state-p-implies
  (implies
   (weak-uav-state-p ens)
   (and (consp ens)
        (all-uavs ens)
        (all-ordered-locations ens)
        (all-current-locations-bounded-p ens)))
  :rule-classes (:forward-chaining))

(defthm uav-state-implies-weak-uav-state-p
  (implies
   (uav-state-p x)
   (weak-uav-state-p x)))

(in-theory (disable weak-uav-state-p))

(encapsulate
    ()

  (local
   (defthm co-located-means-co-located-right-index-helper
     (implies
      (and
       (all-ordered-locations ens)
       (equal (current-location i ens)
              (current-location k ens))
       (<= (ensemble-index i ens) (ensemble-index k ens)))
      (equal (co-located-right-index k ens)
             (co-located-right-index i ens)))
     :hints (("Goal" :do-not-induct t
              :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-2)
              :do-not '(generalize)
              :induct (co-located-right-index i ens))
             (stable-p :cases ((EQUAL (ENSEMBLE-INDEX K ENS)
                                      (ENSEMBLE-INDEX I ENS))))
             (stable-p :expand (CO-LOCATED-RIGHT-INDEX K ENS))
             )))

  (defthmd co-located-means-co-located-right-index
    (implies
     (and
      (all-ordered-locations ens)
      (equal (current-location i ens)
             (current-location k ens)))
     (iff (equal (co-located-right-index k ens)
                 (co-located-right-index i ens)) t))
    :hints (("Goal" :do-not-induct t
             :cases ((<= (ensemble-index i ens) (ensemble-index k ens))))))

  )
  
(defthmd co-located-right-index-arbitrary-bound
  (implies
   (and
    (all-ordered-locations ens)
    (EQUAL (CURRENT-LOCATION K1 ENS)
           (CURRENT-LOCATION K2 ENS)))
   (<= (ENSEMBLE-INDEX K1 ENS) (CO-LOCATED-RIGHT-INDEX K2 ENS)))
  :rule-classes ((:linear :trigger-terms ((CO-LOCATED-right-INDEX K2 ENS))))
  :hints (("Goal" :do-not-induct t
           :use (:instance co-located-means-co-located-right-index
                           (i k1)
                           (k k2)))))

(encapsulate
    ()

  (local
   (defthm equal-co-located-right-index-implies-co-located-helper
     (implies
      (and
       (equal (co-located-right-index k ens) (co-located-right-index i ens))
       (<= (ensemble-index i ens) (ensemble-index k ens)))
      (equal (current-location k ens)
             (current-location i ens)))
     :hints (("Goal" :induct (co-located-right-index i ens)))))
  
  (defthmd equal-co-located-right-index-implies-co-located
     (implies
      (equal (co-located-right-index k ens) (co-located-right-index i ens))
      (iff (equal (current-location k ens)
                  (current-location i ens)) t))
     :hints (("Goal" :do-not-induct t
              :cases ((<= (ensemble-index k ens) (ensemble-index i ens))))))

  )

(defthmd equal-co-located-right-index-to-co-located
  (implies
   (uav-state-p ens)
   (iff (equal (co-located-right-index k ens)
               (co-located-right-index i ens))
        (equal (current-location k ens)
               (current-location i ens))))
  :hints (("Goal" :in-theory (enable equal-co-located-right-index-implies-co-located
                                     co-located-means-co-located-right-index))))

(defthm co-located-right-index-deliniation
  (implies
   (< (CO-LOCATED-RIGHT-INDEX J ENS) (max-ens-index ens))
   (not (equal (current-location (+ 1 (CO-LOCATED-RIGHT-INDEX J ENS)) ens)
               (current-location (CO-LOCATED-RIGHT-INDEX J ENS) ens)))))

;;
;;
;;

(def::un co-located-left-index (i ens)
  (declare (xargs :fty ((nat ens) nat)
                  :measure (nfix i)))
  (let ((i (ensemble-index i   ens)))
    (if (<= i 0) 0
      (if (equal (current-location i ens)
                 (current-location (1- i) ens))
          (co-located-left-index (1- i) ens)
        i))))

(defthm co-located-left-index-ensemble-index
  (equal (co-located-left-index (ensemble-index i ens) ens)
         (co-located-left-index i ens))
  :hints (("Goal" :expand ((co-located-left-index (ensemble-index i ens) ens)
                           (co-located-left-index i ens))))
  :rule-classes (:rewrite
                 (:linear :trigger-terms ((co-located-left-index (ensemble-index i ens) ens)))
                 (:forward-chaining :trigger-terms ((co-located-left-index (ensemble-index i ens) ens)))))

(defthm co-located-left-index-lower-bound
  (<= 0 (co-located-left-index i ens))
  :rule-classes ((:linear :trigger-terms ((co-located-left-index i ens)))))

(defthm co-located-left-index-upper-bound
  (<= (co-located-left-index i ens) (ensemble-index i ens))
  :rule-classes ((:linear :trigger-terms ((co-located-left-index i ens)))))


(defthmd co-located-left-index-fundamental-property
  (implies
   (and
    (<= (co-located-left-index i ens) (ensemble-index k ens))
    (<= (ensemble-index k ens) (ensemble-index i ens)))
   (equal (current-location k ens)
          (current-location i ens)))
  :hints (("Goal" :induct (co-located-left-index i ens)
           ;;:in-theory (enable ensemble-index-equiv-implies-current-location-equal)
           :do-not-induct t)))

(defthm co-located-left-index-within-range-linear
  (implies
   (and
    (not (equal (co-located-left-index k ens)
                (co-located-left-index i ens)))
    (<= (ensemble-index k ens) (ensemble-index i ens)))
   (< (ensemble-index k ens) (co-located-left-index i ens)))
  :rule-classes ((:linear :trigger-terms ((co-located-left-index i ens))))
  :hints (("Goal" :induct (co-located-left-index i ens) ;; (co-located-left-index k ens)
           :do-not-induct t
           ;;:in-theory (enable ensemble-index-equiv-implies-current-location-equal))
           )
          (stable-p :expand (CO-LOCATED-LEFT-INDEX K ENS))
          ))

(defthmd co-located-left-index-within-range
  (implies
   (and
    (<= (co-located-left-index k ens) (ensemble-index i ens))
    (<= (ensemble-index i ens) (ensemble-index k ens)))
   (iff (equal (co-located-left-index k ens)
               (co-located-left-index i ens)) t)))

(defthm escort-left-index-co-located-left-index-lower-bound
  (<= (co-located-left-index i ens)
      (escort-left-index i ens))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable escort-left-index)
           :do-not-induct t
           :expand (CO-LOCATED-LEFT-INDEX I ENS)
           :induct (escort-left-index i ens))))

(defthm co-located-left-index-escort-left-index
  (equal (CO-LOCATED-LEFT-INDEX (ESCORT-LEFT-INDEX I ENS) ENS)
         (CO-LOCATED-LEFT-INDEX I ENS))
  :hints (("Goal" :do-not-induct t
           :use (:instance CO-LOCATED-LEFT-INDEX-WITHIN-RANGE
                           (i (ESCORT-LEFT-INDEX I ENS))
                           (k i)))))

(encapsulate
    ()
  
  (local
   (defthm co-located-means-co-located-left-index-helper
     (implies
      (and
       (all-ordered-locations ens)
       (equal (current-location i ens)
              (current-location k ens))
       (<= (ensemble-index k ens) (ensemble-index i ens)))
      (equal (co-located-left-index k ens)
             (co-located-left-index i ens)))
     :hints (("Goal" :do-not-induct t
              :do-not '(generalize)
              :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-2)
              :induct (co-located-left-index i ens))
             (stable-p :cases ((EQUAL (ENSEMBLE-INDEX K ENS)
                                      (ENSEMBLE-INDEX I ENS))))
             (stable-p :expand (CO-LOCATED-LEFT-INDEX k ENS))
             )))

  (defthmd co-located-means-co-located-left-index
    (implies
     (and
      (all-ordered-locations ens)
      (equal (current-location i ens)
             (current-location k ens)))
     (iff (equal (co-located-left-index k ens)
                 (co-located-left-index i ens)) t))
    :hints (("Goal" :do-not-induct t
             :cases ((<= (ensemble-index i ens) (ensemble-index k ens))))))

  )

(defthmd co-located-left-index-arbitrary-bound
  (implies
   (and
    (all-ordered-locations ens)
    (EQUAL (CURRENT-LOCATION K1 ENS)
           (CURRENT-LOCATION K2 ENS)))
   (<= (CO-LOCATED-LEFT-INDEX K2 ENS) (ENSEMBLE-INDEX K1 ENS)))
  :rule-classes ((:linear :trigger-terms ((CO-LOCATED-LEFT-INDEX K2 ENS))))
  :hints (("Goal" :do-not-induct t
           :use (:instance co-located-means-co-located-left-index
                           (i k1)
                           (k k2)))))

(encapsulate
    ()

  (local
   (defthm equal-co-located-left-index-implies-co-located-helper
     (implies
      (and
       (equal (co-located-left-index k ens) (co-located-left-index i ens))
       (<= (ensemble-index k ens) (ensemble-index i ens)))
      (equal (current-location k ens)
             (current-location i ens)))
     :hints (("Goal" ;;:in-theory (enable ensemble-index-equiv-implies-current-location-equal)
              :induct (co-located-left-index i ens)))))

  (defthmd equal-co-located-left-index-implies-co-located
     (implies
      (equal (co-located-left-index k ens) (co-located-left-index i ens))
      (iff (equal (current-location k ens)
                  (current-location i ens)) t))
     :hints (("Goal" :do-not-induct t
              :cases ((<= (ensemble-index k ens) (ensemble-index i ens))))))

  )

(defthmd equal-co-located-left-index-to-co-located
  (implies
   (uav-state-p ens)
   (iff (equal (co-located-left-index k ens)
               (co-located-left-index i ens))
        (equal (current-location k ens)
               (current-location i ens))))
  :hints (("Goal" :in-theory (enable equal-co-located-left-index-implies-co-located
                                     co-located-means-co-located-left-index))))

(defthm co-located-left-index-deliniation
  (implies
   (< 0 (CO-LOCATED-LEFT-INDEX J ENS))
   (not (equal (current-location (+ -1 (CO-LOCATED-LEFT-INDEX J ENS)) ens)
               (current-location (CO-LOCATED-LEFT-INDEX J ENS) ens)))))

(defthmd co-located-left-index-bounded-by-co-located-right-index
  (implies
   (and
    (<= (ensemble-index m ens) (ensemble-index k ens))
    (<= (ensemble-index k ens) (co-located-right-index m ens)))
   (iff (equal (co-located-left-index k ens)
               (co-located-left-index m ens)) t))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-2)
           :induct (co-located-right-index m ens)
           :expand (CO-LOCATED-LEFT-INDEX (+ 1 (ENSEMBLE-INDEX M ENS)) ENS))))

(defthmd co-located-right-index-bounded-by-co-located-left-index
  (implies
   (and
    (<= (co-located-left-index m ens)  (ensemble-index k ens))
    (<= (ensemble-index k ens) (ensemble-index m ens)))
   (iff (equal (co-located-right-index k ens)
               (co-located-right-index m ens)) t))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-2)
           :induct (co-located-left-index m ens)
           :expand (CO-LOCATED-right-INDEX (+ -1 (ENSEMBLE-INDEX M ENS)) ENS))))

(defthmd equal-current-location-implies-bounds
  (implies
   (and
    (equal (current-location x ens)
           (current-location y ens))
    (all-ordered-locations ens))
   (and (<= (co-located-left-index x ens) (ensemble-index y ens))
        (<= (ensemble-index y ens) (co-located-right-index x ens))))
  :hints (("Goal" :in-theory (enable co-located-left-index-arbitrary-bound
                                     co-located-right-index-arbitrary-bound)))
  :rule-classes (:forward-chaining))

(defthmd co-located-index-invariant
  (implies
   (and
    (<= (co-located-left-index x ens) (ensemble-index y ens))
    (<= (ensemble-index y ens) (co-located-right-index x ens)))
   (and
    (iff (equal (co-located-left-index y ens)
                (co-located-left-index x ens)) t)
    (iff (equal (co-located-right-index y ens)
                (co-located-right-index x ens)) t)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable co-located-left-index-bounded-by-co-located-right-index
                              co-located-right-index-bounded-by-co-located-left-index
                              co-located-right-index-within-range
                              co-located-left-index-within-range))
          (stable-p :cases ((<= (ensemble-index y ens) (ensemble-index x ens))))
          (stable-p :cases ((<= (ensemble-index y ens) (co-located-left-index x ens))))
          (stable-p :cases ((<= (co-located-right-index x ens) (ensemble-index y ens))))
          ))

(defthmd co-located-index-invariant-forward
  (implies
   (and
    (<= (co-located-left-index x ens) (ensemble-index y ens))
    (<= (ensemble-index y ens) (co-located-right-index x ens)))
   (and
    (equal (co-located-left-index y ens)
           (co-located-left-index x ens))
    (equal (co-located-right-index y ens)
           (co-located-right-index x ens))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable co-located-index-invariant))))

(defthm co-located-idex-escort-index
  (and
   (equal (co-located-left-index (escort-left-index x ens) ens)
          (co-located-left-index x ens))
   (equal (co-located-left-index (escort-right-index x ens) ens)
          (co-located-left-index x ens))
   (equal (co-located-right-index (escort-left-index x ens) ens)
          (co-located-right-index x ens))
   (equal (co-located-right-index (escort-right-index x ens) ens)
          (co-located-right-index x ens)))
  :hints (("Goal" :in-theory (enable co-located-index-invariant))))

;;
;; left and right
;;

(defthm co-located-right-index-of-co-located-left-index
  (implies
   (< 0 (CO-LOCATED-LEFT-INDEX J ENS))
   (equal (CO-LOCATED-RIGHT-INDEX (+ -1 (CO-LOCATED-LEFT-INDEX J ENS)) ENS)
          (+ -1 (CO-LOCATED-LEFT-INDEX J ENS))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-2)
           :expand (CO-LOCATED-RIGHT-INDEX (+ -1 (CO-LOCATED-LEFT-INDEX J ENS)) ENS))))

(defthm co-located-left-index-of-co-located-right-index
  (implies
   (< (CO-LOCATED-RIGHT-INDEX J ENS) (max-ens-index ens))
   (equal (CO-LOCATED-LEFT-INDEX (+ 1 (CO-LOCATED-RIGHT-INDEX J ENS)) ENS)
          (+ 1 (CO-LOCATED-RIGHT-INDEX J ENS))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-2)
           :expand (CO-LOCATED-LEFT-INDEX (+ 1 (CO-LOCATED-RIGHT-INDEX J ENS)) ENS))))

(defthm left-and-right
  (<= (CO-LOCATED-LEFT-INDEX J ENS) (CO-LOCATED-RIGHT-INDEX J ENS))
  :rule-classes :linear)

(def::linear co-located-left-right-index-bounds-left
  (implies
   (and
    (syntaxp (not (equal i j)))
    (< (ENSEMBLE-INDEX J ENS)
       (CO-LOCATED-LEFT-INDEX I ENS)))
   (< (co-located-right-index j ens)
      (co-located-left-index i ens)))
  :hints (("Goal" :do-not-induct t
           :induct (co-located-left-index i ens))
          ("Subgoal *1/3.1"  :induct (CO-LOCATED-RIGHT-INDEX J ENS))
          ))

(def::linear co-located-left-right-index-bounds-right
  (implies
   (and
    (syntaxp (not (equal i j)))
    (< (CO-LOCATED-RIGHT-INDEX J ENS)
       (ENSEMBLE-INDEX I ENS)))
   (< (co-located-right-index j ens)
      (co-located-left-index i ens)))
  :hints (("Goal" :do-not-induct t
           :induct (co-located-right-index j ens))
          ("Subgoal *1/3.1" :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-2)
           :induct (CO-LOCATED-LEFT-INDEX I ENS))
          ))

(defthmd singular-uav-condition
  (iff (equal (CO-LOCATED-RIGHT-INDEX J ENS) (CO-LOCATED-LEFT-INDEX I ENS))
       (and (equal (CO-LOCATED-RIGHT-INDEX J ENS) (ENSEMBLE-INDEX J ENS))
            (equal (CO-LOCATED-LEFT-INDEX I ENS) (ENSEMBLE-INDEX I ENS))
            (equal (ENSEMBLE-INDEX I ENS) (ENSEMBLE-INDEX J ENS))))
  :hints (("Goal" :do-not-induct t
           ;;:in-theory (enable ensemble-index-equiv-implies-current-location-equal)
           :cases ((< (ENSEMBLE-INDEX J ENS) (ENSEMBLE-INDEX I ENS))))
          (stable-p :cases ((<= (ENSEMBLE-INDEX I ENS) (CO-LOCATED-RIGHT-INDEX J ENS))))
          (stable-p :cases ((<= (CO-LOCATED-LEFT-INDEX I ENS) (ENSEMBLE-INDEX J ENS))))
          ))

;; This is one useful special case ..
(defthm lone-uav
  (implies
   (equal (CO-LOCATED-LEFT-INDEX J ENS)
          (CO-LOCATED-RIGHT-INDEX J ENS))
   (and (equal (CO-LOCATED-LEFT-INDEX J ENS) (ENSEMBLE-INDEX J ENS))
        (equal (CO-LOCATED-RIGHT-INDEX J ENS) (ENSEMBLE-INDEX J ENS))))
  :hints (("Goal" :use (:instance singular-uav-condition
                                  (i j))))
  :rule-classes ((:linear :trigger-terms ((CO-LOCATED-LEFT-INDEX J ENS)
                                          (CO-LOCATED-RIGHT-INDEX J ENS)))
                 :forward-chaining))

(DEFTHM CO-LOCATED-RIGHT-INDEX-FUNDAMENTAL-PROPERTY-linear
  (IMPLIES (AND (not (EQUAL (CURRENT-LOCATION K ENS)
                            (CURRENT-LOCATION I ENS)))
                (<= (ENSEMBLE-INDEX I ENS)
                    (ENSEMBLE-INDEX K ENS)))
           (< (CO-LOCATED-RIGHT-INDEX I ENS)
              (ENSEMBLE-INDEX K ENS)))
  :rule-classes ((:linear :trigger-terms ((CO-LOCATED-RIGHT-INDEX I ENS))))
  :hints (("Goal" :in-theory (enable CO-LOCATED-RIGHT-INDEX-FUNDAMENTAL-PROPERTY))))

(DEFTHM CO-LOCATED-LEFT-INDEX-FUNDAMENTAL-PROPERTY-linear
  (IMPLIES (AND (not (EQUAL (CURRENT-LOCATION K ENS)
                            (CURRENT-LOCATION I ENS)))
                (<= (ENSEMBLE-INDEX K ENS)
                    (ENSEMBLE-INDEX I ENS)))
           (< (ENSEMBLE-INDEX K ENS)
              (CO-LOCATED-LEFT-INDEX I ENS)))
  :rule-classes ((:linear :trigger-terms ((CO-LOCATED-LEFT-INDEX I ENS))))
  :hints (("Goal" :in-theory (enable CO-LOCATED-LEFT-INDEX-FUNDAMENTAL-PROPERTY))))
  
(defthmd pinched-index-is-co-located
  (implies
   (and
    (<= (co-located-left-index i ens) (ensemble-index k ens))
    (<= (ensemble-index k ens) (co-located-right-index i ens)))
   (equal (current-location k ens)
          (current-location i ens))))

(defthm ensemble-index-p-CO-LOCATED-LEFT-INDEX
  (ensemble-index-p (CO-LOCATED-LEFT-INDEX X ENS) ens)
  :hints (("Goal" :in-theory (enable ensemble-index-p))))

(defthm ensemble-index-p-CO-LOCATED-right-INDEX
  (ensemble-index-p (CO-LOCATED-right-INDEX X ENS) ens)
  :hints (("Goal" :in-theory (enable ensemble-index-p))))

(defthmd current-location-co-located-*-index
  (and (equal (current-location (co-located-right-index i ens) ens)
              (current-location i ens))
       (equal (current-location (co-located-left-index i ens) ens)
              (current-location i ens)))
  :hints (("Goal" :use ((:instance pinched-index-is-co-located
                                   (i i)
                                   (k (co-located-right-index i ens)))
                        (:instance pinched-index-is-co-located
                                   (i i)
                                   (k (co-located-left-index i ens)))))))

(defthmd co-located-index-within-range
  (implies
   (and
    (<= (co-located-left-index i ens) (ensemble-index k ens))
    (syntaxp (not (equal i k)))
    (<= (ensemble-index k ens) (co-located-right-index i ens)))
   (and (equal (co-located-left-index k ens)
               (co-located-left-index i ens))
        (equal (co-located-right-index k ens)
               (co-located-right-index i ens))))
  :hints (("Goal" :cases ((<= (ensemble-index k ens) (ensemble-index i ens)))
           :do-not-induct t)))

(defthmd co-located-index-within-range-alt
  (implies
   (and
    (<= (ensemble-index k ens) (co-located-right-index i ens))
    (syntaxp (not (equal i k)))
    (<= (co-located-left-index i ens) (ensemble-index k ens))
    )
   (and (equal (co-located-left-index k ens)
               (co-located-left-index i ens))
        (equal (co-located-right-index k ens)
               (co-located-right-index i ens))))
  :hints (("Goal" :use co-located-index-within-range)))

(defthm current-location-share-region-wrapper
  (equal (current-location x (share-region-wrapper min max ens))
         (current-location x ens))
  :hints (("Goal" :in-theory (enable share-region-wrapper))))

;;
;; ---
;;

(def::un share-rec (i ens)
  (declare (xargs :fty ((nat ens) ens)
                  :measure (nfix i)))
  (let (;;(i   (ensemble-index i ens))
        (min (co-located-left-index i ens))
        (max (co-located-right-index i ens)))
    (if (zp min) (share-region-wrapper min max ens)
      (let ((ens (share-rec (1- min) ens)))
        (share-region-wrapper min max ens)))))

(defthm len-equiv-share-rec
  (len-equiv (share-rec i ens) ens))

(defthm all-uavs-share-rec
  (implies
   (and
    (all-uavs ens)
    (consp (double-rewrite ens)))
   (all-uavs (share-rec i ens))))

(defthm share-rec-ensemble-index
  (equal (share-rec (ensemble-index i ens) ens)
         (share-rec i ens))
  :hints (("Goal" :expand ((share-rec (ensemble-index i ens) ens)
                           (share-rec i ens)))))

(defthm special-case
  (implies
   (< (co-located-right-index j ens) (ENSEMBLE-INDEX I ENS))
   (equal (GET-UAV I (SHARE-REC J ENS))
          (get-uav i ens)))
  :hints (("goal" :induct (SHARE-REC J ENS)
           :do-not-induct t)))

(in-theory (disable CO-LOCATED-RIGHT-INDEX CO-LOCATED-LEFT-INDEX EQUAL-SIGN-REDUCTION))
           
(defthm current-location-share-rec
  (equal (current-location x (share-rec i ens))
         (current-location x ens)))

(in-theory (disable (share-region-wrapper)))

(with-arithmetic
 (defthm get-uav-share-rec
  (equal (get-uav i (share-rec j ens))
         (let ((i   (ensemble-index i ens))
               (min (co-located-left-index i ens))
               (max (co-located-right-index i ens)))
           (let ((d2 (- max i)))
             (if (and (consp ens) (<= i (co-located-right-index j ens)))
                 (b* ((uavL (get-uav min ens))
                      ((UAV* :xx Lxx :LP lp :LC lc) uavL)
                      (uavR (get-uav max ens))
                      ((UAV* :xx Rxx :RC rc :RP rp) uavR)
                      ((mv lp lc rp) (if (equal Lxx (ActualLeftPerimeter)) (mv (ActualLeftPerimeter)   0 (fix-max (ActualLeftPerimeter) rp)) (mv lp lc rp)))
                      ((mv rp rc lp) (if (equal Rxx (ActualRightPerimeter)) (mv (ActualRightPerimeter) 0 (fix-min lp (ActualRightPerimeter))) (mv rp rc lp)))
                      (lc (+ lc (- max min))))
                   (share-uav lp (- lc d2) (+ rc d2) rp (get-uav i ens)))
               (get-uav i ens)))))
  :hints (("Goal" :induct (share-rec j ens)
           :in-theory (e/d (co-located-index-within-range
                            co-located-index-within-range-alt
                            LEFTPERIMETERGUESS RIGHTCOUNTGUESS RightPERIMETERGUESS LeftCOUNTGUESS)
                           (UAV->LC-TO-LEFTCOUNTGUESS UAV->RC-TO-RightCOUNTGUESS UAV->LP-TO-LEFTPerimeterGUESS UAV->RP-TO-RightPerimeterGuess))
           :do-not-induct t)
          (stable-p :in-theory (e/d (co-located-index-within-range
                                     co-located-index-within-range-alt
                                     STRICTLY-LESS-MEANS-REDUCE-2
                                     LEFTPERIMETERGUESS RIGHTCOUNTGUESS RightPERIMETERGUESS LeftCOUNTGUESS)
                                    (UAV->LC-TO-LEFTCOUNTGUESS UAV->RC-TO-RightCOUNTGUESS UAV->LP-TO-LEFTPerimeterGUESS UAV->RP-TO-RightPerimeterGuess)))
          ))
 )

(def::un share (ens)
  (declare (xargs :fty ((ens) ens)))
  (share-rec (max-ens-index ens) ens))

(defthm len-equiv-share
  (len-equiv (share ens) ens))

(defthm all-uavs-share
  (implies
   (and
    (all-uavs ens)
    (consp (double-rewrite ens)))
   (all-uavs (share ens))))

(def::un get-share-uav (d2 min left uav right max)
  (declare (xargs :fty ((nat nat uav uav uav nat) uav)))
  (b* (((UAV* :xx Lxx :LP lp :LC lc) left)
       ((UAV* :xx Rxx :RC rc :RP rp) right)
       ((mv lp lc rp) (if (equal Lxx (ActualLeftPerimeter))  (mv (ActualLeftPerimeter)  0 (fix-max (ActualLeftPerimeter) rp)) (mv lp lc rp)))
       ((mv rp rc lp) (if (equal Rxx (ActualRightPerimeter)) (mv (ActualRightPerimeter) 0 (fix-min lp (ActualRightPerimeter))) (mv rp rc lp)))
       (lc (+ lc (- max min))))
    (share-uav lp (- lc d2) (+ rc d2) rp uav)))

(def::un get-uav-share-implementation (i ens)
  (declare (xargs :fty ((nat ens) uav)))
  (let ((i   (ensemble-index i ens))
        (min (co-located-left-index i ens))
        (max (co-located-right-index i ens)))
    (let ((d2 (- max i)))
      (if (consp ens)
          (let ((left  (get-uav min ens))
                (uav   (get-uav i   ens))
                (right (get-uav max ens)))
            (get-share-uav d2 min left uav right max))
        (get-uav i ens)))))

(defthm get-uav-share
  (equal (get-uav i (share ens))
         (get-uav-share-implementation i ens)))

(in-theory (disable share))

(defthm primary-invariants-share
  (and
   (equal (current-location x (share ens))
          (current-location x ens))
   (equal (left-moving-p x (share ens))
          (left-moving-p x ens))
   )
  :hints (("Goal" :in-theory (e/d (current-location
                                   left-moving-p
                                   share-uav)
                                  (UAV->xx-to-current-location
                                   UAV->DX-TO-RIGHT-MOVING-P
                                   UAV->DX-TO-NOT-LEFT-MOVING-P
                                   UAV->DX-TO-LEFT-MOVING-P
                                   EQUAL-UAV->DX--1-TO-LEFT-MOVING
                                   )))))

(defthm escort-left-index-share
  (equal (escort-left-index x (share ens))
         (escort-left-index x ens))
  :hints (("Goal" :induct (escort-left-index x ens)
           :do-not-induct t
           :expand (ESCORT-LEFT-INDEX X (SHARE ENS))
           :in-theory (e/d (equal-sign-reduction
                            escort-left-index)
                           (get-uav-share)))))

(defthm escort-right-index-share
  (equal (escort-right-index x (share ens))
         (escort-right-index x ens))
  :hints (("Goal" :induct (escort-right-index x ens)
           :do-not-induct t
           :expand (ESCORT-right-INDEX X (SHARE ENS))
           :in-theory (e/d (equal-sign-reduction
                            escort-right-index)
                           (get-uav-share)))))
  
(defthm perimeter-variants-share
  (and
   (equal (LEFTPERIMETERGUESS x (share ens))
          (if (consp ens)
              (let ((Lindex (co-located-left-index x ens))
                    (Rindex (co-located-right-index x ens)))
                (if (equal (current-location Lindex ens) (ActualLeftPerimeter)) (ActualLeftPerimeter)
                  (if (equal (current-location Rindex ens) (ActualRightPerimeter))
                      (fix-min (LEFTPERIMETERGUESS Lindex ens) (ActualRightPerimeter))
                    (LEFTPERIMETERGUESS Lindex ens))))
            (LEFTPERIMETERGUESS x ens)))
   (equal (RIGHTPERIMETERGUESS x (share ens))
          (if (consp ens)
              (let ((Lindex (co-located-left-index x ens))
                    (Rindex (co-located-right-index x ens)))
                (if (equal (current-location Rindex ens) (ActualRightPerimeter)) (ActualRightPerimeter)
                  (if (equal (current-location Lindex ens) (ActualLeftPerimeter))
                      (fix-max (ActualLeftPerimeter) (RIGHTPERIMETERGUESS Rindex ens))
                    (RIGHTPERIMETERGUESS Rindex ens))))
            (RIGHTPERIMETERGUESS x ens)))
   )
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (share-uav
                            LEFTPERIMETERGUESS
                            RIGHTPERIMETERGUESS)
                           (UAV->LP-TO-LEFTPERIMETERGUESS
                            UAV->RP-TO-RIGHTPERIMETERGUESS
                            )))))

(defthm count-variants-share
  (and
   (equal (LEFTCOUNTGUESS x (share ens))
          (if (consp ens)
              (let* ((min (co-located-left-index x ens))
                     (lc  (leftcountguess min ens))
                     (lxx (current-location min ens)))
                (if (equal lxx (ActualLeftPerimeter)) (- (ensemble-index x ens) min)
                  (+ lc (- (ensemble-index x ens) min))))
            (LEFTCOUNTGUESS x ens)))
   (equal (RightCOUNTGUESS x (share ens))
          (if (consp ens)
              (let* ((max (co-located-right-index x ens))
                     (rc  (rightcountguess max ens))
                     (rxx (current-location max ens)))
                (if (equal rxx (ActualRightPerimeter)) (- max (ensemble-index x ens))
                  (+ rc (- max (ensemble-index x ens)))))
            (RightCOUNTGUESS x  ens)))
   )
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (share-uav
                            LEFTCOUNTGUESS
                            RIGHTCOUNTGUESS)
                           (UAV->LC-TO-LEFTCOUNTGUESS
                            UAV->RC-TO-RIGHTCOUNTGUESS
                            )))))

(def::un escort-share (left Li dl e dr Ri right)
  (declare (xargs :fty ((uav nat nat escort nat nat uav) escort)))
  (b* (((UAV* :xx Lxx :lp lp :lc lc) left)
       ((UAV* :xx Rxx :rp rp :rc rc) right)
       ((mv lp lc rp) (if (equal Lxx (ActualLeftPerimeter)) (mv (ActualLeftPerimeter)   0 (fix-max (ActualLeftPerimeter) rp)) (mv lp lc rp)))
       ((mv rp rc lp) (if (equal Rxx (ActualRightPerimeter)) (mv (ActualRightPerimeter) 0 (fix-min lp (ActualRightPerimeter))) (mv rp rc lp)))
       )
    (Escort* e :lp lp :lc (+ lc dl) :Li Li :Ri Ri :rp rp :rc (+ rc dr))))

;; splitting-event
;; sharing-event

(def::un escort-share-implementation (i ens)
  (declare (xargs :fty ((nat ens) escort)))
  (if (consp ens)
      (escort-share (get-uav (co-located-left-index i ens) ens)
                    (escort-left-index i ens)
                    (- (escort-left-index i ens) (co-located-left-index i ens))
                    (get-escort i ens)
                    (- (co-located-right-index i ens) (escort-right-index i ens))
                    (escort-right-index i ens)
                    (get-uav (co-located-right-index i ens) ens))
    (get-escort i ens)))

(in-theory (disable (share)))

(defthmd escort-left-index-nil-helper
  (equal (ESCORT-LEFT-INDEX (ensemble-index I nil) NIL)
         (escort-left-index 0 nil))
  :hints (("Goal" :in-theory (enable ensemble-index))))

(defthm escort-left-index-nil
  (equal (ESCORT-LEFT-INDEX I NIL)
         (escort-left-index 0 nil))
  :hints (("Goal" :use escort-left-index-nil-helper)))

(defthmd escort-right-index-nil-helper
  (equal (ESCORT-RIGHT-INDEX (ensemble-index I nil) NIL)
         (escort-right-index 0 nil))
  :hints (("Goal" :in-theory (enable ensemble-index))))

(defthm escort-right-index-nil
  (equal (ESCORT-RIGHT-INDEX I NIL)
         (escort-right-index 0 nil))
  :hints (("Goal" :use escort-right-index-nil-helper)))

(defthm get-escort-share
  (equal (get-escort i (share ens))
         (escort-share-implementation i ens))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable get-escort))
          (stable-p :in-theory (enable share-uav))))

(def::un Escort->meta-leftmost-escort-p (esc)
  (declare (xargs :fty ((escort) bool)))
  (equal (Escort->Li esc) 0))

(def::un Escort->meta-rightmost-escort-p (esc max)
  (declare (xargs :fty ((escort nat) bool)))
  (equal (Escort->Ri esc) max))

(def::un escort-share-spec (left esc right) ;; max)
  (declare (xargs :fty ((escort escort escort) escort)))
  (b* (((mv lp rp) (mv (Escort->LP left) (ESCORT->RP right)))
       ((mv lp lc rp) (if (equal (Escort->xx esc) (ActualLeftPerimeter))
                          (mv (ActualLeftPerimeter) (nfix (- (Escort->Li esc) (Escort->Li left))) (fix-max (ACTUALLEFTPERIMETER) rp))
                        (mv lp (nfix (+ (Escort->LC left) (- (Escort->Li esc) (Escort->Li left)))) rp)))
       ((mv rp rc lp) (if (equal (Escort->xx esc) (ActualRightPerimeter))
                          (mv (ActualRightPerimeter) (nfix (- (Escort->Ri right) (Escort->Ri esc))) (fix-min lp (ActualRightPerimeter)))
                        (mv rp (nfix (+ (- (Escort->Ri right) (Escort->Ri esc)) (Escort->RC right))) lp)))
       )
    (Escort* esc :LP lp :LC lc :RC rc :RP rp)))


(defthmd escort-right-neighbor-property
  (implies
   (not (equal (ESCORT-RIGHT-INDEX I ENS) (max-ens-index ens)))
   (or (not (equal (current-location (+ 1 (escort-right-index i ens)) ens)
                   (current-location i ens)))
       (not (equal (left-moving-p (+ 1 (escort-right-index i ens)) ens)
                   (left-moving-p i ens)))))
  :hints (("Goal" :in-theory (enable equal-sign-reduction escort-right-index))))

(defthm escort-left-index-of-escort-right-index
  (implies
   (not (equal (ESCORT-RIGHT-INDEX I ENS) (max-ens-index ens)))
   (equal (ESCORT-LEFT-INDEX (+ 1 (ESCORT-RIGHT-INDEX I ENS)) ENS)
          (+ 1 (escort-right-index i ens))))
  :hints (("Goal" :use escort-right-neighbor-property
           :in-theory (enable equal-sign-reduction STRICTLY-LESS-MEANS-REDUCE-2)
           :expand (ESCORT-LEFT-INDEX (+ 1 (ESCORT-RIGHT-INDEX I ENS)) ENS))))

(defthmd escort-left-neighbor-property
  (implies
   (not (equal (ESCORT-LEFT-INDEX I ENS) 0))
   (or (not (equal (current-location (+ -1 (escort-left-index i ens)) ens)
                   (current-location i ens)))
       (not (equal (left-moving-p (+ -1 (escort-left-index i ens)) ens)
                   (left-moving-p i ens)))))
  :hints (("Goal" :in-theory (enable equal-sign-reduction escort-left-index))))

(defthm escort-left-index-of-escort-left-index
  (implies
   (not (equal (ESCORT-LEFT-INDEX I ENS) 0))
   (equal (ESCORT-RIGHT-INDEX (+ -1 (ESCORT-LEFT-INDEX I ENS)) ENS)
          (+ -1 (escort-left-index i ens))))
  :hints (("Goal" :use escort-left-neighbor-property
           :in-theory (enable equal-sign-reduction ENSEMBLE-INDEX-P ;;STRICTLY-LESS-MEANS-REDUCE-2)
                              )
           :expand (ESCORT-RIGHT-INDEX (+ -1 (ESCORT-LEFT-INDEX I ENS)) ENS))))

;; (defstub there-can-be-only-one (ens) nil)

;; (skip-proofs
;;  (defthm highlander-right
;;    (implies
;;     (there-can-be-only-one ens)
;;     (equal (ESCORT-RIGHT-INDEX (+ 1 (ESCORT-RIGHT-INDEX I ENS)) ens)
;;            (CO-LOCATED-RIGHT-INDEX I ENS)))))

;; (skip-proofs
;;  (defthm highlander-left
;;    (implies
;;     (there-can-be-only-one ens)
;;     (equal (ESCORT-left-INDEX (+ -1 (ESCORT-left-INDEX I ENS)) ens)
;;            (CO-LOCATED-left-INDEX I ENS)))))

;; #+joe
;; (skip-proofs
;;  (defthm alfred-alt
;;    (implies
;;     (and
;;      (there-can-be-only-one ens)
;;      (equal (CURRENT-LOCATION I ENS) (ACTUALRIGHTPERIMETER)))
;;     (< (CURRENT-LOCATION (+ -1 (ESCORT-LEFT-INDEX I ENS)) ens)
;;        (CURRENT-LOCATION I ENS)))
;;    :rule-classes :linear))
   

(defthm co-located-escort-neighbor-bounds-escort-right-index
  (implies
   (and
    (not (equal (ESCORT-RIGHT-INDEX I ENS) (max-ens-index ens)))
    (equal (current-location (1+ (ESCORT-RIGHT-INDEX I ENS)) ens)
           (current-location (CO-LOCATED-RIGHT-INDEX I ENS) ens)))
   (< (ESCORT-RIGHT-INDEX I ENS) (CO-LOCATED-RIGHT-INDEX I ENS)))
  :hints (("Goal" :in-theory (enable ESCORT-RIGHT-INDEX
                                     CO-LOCATED-RIGHT-INDEX)))
  :rule-classes :linear)

(defthm co-located-escort-neighbor-bounds-escort-left-index
  (implies
   (and
    (not (equal (ESCORT-LEFT-INDEX I ENS) 0))
    (equal (current-location (1- (ESCORT-LEFT-INDEX I ENS)) ens)
           (current-location (CO-LOCATED-LEFT-INDEX I ENS) ens)))
   (< (CO-LOCATED-LEFT-INDEX I ENS) (ESCORT-LEFT-INDEX I ENS) ))
  :hints (("Goal" :in-theory (enable ESCORT-LEFT-INDEX
                                     CO-LOCATED-LEFT-INDEX)))
  :rule-classes :linear)

(defthm CO-LOCATED-RIGHT-INDEX-to-ESCORT-RIGHT-INDEX
  (implies
   (and
    (not (equal (ESCORT-RIGHT-INDEX I ENS) (max-ens-index ens)))
    (not (equal (current-location (1+ (ESCORT-RIGHT-INDEX I ENS)) ens)
                (current-location (CO-LOCATED-RIGHT-INDEX I ENS) ens))))
   (equal (CO-LOCATED-RIGHT-INDEX I ENS) (ESCORT-RIGHT-INDEX I ENS)))
  :hints (("Goal" :induct (ESCORT-RIGHT-INDEX I ENS)
           :in-theory (enable ESCORT-RIGHT-INDEX
                              CO-LOCATED-RIGHT-INDEX))
          (stable-p :expand ((CO-LOCATED-RIGHT-INDEX I ENS)))))

(defthm CO-LOCATED-LEFT-INDEX-to-ESCORT-LEFT-INDEX
  (implies
   (and
    (not (equal (ESCORT-LEFT-INDEX I ENS) 0))
    (not (equal (current-location (1- (ESCORT-LEFT-INDEX I ENS)) ens)
                (current-location (CO-LOCATED-LEFT-INDEX I ENS) ens))))
   (equal (CO-LOCATED-LEFT-INDEX I ENS) (ESCORT-left-INDEX I ENS)))
  :hints (("Goal" :induct (ESCORT-LEFT-INDEX I ENS)
           :in-theory (enable ESCORT-LEFT-INDEX
                              CO-LOCATED-LEFT-INDEX))
          (stable-p :expand ((CO-LOCATED-LEFT-INDEX I ENS)))))

;; (skip-proofs
;;  (defthm saturated-right-index
;;    (implies
;;     ;; Interesting .. so we need to prohibit multiple
;;     ;; escorts on the boundaries as well as multiple
;;     ;; escorts in a row.
;;     (and
;;      (there-can-be-only-one ens)
;;      (equal (current-location i ens)
;;             (ACTUALRIGHTPERIMETER)))
;;     (equal (ESCORT-RIGHT-INDEX I ENS)
;;            (MAX-ENS-INDEX ENS)))))

;; (skip-proofs
;;  (defthm saturated-left-index
;;    (implies
;;     (and
;;      (there-can-be-only-one ens)
;;      (equal (current-location i ens)
;;             (ACTUALLEFTPERIMETER)))
;;     (equal (ESCORT-left-INDEX I ENS)
;;            0))))

(encapsulate
    ()

  (local (in-theory (disable CO-LOCATED-RIGHT-INDEX-TO-ESCORT-RIGHT-INDEX
                             CURRENT-LOCATION-ENSEMBLE-INDEX-EQUIV-REWRITE
                             lone-uav
                             CO-LOCATED-LEFT-INDEX-TO-ESCORT-LEFT-INDEX
                             CO-LOCATED-LEFT-RIGHT-INDEX-BOUNDS-RIGHT
                             )))
  
  (defthm co-located-right-index-jumps-the-shark
    (implies
     (and
      (not (equal (ESCORT-RIGHT-INDEX I ENS) (max-ens-index ens)))
      (equal (CURRENT-LOCATION I ENS)
             (CURRENT-LOCATION (+ 1 (ESCORT-RIGHT-INDEX I ENS)) ENS)))
     (equal (CO-LOCATED-RIGHT-INDEX (+ 1 (ESCORT-RIGHT-INDEX I ENS)) ens)
            (CO-LOCATED-RIGHT-INDEX I ens)))
    :hints (("Goal" :induct (ESCORT-RIGHT-INDEX I ENS)
             :do-not-induct t
             :expand (CO-LOCATED-RIGHT-INDEX I ens)
             :in-theory (enable equal-sign-reduction
                                ESCORT-RIGHT-INDEX CO-LOCATED-RIGHT-INDEX))))
  
  (defthm co-located-left-index-jumps-the-shark
    (implies
     (and
      (not (equal (ESCORT-left-INDEX I ENS) 0))
      (equal (CURRENT-LOCATION I ENS)
             (CURRENT-LOCATION (+ -1 (ESCORT-LEFT-INDEX I ENS)) ENS)))
     (equal (CO-LOCATED-LEFT-INDEX (+ -1 (ESCORT-LEFT-INDEX I ENS)) ens)
            (CO-LOCATED-LEFT-INDEX I ens)))
    :hints (("Goal" :induct (ESCORT-left-INDEX I ENS)
             :do-not-induct t
             :expand (CO-LOCATED-LEFT-INDEX I ens)
             :in-theory (enable equal-sign-reduction
                                ESCORT-LEFT-INDEX
                                CO-LOCATED-LEFT-INDEX))))
  
  (defthm reduce-right-1
    (equal (ESCORT-RIGHT-INDEX (CO-LOCATED-RIGHT-INDEX I ENS) ENS)
           (CO-LOCATED-RIGHT-INDEX I ENS))
    :hints (("Goal" :in-theory (enable CO-LOCATED-RIGHT-INDEX
                                       ESCORT-RIGHT-INDEX))))
  
  (defthm reduce-left-1
    (equal (ESCORT-LEFT-INDEX (CO-LOCATED-LEFT-INDEX I ENS) ENS)
           (CO-LOCATED-LEFT-INDEX I ENS))
    :hints (("Goal" :in-theory (enable CO-LOCATED-LEFT-INDEX
                                       ESCORT-LEFT-INDEX))))

  )
  
(encapsulate
    ()

  
  (local (in-theory (disable zp-nfix zp-open lone-uav
                             ;;CO-LOCATED-RIGHT-INDEX-TO-ESCORT-RIGHT-INDEX
                             CURRENT-LOCATION-ENSEMBLE-INDEX-EQUIV-REWRITE)))

  (defthm escort-share-implementation-correctness
    (equal (escort-share-implementation i ens)
           (if (not (consp ens)) (get-escort i ens)
             ;;
             ;; That is the problem .. get-escort is trimming the co-located region.
             ;;
             (escort-share-spec (get-escort (CO-LOCATED-left-INDEX I ENS) ens)
                                (get-escort i ens)
                                (get-escort (CO-LOCATED-right-INDEX I ENS) ens)
                                )))
    :hints (("Goal" :do-not '(preprocess)
             :in-theory (e/d (current-location-co-located-*-index
                              escort->size get-escort)
                             nil))))

  (defthm co-located-left-index-on-left-perimeter
    (implies
     (and
      (all-current-locations-bounded-p ens)
      (ALL-ORDERED-LOCATIONS ENS)
      (equal (CURRENT-LOCATION I ENS)
             (ActualLeftPerimeter)))
     (equal (CO-LOCATED-left-INDEX I ENS) 0))
    :hints (("Goal" :in-theory (enable CO-LOCATED-left-INDEX))))
  
  (defthm co-located-right-index-on-right-perimeter
    (implies
     (and
      (all-current-locations-bounded-p ens)
      (ALL-ORDERED-LOCATIONS ENS)
      (equal (CURRENT-LOCATION I ENS)
             (ActualRightPerimeter)))
     (equal (CO-LOCATED-right-INDEX I ENS) (max-ens-index ens)))
    :hints (("Goal" :in-theory (enable strictly-less-means-reduce-2
                                       CO-LOCATED-right-INDEX))))
  

  )
  
(in-theory (disable ZP-OPEN ZP-NFIX EQUAL-SIGN-REDUCTION BODY-IMPLIES-SIGN-P))

(in-theory
 (disable
  CURRENT-LOCATION-ORDER
  LONE-UAV
  CO-LOCATED-RIGHT-INDEX-TO-ESCORT-RIGHT-INDEX
  CO-LOCATED-LEFT-INDEX-TO-ESCORT-LEFT-INDEX))

(defthm uav-state-p-share
  (implies
   (weak-uav-state-p ens)
   (uav-state-p (share ens)))
  :otf-flg t
  :hints (("Goal" :do-not-induct t
           :expand (uav-state-p (share ens))
           :in-theory (enable equal-current-location-implies-bounds
                              leftcountguess-co-located-linear
                              rightcountguess-co-located-linear
                              co-located-left-index-arbitrary-bound
                              co-located-right-index-arbitrary-bound
                              all-ordered-locations-implication
                              ALL-CURRENT-LOCATIONS-BOUNDED-P
                              ALL-ORDERED-LOCATIONS
                              ALL-WITHIN-ESCORT-LEFT-COORDINATED-P
                              ALL-WITHIN-ESCORT-RIGHT-COORDINATED-P
                              ))
          (pattern-hint
           (:and
            (:term (CO-LOCATED-RIGHT-INDEX i ens))
            (:term (CO-LOCATED-RIGHT-INDEX k ens))
            (equal (current-location i ens)
                   (current-location k ens)))
           :use ((:instance co-located-means-co-located-right-index
                            (i   i)
                            (k   k)
                            (ens ens))))
          (pattern-hint
           (:and
            (:term (CO-LOCATED-left-INDEX i ens))
            (:term (CO-LOCATED-left-INDEX k ens))
            (equal (current-location i ens)
                   (current-location k ens)))
           :use ((:instance co-located-means-co-located-left-index
                            (i   i)
                            (k   k)
                            (ens ens))))
          ))

(defun-sk all-co-located-left-coordinated-p (ens)
  (declare (xargs :guard (ens-p ens)))
  (forall (i x)
    (let ((i (nfix i))
          (x (nfix x)))
      (implies
       (and
        (<= (co-located-left-index x ens) (ensemble-index i ens))
        (<= (ensemble-index i ens) (co-located-right-index x ens)))
       (left-coordinated-pair-p i x ens)))))

(in-theory (disable all-co-located-left-coordinated-p))

(defthm all-co-located-left-coordinated-p-implies-rw
  (implies
   (and
    (all-co-located-left-coordinated-p ens)
    (<= (co-located-left-index x ens) (ensemble-index i ens))
    (syntaxp (not (equal x i)))
    (<= (ensemble-index i ens) (co-located-right-index x ens)))
   (and (equal (LeftPerimeterGuess i ens)
               (LeftPerimeterGuess x ens))
        (equal (LeftCountGuess i ens)
               (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens))))))
  :hints (("Goal" :use all-co-located-left-coordinated-p-necc)))

(defthm all-co-located-left-coordinated-p-implies-linear
  (implies
   (and
    (all-co-located-left-coordinated-p ens)
    (<= (co-located-left-index x ens) (ensemble-index i ens))
    (<= (ensemble-index i ens) (co-located-right-index x ens)))
   (<= 0 (- (LeftCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
  :rule-classes ((:linear :trigger-terms ((LeftCountGuess x ens))))
  :hints (("Goal" :use all-co-located-left-coordinated-p-necc)))

(defun-sk all-co-located-right-coordinated-p (ens)
  (declare (xargs :guard (ens-p ens)))
  (forall (i x)
    (let ((i (nfix i))
          (x (nfix x)))
      (implies
       (and
        (<= (co-located-left-index x ens) (ensemble-index i ens))
        (<= (ensemble-index i ens) (co-located-right-index x ens)))
       (right-coordinated-pair-p i x ens)))))

(in-theory (disable all-co-located-right-coordinated-p))

(defthm all-co-located-right-coordinated-p-implies-rw
  (implies
   (and
    (all-co-located-right-coordinated-p ens)
    (<= (co-located-left-index x ens) (ensemble-index i ens))
    (syntaxp (not (equal x i)))
    (<= (ensemble-index i ens) (co-located-right-index x ens)))
   (and (equal (RightPerimeterGuess i ens)
               (RightPerimeterGuess x ens))
        (equal (RightCountGuess i ens)
               (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens))))))
  :hints (("goal" :use all-co-located-right-coordinated-p-necc)))

(defthm all-co-located-right-coordinated-p-implies-linear
  (implies
   (and
    (all-co-located-right-coordinated-p ens)
    (<= (co-located-left-index x ens) (ensemble-index i ens))
    (<= (ensemble-index i ens) (co-located-right-index x ens)))
   (<= 0 (+ (RightCountGuess x ens) (- (ensemble-index x ens) (ensemble-index i ens)))))
  :rule-classes ((:linear :trigger-terms ((RightCountGuess x ens))))
  :hints (("goal" :use all-co-located-right-coordinated-p-necc)))

(defthm co-located-right-index-share
  (equal (co-located-right-index x (share ens))
         (co-located-right-index x ens))
  :hints (("Goal" :induct (co-located-right-index x ens)
           :in-theory (enable co-located-right-index)
           :do-not-induct t
           :expand ((co-located-right-index x (share ens))
                    (co-located-right-index x ens)))))

(defthm co-located-left-index-share
  (equal (co-located-left-index x (share ens))
         (co-located-left-index x ens))
  :hints (("Goal" :induct (co-located-left-index x ens)
           :do-not-induct t
           :in-theory (enable co-located-left-index)
           :expand ((co-located-left-index x (share ens))
                    (co-located-left-index x ens)))))

(defthm all-coordinated-share
  (implies
   (weak-uav-state-p ens)
   (and (all-co-located-left-coordinated-p (share ens))
        (all-co-located-right-coordinated-p (share ens))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable equal-current-location-implies-bounds
                              co-located-index-within-range-alt
                              )
           :expand ((all-co-located-left-coordinated-p (share ens))
                    (all-co-located-right-coordinated-p (share ens))))))

;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =
;;
;; flip
;;
;; = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = = =

(def::un flip-direction (dx lx ls xx rs rx)
  (declare (xargs :fty ((sign rational rational rational rational rational) sign)))
  (if (< dx 0)
      (if (not (equal xx lx)) dx
        (if (< ls xx) dx
          (- dx)))
    (if (not (equal xx rx)) dx
      (if (< xx rs) dx
        (- dx)))))
  
(def::und flip-uav (left uav right)
  (declare (xargs :fty ((uav uav uav) uav)))
  (b* (((UAV* :xx xx :dx dx) uav)
       ((UAV* :xx lx) left)
       ((UAV* :xx rx) right)
       (ls (UAV->left-moving-uav-split-location uav))
       (rs (UAV->right-moving-uav-split-location uav)))
    (UAV* uav :dx (flip-direction dx lx ls xx rs rx))))

#|

;; I don't know if this is useful .. just seemed interesting.

(def::und max-escort-index (s)
  (declare (xargs :fty ((pos) nat)))
  (1- s))

(defthm max-escort-index-upper-bound
  (< (max-escort-index s) (pos-fix s))
  :hints (("Goal" :in-theory (enable max-escort-index)))
  :rule-classes ((:linear :trigger-terms ((max-escort-index s)))))

(in-theory (disable pos-equiv))

(def::und escort-index (i s)
  (declare (xargs :fty ((nat pos) nat)))
  (min (nfix i) (max-escort-index s)))

(defthm escort-index-lower-bound
  (<= 0 (escort-index i s))
  :rule-classes (:linear))

(defthm escort-index-upper-bound
  (< (escort-index i s) (pos-fix s))
  :hints (("Goal" :in-theory (enable escort-index)))
  :rule-classes ((:linear :trigger-terms ((escort-index i s)))))

(defthm escort-index-upper-bound-2
  (<= (escort-index i s) (max-escort-index s))
  :hints (("Goal" :in-theory (enable escort-index)))
  :rule-classes ((:linear :trigger-terms ((escort-index i s)))))

(def::un escort->uav (i e)
  (declare (xargs :fty ((nat escort) uav)))
  (b* ((i  (escort-index i (escort->size e)))
       ((escort* :LP LP :LC LC :XX XX :DX DX :RC RC :RP RP) e))
    (UAV! :LP LP :LC (+ LC i) :XX XX :DX DX :RC (+ RC (max-escort-index (escort->size e)) (- i)) :RP RP)))

(defthm escort->uav-get-escort
  (equal (escort->uav i (get-escort x ens))
         (get-uav (+ (escort-index i (- (escort-right-index x ens)
                                        (escort-left-index x ens)))
                     (escort-left-index x ens))
                  ens))
  :otf-flg t
  :hints (("Goal" :do-not-induct t
           :in-theory (enable get-escort))))
|#
                     

;; (if (< dx 0)
;;     (if (not (equal xx lx)) uav
;;       (if (<  xx) uav
;;         (UAV* uav :dx (- dx))))
;;   (if (not (equal xx rx)) uav
;;     (if (< xx (UAV->right-moving-uav-split-location uav)) uav
;;       (UAV* uav :dx (- dx)))))))

(def::und left-boundary-uav ()
  (declare (xargs :fty (() uav)))
  (UAV! :LP (ActualLeftPerimeter) :LC 0 :dx 1 :xx (ActualLeftPerimeter) :RC 0 :RP (ActualRightPerimeter)))

(def::und right-boundary-uav ()
  (declare (xargs :fty (() uav)))
  (UAV! :LP (ActualLeftPerimeter) :LC 0 :dx -1 :xx (ActualRightPerimeter) :RC 0 :RP (ActualRightPerimeter)))

(def::und wrapped-get-uav (x max uav)
  (declare (xargs :fty ((int nat uav) uav)))
  (if (< x 0) (left-boundary-uav)
    (if (< max x) (right-boundary-uav)
      uav)))

(def::un flip-uav-index (x ens)
  (declare (xargs :fty ((nat ens) uav)))
  (let ((x (ensemble-index x ens)))
    (let ((left  (wrapped-get-uav (1- x) (max-ens-index ens) (get-uav (1- x) ens)))
          (right (wrapped-get-uav (1+ x) (max-ens-index ens) (get-uav (1+ x) ens))))
      (flip-uav left (get-uav x ens) right))))

(defthm flip-uav-index-ensemble-index
  (equal (flip-uav-index (ensemble-index x ens) ens)
         (flip-uav-index x ens))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((flip-uav-index (ensemble-index x ens) ens)))))

(defthmd flip-uav-index-ensemble-index!
  (implies
   (syntaxp (symbolp x))
   (equal (flip-uav-index x ens)
          (flip-uav-index (ensemble-index x ens) ens))))

(theory-invariant (incompatible (:rewrite flip-uav-index-ensemble-index!)
                                (:rewrite flip-uav-index-ensemble-index)))

(in-theory (disable flip-uav-index))

(defthm ensemble-index-equiv-flip-uav-index-congruence
  (implies
   (equal (ensemble-index x ens)
          (ensemble-index y ens))
   (iff (equal (flip-uav-index x ens)
               (flip-uav-index y ens)) t))
  :hints (("Goal" :in-theory (e/d (flip-uav-index-ensemble-index!)
                                  (flip-uav-index-ensemble-index))))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :corollary
                  (implies
                   (equal (ensemble-index x ens)
                          (ensemble-index y ens))
                   (equal (flip-uav-index x ens)
                          (flip-uav-index y ens)))
                  :trigger-terms ((flip-uav-index x ens)))))

(def::un flip-all-uav (x ens)
  (declare (xargs :fty ((nat ens) ens)
                  :measure (ensemble-index x ens)))
  (let ((x (ensemble-index x ens)))
    (if (zp x) (set-uav x (flip-uav-index x ens) ens)
      (set-uav x (flip-uav-index x ens)
               (flip-all-uav (1- x) ens)))))

(defthm len-equiv-flip-all-uav
  (len-equiv (flip-all-uav x ens) ens))

(defthm all-uavs-flip-all-uav
  (implies
   (and
    (all-uavs ens)
    (consp (double-rewrite ens)))
   (all-uavs (flip-all-uav x ens))))

(defthm get-uav-flip-all-uav
  (equal (get-uav i (flip-all-uav x ens))
         (if (not (consp ens)) (get-uav i ens)
           (let ((x (ensemble-index x ens))
                 (i (ensemble-index i ens)))
             (if (< x i) (get-uav i ens)
               (flip-uav-index i ens))))))

(def::un flip (ens)
  (declare (xargs :fty ((ens) ens)))
  (flip-all-uav (max-ens-index ens) ens))

(defthm len-equiv-flip
  (len-equiv (flip ens) ens))

(defthm all-uavs-flip
  (implies
   (and
    (all-uavs ens)
    (consp (double-rewrite ens)))
   (all-uavs (flip ens))))

(defthm get-uav-flip
  (equal (get-uav i (flip ens))
         (if (not (consp ens)) (get-uav i ens)
           (flip-uav-index i ens)))
  :hints (("Goal" :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-2))))

(in-theory (disable flip))

(defthm flip-primitive-accessor-invariants
  (and (equal (LEFTPERIMETERGUESS x (flip ens))
              (LEFTPERIMETERGUESS x ens))
       (equal (RightPERIMETERGUESS x (flip ens))
              (RightPERIMETERGUESS x ens))
       (equal (LEFTCOUNTGUESS x (flip ens))
              (LEFTCOUNTGUESS x  ens))
       (equal (RightCOUNTGUESS x (flip ens))
              (RightCOUNTGUESS x  ens))
       (equal (current-location x (flip ens))
              (current-location x  ens))
       )
  :hints (("Goal" :in-theory (e/d (LEFTPERIMETERGUESS
                                   LEFTCOUNTGUESS
                                   RIGHTPERIMETERGUESS
                                   RIGHTCOUNTGUESS
                                   current-location
                                   FLIP-UAV-INDEX
                                   flip-uav
                                   )
                                  (UAV->xx-to-current-location
                                   UAV->LC-TO-LEFTCOUNTGUESS
                                   UAV->RC-TO-RIGHTCOUNTGUESS
                                   UAV->LP-TO-LEFTPERIMETERGUESS
                                   UAV->RP-TO-RIGHTPERIMETERGUESS
                                   
                                   )
                                  ))))

(def::und left-moving-sign-p (s)
  (declare (xargs :fty ((sign) bool)))
  (< s 0))

(def::und left-moving-bool-to-sign (x)
  (declare (xargs :fty ((bool) sign)))
  (if x -1 1))

(defthm left-moving-bool-to-sign-left-moving-sign-p
  (implies
   (sign-p x)
   (equal (left-moving-bool-to-sign (left-moving-sign-p x))
          x))
  :hints (("Goal" :in-theory (enable left-moving-sign-p left-moving-bool-to-sign))))

(def::und left-moving-uav-p (uav)
  (declare (xargs :fty ((uav) bool)))
  (left-moving-sign-p (UAV->dx uav)))

(defthmd left-moving-p-definition
  (equal (left-moving-p x ens)
         (left-moving-uav-p (get-uav x ens)))
  :hints (("Goal" :in-theory (e/d (left-moving-p
                                   left-moving-uav-p
                                   left-moving-sign-p)
                                  (EQUAL-UAV->DX--1-TO-LEFT-MOVING
                                   UAV->DX-TO-RIGHT-MOVING-P
                                   UAV->DX-TO-NOT-LEFT-MOVING-P
                                   UAV->DX-TO-LEFT-MOVING-P)))))

(def::un left-moving-p-flip (x ens)
  (declare (xargs :fty ((nat ens) bool)))
  (if (not (consp ens)) (left-moving-p x ens)
    (let ((x (ensemble-index x ens)))
      (let ((left  (wrapped-get-uav (1- x) (max-ens-index ens) (get-uav (1- x) ens)))
            (uav   (get-uav x ens))
            (right (wrapped-get-uav (1+ x) (max-ens-index ens) (get-uav (1+ x) ens))))
        (b* (((UAV* :xx xx :dx dx) uav)
             ((UAV* :xx lx) left)
             ((UAV* :xx rx) right)
             (ls (UAV->left-moving-uav-split-location uav))
             (rs (UAV->right-moving-uav-split-location uav)))
          (left-moving-sign-p (flip-direction dx lx ls xx rs rx)))))))

(defthm left-moving-p-flip-ensemble-index
  (equal (LEFT-MOVING-P-FLIP (ENSEMBLE-INDEX X ENS) ens)
         (LEFT-MOVING-P-FLIP x ens))
  :hints (("Goal" :expand ((LEFT-MOVING-P-FLIP (ENSEMBLE-INDEX X ENS) ens)
                           (LEFT-MOVING-P-FLIP x ens)))))

(defthm flip-primitive-variant
  (equal (left-moving-p x (flip ens))
         (left-moving-p-flip x ens))
  :hints (("Goal" :in-theory (enable FLIP-UAV-INDEX
                                     LEFT-MOVING-UAV-P
                                     FLIP-UAV
                                     left-moving-p-definition))))

(in-theory (disable left-moving-p-flip))

;; Now we will probably need to prove a bunch of
;; things about this new function.  At a minimum
;; we know that it is bounded by co-located.

(def::un escort-left-index-flip (x ens)
  (declare (xargs :fty ((nat ens) nat)
                  :measure (ensemble-index x ens)))
  (let ((x (ensemble-index x ens)))
    (if (zp x) x
      (let* ((lx  (current-location (1- x) ens))
             (rx  (current-location x ens))
             (ldx (left-moving-p-flip (1- x) ens))
             (rdx (left-moving-p-flip x ens)))
        (if (not (equal lx rx)) x
          (if (not (equal ldx rdx)) x
            (escort-left-index-flip (1- x) ens)))))))

(defthm escort-left-index-flip-lower-bound
  (<= 0 (escort-left-index-flip x ens))
  :rule-classes ((:linear :trigger-terms ((escort-left-index-flip x ens)))))

(defthm escort-left-index-flip-upper-bound
  (<= (escort-left-index-flip x ens) (ensemble-index x ens))
  :rule-classes ((:linear :trigger-terms ((escort-left-index-flip x ens)))))

(defthm co-located-left-index-bounds-escort-left-index-flip
  (<= (co-located-left-index x ens) (escort-left-index-flip x ens))
  :hints (("Goal" :in-theory (enable CO-LOCATED-LEFT-INDEX)))
  :rule-classes (:linear (:forward-chaining :trigger-terms ((escort-left-index-flip x ens)))))

(defthm ensemble-index-p-escort-left-index-flip
  (ensemble-index-p (escort-left-index-flip x ens) ens)
  :hints (("Goal" :in-theory (enable ensemble-index-p))))

(def::un escort-right-index-flip (x ens)
  (declare (xargs :fty ((nat ens) nat)
                  :hints (("Goal" :in-theory (enable ensemble-index max-ens-index)))
                  :measure (- (max-ens-index ens) (ensemble-index x ens))))
  (let ((x (ensemble-index x ens)))
    (if (<= (max-ens-index ens) x) (max-ens-index ens)
      (let* ((rx  (current-location (1+ x) ens))
             (lx  (current-location x ens))
             (rdx (left-moving-p-flip (1+ x) ens))
             (ldx (left-moving-p-flip x ens)))
        (if (not (equal lx rx)) x
          (if (not (equal ldx rdx)) x
            (escort-right-index-flip (1+ x) ens)))))))

(defthm escort-right-index-flip-lower-bound
  (<= (ensemble-index x ens) (escort-right-index-flip x ens))
  :hints (("Goal" :in-theory (enable STRICTLY-LESS-MEANS-REDUCE-2)))
  :rule-classes ((:linear :trigger-terms ((escort-right-index-flip x ens)))))

(defthm escort-right-index-flip-upper-bound
  (<= (escort-right-index-flip x ens) (max-ens-index ens))
  :rule-classes ((:linear :trigger-terms ((escort-right-index-flip x ens)))))

(defthm co-located-right-index-bounds-escort-right-index-flip
  (<= (escort-right-index-flip x ens) (co-located-right-index x ens))
  :hints (("Goal" :in-theory (enable CO-LOCATED-right-INDEX)))
  :rule-classes (:linear (:forward-chaining :trigger-terms ((escort-right-index-flip x ens)))))

(defthm ensemble-index-p-escort-right-index-flip
  (ensemble-index-p (escort-right-index-flip x ens) ens)
  :hints (("Goal" :in-theory (enable ensemble-index-p))))

(defthm co-located-also-bound-the-opposite
  (and (<= (escort-left-index-flip x ens) (co-located-right-index x ens))
       (<= (co-located-left-index x ens) (escort-right-index-flip x ens)))
  :rule-classes (:linear
                 (:forward-chaining :trigger-terms ((escort-left-index-flip x ens)
                                                    (escort-right-index-flip x ens)))))

(encapsulate
    ()

  (local
   (def::un alt-escort-left-index (x ens)
     (declare (xargs :fty ((nat ens) nat)
                     :measure (ensemble-index x ens)))
     (let ((x (ensemble-index x ens)))
       (if (zp x) x
         (let* ((lx  (current-location (1- x) ens))
                (rx  (current-location x ens))
                (ldx (left-moving-p (1- x) ens))
                (rdx (left-moving-p x ens)))
           (if (not (equal lx rx)) x
             (if (not (equal ldx rdx)) x
               (alt-escort-left-index (1- x) ens))))))))

  (local
   (defthmd alt-escort-left-index-definition
     (equal (escort-left-index x ens)
            (alt-escort-left-index x ens))
     :hints (("Goal" :induct (escort-left-index x ens)
              :in-theory (enable EQUAL-SIGN-REDUCTION escort-left-index)
              :expand ((alt-escort-left-index x ens))))))

  (local
   (def::un alt-escort-right-index (x ens)
     (declare (xargs :fty ((nat ens) nat)
                     :hints (("Goal" :in-theory (enable ensemble-index max-ens-index)))
                     :measure (- (max-ens-index ens) (ensemble-index x ens))))
     (let ((x (ensemble-index x ens)))
       (if (<= (max-ens-index ens) x) (max-ens-index ens)
         (let* ((rx  (current-location (1+ x) ens))
                (lx  (current-location x ens))
                (rdx (left-moving-p (1+ x) ens))
                (ldx (left-moving-p x ens)))
           (if (not (equal lx rx)) x
             (if (not (equal ldx rdx)) x
               (alt-escort-right-index (1+ x) ens))))))))
   
  
  (local
   (defthmd alt-escort-right-index-definition
     (equal (escort-right-index x ens)
            (alt-escort-right-index x ens))
     :hints (("Goal" :induct (escort-right-index x ens)
              :in-theory (enable EQUAL-SIGN-REDUCTION escort-right-index)
              :expand ((alt-escort-right-index x ens))))))
  
  (defthm escort-left-index-flip-variant
    (equal (escort-left-index x (flip ens))
           (escort-left-index-flip x ens))
    :hints (("Goal" :induct (escort-left-index-flip x ens)
             :do-not-induct t
             :in-theory (enable alt-escort-left-index-definition
                                EQUAL-SIGN-REDUCTION)
             :expand ((ALT-ESCORT-LEFT-INDEX X (FLIP ENS))
                      (ESCORT-LEFT-INDEX-FLIP X ENS)))))
  
  (defthm escort-right-index-flip-variant
    (equal (escort-right-index x (flip ens))
           (escort-right-index-flip x ens))
    :hints (("Goal" :induct (escort-right-index-flip x ens)
             :do-not-induct t
             :in-theory (enable alt-escort-right-index-definition
                                EQUAL-SIGN-REDUCTION)
             :expand ((ALT-ESCORT-right-INDEX X (FLIP ENS))
                      (ESCORT-right-INDEX-FLIP X ENS)))))
  
  )

(in-theory (disable (flip)))

(defthm get-uav-not-consp
  (implies
   (and
    (not (consp ens))
    (syntaxp (not (quotep a))))
   (equal (get-uav a ens)
          (get-uav 0 ens)))
  :hints (("Goal" :in-theory (enable get-uav))))

(defthm leftperimeterguess-not-consp
  (implies
   (and
    (not (consp ens))
    (syntaxp (not (quotep a))))
   (and (equal (leftperimeterguess a ens)
               (leftperimeterguess 0 ens))
        (equal (leftcountguess a ens)
               (leftcountguess 0 ens))
        (equal (rightperimeterguess a ens)
               (rightperimeterguess 0 ens))
        (equal (rightcountguess a ens)
               (rightcountguess 0 ens))))
  :hints (("Goal" :in-theory (e/d (leftperimeterguess
                                   leftcountguess
                                   rightperimeterguess
                                   rightcountguess)
                                  (UAV->LP-TO-LEFTPERIMETERGUESS
                                   UAV->LC-TO-LEFTCOUNTGUESS
                                   UAV->RP-TO-RIGHTPERIMETERGUESS
                                   UAV->RC-TO-RIGHTCOUNTGUESS
                                   )))))

(defthm get-escort-not-consp
  (implies
   (and
    (not (consp ens))
    (syntaxp (not (quotep x))))
   (equal (get-escort x ens)
          (get-escort 0 ens)))
  :hints (("Goal" :in-theory (enable get-escort))))

(in-theory (disable flip-direction))

(def::un get-escort-flip (x ens)
  (declare (xargs :fty ((nat ens) ens)))
  (B* ((XUAV (GET-UAV X ENS))
       ((UAV* :XX XX) XUAV)
       (LEFT (ESCORT-LEFT-INDEX-FLIP X ENS))
       (LUAV (GET-UAV LEFT ENS))
       ((UAV* :LP LP :LC LC) LUAV)
       (RIGHT (ESCORT-RIGHT-INDEX-FLIP X ENS))
       (RUAV (GET-UAV RIGHT ENS))
       ((UAV* :RC RC :RP RP) RUAV))
      (ESCORT! :LP LP
               :LC LC
               :LI LEFT
               :XX XX
               :DX (left-moving-bool-to-sign (left-moving-p-flip x ens))
               :RI RIGHT
               :RC RC
               :RP RP)))


(encapsulate
    ()

  (local  (include-book "arithmetic-5/top" :dir :system))

  (local
   (set-default-hints '((nonlinearp-default-hint
                         stable-under-simplificationp
                         hist pspv))))

  (def::un leftmost-left-of-left-segment-boundary-index (index ss diff)
    (declare (xargs :measure (nfix (- (ifix index) (floor (rfix diff) (prat-fix ss))))
                    :hints (("Goal" :in-theory (enable nfix)))))
    (let ((index (ifix index))
          (ss    (prat-fix ss))
          (diff  (rfix diff)))
      (if (< (* (1- index) ss) diff) index
        (leftmost-left-of-left-segment-boundary-index (1- index) ss diff))))

  (defthm leftmost-left-of-left-segment-boundary-index-upper-bound
    (<= (leftmost-left-of-left-segment-boundary-index index ss diff) (ifix index))
    :rule-classes ((:linear :trigger-terms ((leftmost-left-of-left-segment-boundary-index index ss diff)))))
  
  (defthm leftmost-left-of-left-segment-boundary-index-property
    (implies
     (<= (rfix diff) (* (ifix index) (prat-fix ss)))
     (<= (rfix diff) (* (leftmost-left-of-left-segment-boundary-index index ss diff) (prat-fix ss))))
    :rule-classes ((:linear :trigger-terms ((leftmost-left-of-left-segment-boundary-index index ss diff)))))
  
  (defthm leftmost-left-of-left-segment-boundary-index-is-the-smallest
    (implies
     (and
      (<= (rfix diff) (* (ifix index) (prat-fix ss)))
      (<= (rfix diff) (* (ifix small) (prat-fix ss))))
     (<= (leftmost-left-of-left-segment-boundary-index index ss diff) (ifix small))))
  
  (defthm positive-diff-implies-positive-index
    (implies
     (and
      (<= 0 (rfix diff))
      (<= 0 (ifix index)))
     (<= 0 (leftmost-left-of-left-segment-boundary-index index ss diff)))
    :rule-classes (:linear))
  
  )

(encapsulate
    ()

  (local  (include-book "arithmetic-5/top" :dir :system))

  (local
   (set-default-hints '((nonlinearp-default-hint
                         stable-under-simplificationp
                         hist pspv))))

  (def::un rightmost-right-of-right-segment-boundary-index (index ss diff)
    (declare (xargs :measure (nfix (- (floor (rfix diff) (prat-fix ss)) (ifix index)))
                    :hints (("Goal" :in-theory (enable nfix)))))
    (let ((index (ifix index))
          (ss    (prat-fix ss))
          (diff  (rfix diff)))
      (if (< diff (* (1+ index) ss)) index
        (rightmost-right-of-right-segment-boundary-index (1+ index) ss diff))))

  (defthm rightmost-right-of-right-segment-boundary-index-lower-bound
    (<= (ifix index) (rightmost-right-of-right-segment-boundary-index index ss diff))
    :rule-classes ((:linear :trigger-terms ((rightmost-right-of-right-segment-boundary-index index ss diff)))))
  
  (defthm rightmost-right-of-right-segment-boundary-index-property
    (implies
     (<= (* (ifix index) (prat-fix ss)) (rfix diff))
     (<= (* (rightmost-right-of-right-segment-boundary-index index ss diff) (prat-fix ss)) (rfix diff)))
    :rule-classes ((:linear :trigger-terms ((rightmost-right-of-right-segment-boundary-index index ss diff)))))
  
  (defthm rightmost-right-of-right-segment-boundary-index-is-the-largest
    (implies
     (and
      (<= (* (ifix index) (prat-fix ss)) (rfix diff))
      (<= (* (ifix small) (prat-fix ss)) (rfix diff)))
     (<= (ifix small) (rightmost-right-of-right-segment-boundary-index index ss diff))))
  
  ;; We may need an upper bound on this ..
  
  )

(defund indexed-seg-size (x ss)
  (* (ifix x) (rfix ss)))

(defun Escort->left-moving-uav-split-location (x esc)
  (- (Escort->left-moving-escort-split-location esc) (indexed-seg-size (- (Escort->Ri esc) (nfix x)) (Escort->seg-size esc))))

(defun Escort->right-moving-uav-split-location (x esc)
  (+ (Escort->right-moving-escort-split-location esc) (indexed-seg-size (- (nfix x) (Escort->Li esc)) (Escort->seg-size esc))))

(defmacro update-lc (&key (li '0) (lc '0) (lii '0))
  `(+ ,Lc (- ,Li) ,Lii))

(defmacro update-rc (&key (ri '0) (rc '0) (rii '0))
  `(+ ,Rc (- ,Rii) ,Ri))

(defun Escort->left-moving-p (esc)
  (< (Escort->dx esc) 0))

(defun Escort->right-moving-p (esc)
  (not (Escort->left-moving-p esc)))

;;
;; This still needs to reflect the behavior when we reach a perimeter.
;;
(defun escort-flip-spec (x left esc right)
  (let ((Li (Escort->Li left))
        (Lc (Escort->LC left))
        (Rc (Escort->RC right))
        (Ri (Escort->Ri right)))
    (cond
     ((equal (Escort->xx esc) (ActualLeftPerimeter))
      (Escort* esc
               :Li Li
               :LC Lc
               :dx +1
               :RC RC
               :Ri Ri))
     ((equal (Escort->xx esc) (ActualRightPerimeter))
      (Escort* esc
               :Li Li
               :LC Lc
               :dx -1
               :RC RC
               :Ri Ri))
     ((<= (Escort->xx esc) (Escort->left-moving-uav-split-location x esc))
      (cond
       ((< Li x)
        ;; We have a left neighbor
        (let ((Lii (max (leftmost-left-of-left-segment-boundary-index x (Escort->seg-size esc) (- (Escort->xx esc) (Escort->Lp esc)))
                        (Escort->Li left)))
              (Rii (Escort->Ri right))
              (dx +1))
          (Escort* esc
                   :Li Lii
                   :LC (update-lc :Li Li :LC LC :Lii Lii)
                   :dx dx
                   :RC (update-rc :Ri Ri :RC RC :Rii Rii)
                   :Ri Rii)))
       ((Escort->right-moving-p esc)
        (let ((Lii x)
              (Rii (Escort->Ri right))
              (dx (Escort->dx esc)))
          (Escort* esc
                   :Li Lii
                   :LC (update-lc :Li Li :LC LC :Lii Lii)
                   :dx dx
                   :RC (update-rc :Ri Ri :RC RC :Rii Rii)
                   :Ri Rii)))
       (t
        (let ((Lii x)
              (Rii x)
              (dx (Escort->dx esc)))
          (Escort* esc
                   :Li Lii
                   :LC (update-lc :Li Li :LC LC :Lii Lii)
                   :dx dx
                   :RC (update-rc :Ri Ri :RC RC :Rii Rii)
                   :Ri Rii)))))
     ((<= (Escort->right-moving-uav-split-location x esc) (Escort->xx esc))
      (cond
       ((< x Ri)
        ;; We have a right neighbor
        (let ((Rii (min (rightmost-right-of-right-segment-boundary-index x (Escort->seg-size esc) (- (Escort->xx esc) (Escort->Lp esc)))
                        (Escort->Ri right)))
              (Lii (Escort->Li left))
              (dx -1))
          (Escort* esc
                   :Li Lii
                   :LC (update-lc :Li Li :LC LC :Lii Lii)
                   :dx dx
                   :RC (update-rc :Ri Ri :RC RC :Rii Rii)
                   :Ri Rii)))
       ((Escort->left-moving-p esc)
        (let ((Rii x)
              (Lii (Escort->Li left))
              (dx (Escort->dx esc)))
          (Escort* esc
                   :Li Lii
                   :LC (update-lc :Li Li :LC LC :Lii Lii)
                   :dx dx
                   :RC (update-rc :Ri Ri :RC RC :Rii Rii)
                   :Ri Rii)))
       (t
        (let ((Lii x)
              (Rii x)
              (dx (Escort->dx esc)))
          (Escort* esc
                   :Li Lii
                   :LC (update-lc :Li Li :LC LC :Lii Lii)
                   :dx dx
                   :RC (update-rc :Ri Ri :RC RC :Rii Rii)
                   :Ri Rii)))))
     (t
      ;;
      ;; don't flip .. add yourself to left or right escort depending on
      ;; direction.
      ;;
      (cond
       ((Escort->left-moving-p esc)
        (let ((Rii x)
              (Lii (if (<= x Li) x
                     (max (leftmost-left-of-left-segment-boundary-index (1- x) (Escort->seg-size esc) (- (Escort->xx esc) (Escort->Lp esc)))
                          (Escort->Li left))))
              (dx (Escort->dx esc)))
          (Escort* esc
                   :Li Lii
                   :LC (update-lc :Li Li :LC LC :Lii Lii)
                   :dx dx
                   :RC (update-rc :Ri Ri :RC RC :Rii Rii)
                   :Ri Rii)))
       (t
        (let ((Lii x)
              (Rii (if (<= Ri x) x
                     (min (rightmost-right-of-right-segment-boundary-index (1+ x) (Escort->seg-size esc) (- (Escort->xx esc) (Escort->Lp esc)))
                          (Escort->Ri right))))
              (dx (Escort->dx esc)))
          (Escort* esc
                   :Li Lii
                   :LC (update-lc :Li Li :LC LC :Lii Lii)
                   :dx dx
                   :RC (update-rc :Ri Ri :RC RC :Rii Rii)
                   :Ri Rii))))))))

(with-arithmetic
 (defthm combine-two
   (equal (+ (LEFT-MOVING-UAV-SPLIT-OFFSET-FN x ss) (- (indexed-seg-size y ss)))
          (LEFT-MOVING-UAV-SPLIT-OFFSET-FN (- (ifix x) (ifix y)) ss))
   :hints (("Goal" :in-theory (enable LEFT-MOVING-UAV-SPLIT-OFFSET-FN
                                      indexed-seg-size))))
 )

(defthm LEFT-MOVING-UAV-SPLIT-OFFSET-FN-zero
  (equal (LEFT-MOVING-UAV-SPLIT-OFFSET-FN 0 ss) 0)
  :hints (("Goal" :in-theory (enable LEFT-MOVING-UAV-SPLIT-OFFSET-FN))))

(defthm non-zero-offset
  (implies
   (and
    (< 0 (rfix ss))
    (< 0 (ifix x)))
   (< 0 (LEFT-MOVING-UAV-SPLIT-OFFSET-FN x ss)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable LEFT-MOVING-UAV-SPLIT-OFFSET-FN))))
  
(defthm double-negation-really?
  (equal (- (- x)) (fix x)))

(defthm less-than-negative
  (implies
   (rationalp x)
   (iff (< (- x) 0)
        (< 0 x))))

(defthm equal-negative-x-1
  (iff (equal (- x) 1)
       (equal (fix x) -1)))

(defthm plus-negative-associate-1
  (equal (+ a (+ (- a) b))
         (fix b)))

#+dag
(dag)
(defthm current-location-co-located-left-index
  (equal (current-location (co-located-left-index x ens) ens)
         (current-location x ens))
  :hints (("Goal" :use (:instance co-located-left-index-fundamental-property
                                  (i x)
                                  (k (co-located-left-index x ens))))))

(defthm current-location-co-located-right-index
  (equal (current-location (co-located-right-index x ens) ens)
         (current-location x ens))
  :hints (("Goal" :use (:instance co-located-right-index-fundamental-property
                                  (i x)
                                  (k (co-located-right-index x ens))))))


(def::un shared-state-p (x y ens)
  (declare (xargs :fty ((nat nat ens) bool)))
  (implies
   (and
    (<= (co-located-left-index x ens) (ensemble-index y ens))
    (<= (ensemble-index y ens) (co-located-right-index x ens)))
   (and
    (equal (leftperimeterguess y ens)
           (leftperimeterguess x ens))
    (equal (rightperimeterguess y ens)
           (rightperimeterguess x ens))
    (<= (- (ensemble-index y ens) (co-located-left-index y ens)) (leftcountguess y ens))
    (<= (- (co-located-right-index y ens) (ensemble-index y ens)) (rightcountguess y ens))
    (implies
     (and
      (uav-state-p ens)
      (equal (current-location y ens) (ActualRightPerimeter)))
     (and
      (equal (rightperimeterguess y ens) (ActualRightPerimeter))
      (equal (rightcountguess y ens) (- (max-ens-index ens) (ensemble-index y ens)))
      (< (leftperimeterguess y ens) (ActualRightPerimeter))))
    (implies
     (and
      (uav-state-p ens)
      (equal (current-location y ens) (ActualLeftPerimeter)))
     (and
      (equal (leftperimeterguess y ens) (ActualLeftPerimeter))
      (equal (leftcountguess y ens) (ensemble-index y ens))
      (< (ActualLeftPerimeter) (rightperimeterguess y ens))))
    ;; x ... y
    ;; 
    (equal (leftcountguess y ens)
           (+ (leftcountguess x ens) (- (ensemble-index y ens)
                                        (ensemble-index x ens))))
    (equal (rightcountguess y ens)
           (+ (rightcountguess x ens) (- (ensemble-index x ens)
                                         (ensemble-index y ens)))))))

(defthm current-location-on-rightperimeter
  (implies
   (and
    (uav-state-p ens)
    (EQUAL (CURRENT-LOCATION X ENS)
           (ACTUALRIGHTPERIMETER))
    (<= (ensemble-index x ens) (ensemble-index y ens)))
   (equal (current-location y ens)
          (ACTUALRIGHTPERIMETER)))
  :hints (("Goal" :use ((:instance ALL-CURRENT-LOCATIONS-BOUNDED-P-IMPLICATION
                                   (x y))
                        current-location-order))))

(defthm current-location-on-leftperimeter
  (implies
   (and
    (uav-state-p ens)
    (EQUAL (CURRENT-LOCATION y ENS)
           (ACTUALleftPERIMETER))
    (<= (ensemble-index x ens) (ensemble-index y ens)))
   (equal (current-location x ens)
          (ACTUALleftPERIMETER)))
  :hints (("Goal" :use (ALL-CURRENT-LOCATIONS-BOUNDED-P-IMPLICATION
                        current-location-order))))

(with-arithmetic
 (defthmd shared-state-p-share
   (implies
    (uav-state-p ens)
    (shared-state-p x y (share ens)))
   :hints (("Goal" :in-theory (enable CO-LOCATED-INDEX-INVARIANT
                                      CO-LOCATED-INDEX-INVARIANT-forward
                                      pinched-index-is-co-located
                                      )))))

(defun-sk shared-state (ens)
  (declare (xargs :guard t))
  (forall (x y) (shared-state-p (nfix x) (nfix y) (ens-fix ens)))
  :strengthen t)

(encapsulate
    ()

  (local (in-theory (disable shared-state-p)))
  
  (quant::congruence shared-state  (ens)
    (forall (x y) (shared-state-p (nfix x) (nfix y) (ens-fix ens)))
    :congruences ((ens ens-equiv)))
  
  )

(in-theory (disable shared-state))

(defthm shared-state-leftcountguess-lower-bound
  (implies
   (shared-state ens)
   (<= (- (ensemble-index y ens) (co-located-left-index y ens)) (leftcountguess y ens)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance shared-state-necc
                                  (x y)))))

(defthm shared-state-rightcountguess-lower-bound
  (implies
   (shared-state ens)
   (<= (- (co-located-right-index y ens) (ensemble-index y ens)) (rightcountguess y ens)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance shared-state-necc
                                  (x y)))))
    
(defthm shared-state-coodination-right
  (implies
   (and
    (shared-state ens)
    (uav-state-p ens)
    (equal (current-location y ens) (ActualRightPerimeter)))
   (and
    (equal (rightperimeterguess y ens) (ActualRightPerimeter))
    (equal (rightcountguess y ens) (- (max-ens-index ens) (ensemble-index y ens)))
    ))
  :hints (("Goal" :use (:instance shared-state-necc
                                  (x y)
                                  (y y)))))

(defthm shared-state-coodination-right-linear
  (implies
   (and
    (shared-state ens)
    (uav-state-p ens)
    (equal (current-location y ens) (ActualRightPerimeter)))
   (< (leftperimeterguess y ens) (ActualRightPerimeter)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance shared-state-necc
                                  (x y)
                                  (y y)))))

(defthm shared-state-coodination-left
  (implies
   (and
    (shared-state ens)
    (uav-state-p ens)
    (equal (current-location y ens) (ActualleftPerimeter)))
   (and
    (equal (leftperimeterguess y ens) (ActualleftPerimeter))
    (equal (leftcountguess y ens) (ensemble-index y ens))))
  :hints (("Goal" :use (:instance shared-state-necc
                                  (x y)
                                  (y y)))))

(defthm shared-state-coodination-left-linear
  (implies
   (and
    (shared-state ens)
    (uav-state-p ens)
    (equal (current-location y ens) (ActualleftPerimeter)))
   (< (ActualleftPerimeter) (rightperimeterguess y ens) ))
  :rule-classes :linear
  :hints (("Goal" :use (:instance shared-state-necc
                                  (x y)
                                  (y y)))))

(def::linear shared-state-left-perimeter-guess
  (implies
   (and
    (shared-state ens)
    (syntaxp (not (equal x y)))
    (<= (co-located-left-index x ens) (ensemble-index y ens))
    (<= (ensemble-index y ens) (co-located-right-index x ens)))
   (equal (LEFTPERIMETERGUESS Y ENS)
          (LEFTPERIMETERGUESS X ENS)))
  ;;:trigger-terms ((LEFTPERIMETERGUESS X ENS))
  :hints (("Goal" :use shared-state-necc)))

(defthm LEFTPERIMETERGUESS-ESCORT-LEFT-INDEX-FLIP 
  (IMPLIES (SHARED-STATE ENS)
           (EQUAL (LEFTPERIMETERGUESS (ESCORT-left-INDEX-FLIP X ENS) ENS)
                  (leftPERIMETERGUESS X ENS))))

(defthm LEFTPERIMETERGUESS-ESCORT-right-INDEX-FLIP 
  (IMPLIES (SHARED-STATE ENS)
           (EQUAL (LEFTPERIMETERGUESS (ESCORT-right-INDEX-FLIP X ENS) ENS)
                  (leftPERIMETERGUESS X ENS))))

(defthm LEFTPERIMETERGUESS-CO-LOCATED-LEFT-INDEX 
  (IMPLIES (SHARED-STATE ENS)
           (EQUAL (LEFTPERIMETERGUESS (co-located-left-index X ENS) ENS)
                  (leftPERIMETERGUESS X ENS))))

(defthm LEFTPERIMETERGUESS-co-located-right-index 
  (IMPLIES (SHARED-STATE ENS)
           (EQUAL (LEFTPERIMETERGUESS (co-located-right-index X ENS) ENS)
                  (leftPERIMETERGUESS X ENS))))

(in-theory (disable shared-state-left-perimeter-guess))

(def::linear shared-state-right-perimeter-guess
  (implies
   (and
    (syntaxp (not (equal x y)))
    (shared-state ens)
    (<= (co-located-left-index x ens) (ensemble-index y ens))
    (<= (ensemble-index y ens) (co-located-right-index x ens)))
   (equal (rightPERIMETERGUESS Y ENS)
          (rightPERIMETERGUESS X ENS)))
  ;;:trigger-terms ((rightPERIMETERGUESS X ENS))
  :hints (("Goal" :use shared-state-necc)))

(defthm RIGHTPERIMETERGUESS-ESCORT-LEFT-INDEX-FLIP 
  (IMPLIES (SHARED-STATE ENS)
           (EQUAL (RIGHTPERIMETERGUESS (ESCORT-left-INDEX-FLIP X ENS) ENS)
                  (rightPERIMETERGUESS X ENS))))

(defthm RIGHTPERIMETERGUESS-ESCORT-right-INDEX-FLIP 
  (IMPLIES (SHARED-STATE ENS)
           (EQUAL (RIGHTPERIMETERGUESS (ESCORT-right-INDEX-FLIP X ENS) ENS)
                  (rightPERIMETERGUESS X ENS))))

(defthm RIGHTPERIMETERGUESS-CO-LOCATED-LEFT-INDEX 
  (IMPLIES (SHARED-STATE ENS)
           (EQUAL (RIGHTPERIMETERGUESS (co-located-left-index X ENS) ENS)
                  (rightPERIMETERGUESS X ENS))))

(defthm RIGHTPERIMETERGUESS-co-located-right-index 
  (IMPLIES (SHARED-STATE ENS)
           (EQUAL (RIGHTPERIMETERGUESS (co-located-right-index X ENS) ENS)
                  (rightPERIMETERGUESS X ENS))))

(in-theory (disable shared-state-right-perimeter-guess))

(defthmd shared-state-means-coordinated-leftcountguess
  (implies
   (and
    (shared-state ens)
    (<= (co-located-left-index x ens) (ensemble-index y ens))
    (<= (ensemble-index y ens) (co-located-right-index x ens)))
   (equal (leftcountguess y ens)
          (+ (leftcountguess x ens)
             (- (ensemble-index y ens) 
                (ensemble-index x ens)))))
  :rule-classes (:linear)
  :hints (("Goal" :use shared-state-necc)))

(defthmd shared-state-means-coordinated-rightcountguess
  (implies
   (and
    (shared-state ens)
    (<= (co-located-left-index x ens) (ensemble-index y ens))
    (<= (ensemble-index y ens) (co-located-right-index x ens)))
   (equal (rightcountguess y ens)
          (+ (rightcountguess x ens)
             (- (ensemble-index x ens)
                (ensemble-index y ens) 
                ))))
  :rule-classes (:linear)
  :hints (("Goal" :use shared-state-necc)))

(defthm leftcountguess-co-located-left-index
  (implies
   (shared-state ens)
   (equal (leftcountguess (co-located-left-index x ens) ens)
          (+ (leftcountguess x ens)
             (- (co-located-left-index x ens)
                (ensemble-index x ens)))))
  :hints (("Goal" :use (:instance shared-state-means-coordinated-leftcountguess
                                  (y (co-located-left-index x ens))))))

(defthm leftcountguess-ESCORT-LEFT-INDEX-FLIP
  (implies
   (shared-state ens)
   (equal (leftcountguess (ESCORT-LEFT-INDEX-FLIP X ENS) ens)
          (+ (leftcountguess x ens)
             (- (ESCORT-LEFT-INDEX-FLIP X ENS)
                (ensemble-index x ens)))))
  :hints (("Goal" :use (:instance shared-state-means-coordinated-leftcountguess
                                  (y (ESCORT-LEFT-INDEX-FLIP X ENS))))))

(defthm rightcountguess-co-located-right-index
  (implies
   (shared-state ens)
   (equal (rightcountguess (co-located-right-index x ens) ens)
          (+ (rightcountguess x ens)
             (- (ensemble-index x ens)
                (co-located-right-index x ens)))))
  :hints (("Goal" :use (:instance shared-state-means-coordinated-rightcountguess
                                  (y (co-located-right-index x ens))))))

(defthm plus-one-still-lte-co-located
  (implies
   (and
    (< (ensemble-index x ens) (max-ens-index ens))
    (equal (current-location (+ 1 (ensemble-index x ens)) ens)
           (current-location x ens)))
   (<= (+ 1 (ensemble-index x ens)) (co-located-right-index x ens)))
  :rule-classes (:forward-chaining :linear))

(defthm minus-one-still-lte-co-located
  (implies
   (and
    (< 0 (ensemble-index x ens))
    (equal (current-location (+ -1 (ensemble-index x ens)) ens)
           (current-location x ens)))
   (<= (co-located-left-index x ens) (+ -1 (ensemble-index x ens))))
  :rule-classes (:forward-chaining :linear))

(defthm plus-one-right-perimeter-guess
  (implies
   (and
    (shared-state ens)
    (< (ensemble-index x ens) (max-ens-index ens))
    (equal (current-location (+ 1 (ensemble-index x ens)) ens)
           (current-location x ens)))
   (equal (rightperimeterguess (+ 1 (ensemble-index x ens)) ens)
          (rightperimeterguess x ens)))
  :hints (("Goal" :in-theory (enable shared-state-right-perimeter-guess))))


(defthm plus-one-left-perimeter-guess
  (implies
   (and
    (shared-state ens)
    (< (ensemble-index x ens) (max-ens-index ens))
    (equal (current-location (+ 1 (ensemble-index x ens)) ens)
           (current-location x ens)))
   (equal (leftperimeterguess (+ 1 (ensemble-index x ens)) ens)
          (leftperimeterguess x ens)))
  :hints (("Goal" :in-theory (enable shared-state-left-perimeter-guess))))

(defthm minus-one-right-perimeter-guess
  (implies
   (and
    (shared-state ens)
    (< 0 (ensemble-index x ens))
    (equal (current-location (+ -1 (ensemble-index x ens)) ens)
           (current-location x ens)))
   (equal (rightperimeterguess (+ -1 (ensemble-index x ens)) ens)
          (rightperimeterguess x ens)))
  :hints (("Goal" :in-theory (enable shared-state-right-perimeter-guess))))

(defthm minus-one-left-perimeter-guess
  (implies
   (and
    (shared-state ens)
    (< 0 (ensemble-index x ens))
    (equal (current-location (+ -1 (ensemble-index x ens)) ens)
           (current-location x ens)))
   (equal (leftperimeterguess (+ -1 (ensemble-index x ens)) ens)
          (leftperimeterguess x ens)))
  :hints (("Goal" :in-theory (enable shared-state-left-perimeter-guess))))

(defthm plus-one-right-count-guess
  (implies
   (and
    (shared-state ens)
    (< (ensemble-index x ens) (max-ens-index ens))
    (equal (current-location (+ 1 (ensemble-index x ens)) ens)
           (current-location x ens)))
   (equal (rightcountguess (+ 1 (ensemble-index x ens)) ens)
          (+ -1 (rightcountguess x ens))))
  :hints (("Goal" :use (:instance shared-state-means-coordinated-rightcountguess
                                  (y (+ 1 (ensemble-index x ens)))))))

(defthm plus-one-left-count-guess
  (implies
   (and
    (shared-state ens)
    (< (ensemble-index x ens) (max-ens-index ens))
    (equal (current-location (+ 1 (ensemble-index x ens)) ens)
           (current-location x ens)))
   (equal (leftcountguess (+ 1 (ensemble-index x ens)) ens)
          (+ 1 (leftcountguess x ens))))
  :hints (("Goal" :use (:instance shared-state-means-coordinated-leftcountguess
                                  (y (+ 1 (ensemble-index x ens)))))))


(defthm minus-one-right-count-guess
  (implies
   (and
    (shared-state ens)
    (< 0 (ensemble-index x ens))
    (equal (current-location (+ -1 (ensemble-index x ens)) ens)
           (current-location x ens)))
   (equal (rightcountguess (+ -1 (ensemble-index x ens)) ens)
          (+ 1 (rightcountguess x ens))))
  :hints (("Goal" :use (:instance shared-state-means-coordinated-rightcountguess
                                  (y (+ -1 (ensemble-index x ens)))))))

(defthm minus-one-left-count-guess
  (implies
   (and
    (shared-state ens)
    (< 0 (ensemble-index x ens))
    (equal (current-location (+ -1 (ensemble-index x ens)) ens)
           (current-location x ens)))
   (equal (leftcountguess (+ -1 (ensemble-index x ens)) ens)
          (+ -1 (leftcountguess x ens))))
  :hints (("Goal" :use (:instance shared-state-means-coordinated-leftcountguess
                                  (y (+ -1 (ensemble-index x ens)))))))

(defthm positive-ifix
  (implies
   (< 0 (ifix x))
   (and
    (integerp x)
    (< 0 x)))
  :hints (("Goal" :in-theory (enable ifix)))
  :rule-classes (:forward-chaining))

(defrefinement rational-equiv prat-equiv
  :hints (("Goal" :in-theory (enable rfix prat-fix
                                     rational-equiv
                                     prat-equiv))))

(defthm combine-split-offset-fn
  (implies
   (rationalp ss)
   (equal (+ ss (LEFT-MOVING-UAV-SPLIT-OFFSET-FN x ss))
          (LEFT-MOVING-UAV-SPLIT-OFFSET-FN (1+ (ifix x)) ss)))
  :hints (("Goal" :in-theory (enable LEFT-MOVING-UAV-SPLIT-OFFSET-FN))))
         
(with-arithmetic
 (defthm left-moving-uav-split-offset-fn-seg-zie-fn2-1
   (implies
    (< 0 (ifix x))
    (equal (LEFT-MOVING-UAV-SPLIT-OFFSET-FN x (SEG-SIZE-FN2 x d))
           (prat-fix d)))
   :hints (("Goal" :in-theory (enable SEG-SIZE-FN2 LEFT-MOVING-UAV-SPLIT-OFFSET-FN)))))

(with-arithmetic
 (defthm left-moving-uav-split-offset-fn-seg-zie-fn2-linear
   (implies
    (and
     (< 0 (ifix x))
     (<= (ifix y) (ifix x)))
    (<= (LEFT-MOVING-UAV-SPLIT-OFFSET-FN y (SEG-SIZE-FN2 x d))
        (prat-fix d)))
   :rule-classes ((:linear :trigger-terms ((LEFT-MOVING-UAV-SPLIT-OFFSET-FN y (SEG-SIZE-FN2 x d)))))
   :hints (("Goal" :in-theory (enable SEG-SIZE-FN2 LEFT-MOVING-UAV-SPLIT-OFFSET-FN)))))


(defthm positive-offset-fn
  (implies
   (and
    (<= 0 (ifix x))
    (<= 0 (rfix ss)))
   (<= 0 (LEFT-MOVING-UAV-SPLIT-OFFSET-FN x ss)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable LEFT-MOVING-UAV-SPLIT-OFFSET-FN )))) 
                              
(with-arithmetic
 (defthm equal-left-moving-uav-split-offset-fn-denominator
   (implies
    (and
     (rationalp D)
     (< 0 D))
    (iff (EQUAL (LEFT-MOVING-UAV-SPLIT-OFFSET-FN X (SEG-SIZE-FN2 N D)) D)
         (equal (ifix X) (pos-fix N))))
   :hints (("Goal" :in-theory (enable SEG-SIZE-FN2 LEFT-MOVING-UAV-SPLIT-OFFSET-FN))))
 )
       
(defthm shared-state-rightperimeter-bounds-split-locations
  (implies
   (and
    (uav-state-p ens)
    (shared-state ens)
    (EQUAL (CURRENT-LOCATION X ENS)
           (ACTUALrightPERIMETER)))
   (and (<= (right-moving-uav-split-location x ens) (actualrightperimeter))
        (< (left-moving-uav-split-location x ens) (actualrightperimeter))))
  :hints (("Goal" :in-theory (e/d (UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION
                                   share-uav
                                   uav->seg-size
                                   LEFT-MOVING-UAV-SPLIT-LOCATION
                                   right-moving-uav-split-location)
                                  (LEFT-MOVING-UAV-SPLIT-OFFSET-FN
                                   UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-TO-LEFT-MOVING-UAV-SPLIT-LOCATION
                                   UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION-TO-RIGHT-MOVING-UAV-SPLIT-LOCATION)))))

(defthm shared-state-leftperimeter-bounds-split-locations
  (implies
   (and
    (uav-state-p ens)
    (shared-state ens)
    (EQUAL (CURRENT-LOCATION X ENS)
           (ACTUALleftPERIMETER)))
   (and (< (actualleftperimeter) (right-moving-uav-split-location x ens) )
        (<= (actualleftperimeter) (left-moving-uav-split-location x ens) )))
  :hints (("Goal" :in-theory (e/d (UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION
                                   UAV->left-MOVING-UAV-SPLIT-LOCATION
                                   share-uav
                                   uav->seg-size
                                   LEFT-MOVING-UAV-SPLIT-LOCATION
                                   right-moving-uav-split-location)
                                  (LEFT-MOVING-UAV-SPLIT-OFFSET-FN
                                   UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-TO-LEFT-MOVING-UAV-SPLIT-LOCATION
                                   UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION-TO-RIGHT-MOVING-UAV-SPLIT-LOCATION)))))

(in-theory (disable right-moving-uav-split-location left-moving-uav-split-location))

(defthm ensemble-index-p-plus-ensemble-index
  (implies
   (and
    (natp n)
    (<= (+ N (ENSEMBLE-INDEX X ENS)) (MAX-ENS-INDEX ENS)))
   (ensemble-index-p (+ N (ENSEMBLE-INDEX X ENS)) ens))
  :hints (("Goal" :in-theory (enable  ensemble-index-p))))


(in-theory (disable ESCORT-RIGHT-INDEX-FLIP ESCORT-LEFT-INDEX-FLIP))

;; DAG - try to push this back
(in-theory (disable NFIX-IFIX-EQUIV))
           
(encapsulate
    ()

  (local (in-theory (disable DEGENERATE-ENSEMBLE-INDEX
                             CO-LOCATED-LEFT-RIGHT-INDEX-BOUNDS-RIGHT
                             CO-LOCATED-LEFT-RIGHT-INDEX-BOUNDS-LEFT
                             CO-LOCATED-LEFT-INDEX-ON-LEFT-PERIMETER
                             CO-LOCATED-RIGHT-INDEX-ON-RIGHT-PERIMETER
                             CURRENT-LOCATION-ENSEMBLE-INDEX-EQUIV-REWRITE
                             )))

  (defthm shared-state-left-moving-p-flip-rightperimeter
    (implies
     (AND (EQUAL (CURRENT-LOCATION X ENS)
                 (ACTUALrightPERIMETER))
          (< (ensemble-index x ens) (max-ens-index ens))
          (UAV-STATE-P ENS)
          (SHARED-STATE ENS))
     (equal (LEFT-MOVING-P-FLIP (+ 1 (ensemble-index x ens)) ens)
            (left-moving-p-flip x ens)))
    :hints (("Goal" :in-theory (e/d (right-boundary-uav
                                     wrapped-get-uav
                                     left-moving-sign-p
                                     flip-direction
                                     LEFT-MOVING-P-FLIP)
                                    ()))))
  
  (defthm shared-state-left-moving-p-flip-rightperimeter-minus
    (implies
     (AND (EQUAL (CURRENT-LOCATION (+ -1 (ensemble-index x ens)) ENS)
                 (ACTUALrightPERIMETER))
          (< 0 (ensemble-index x ens))
          (UAV-STATE-P ENS)
          (SHARED-STATE ENS))
     (equal (LEFT-MOVING-P-FLIP (+ -1 (ensemble-index x ens)) ens)
            (left-moving-p-flip x ens)))
    :hints (("Goal" :in-theory (e/d (right-boundary-uav
                                     wrapped-get-uav
                                     left-moving-sign-p
                                     flip-direction
                                     LEFT-MOVING-P-FLIP)
                                    ()))))

  (defthm shared-state-left-moving-p-flip-leftperimeter
    (implies
     (AND (EQUAL (CURRENT-LOCATION X ENS)
                 (ACTUALleftPERIMETER))
          (< 0 (ensemble-index x ens))
          (UAV-STATE-P ENS)
          (SHARED-STATE ENS))
     (equal (LEFT-MOVING-P-FLIP (+ -1 (ensemble-index x ens)) ens)
            (left-moving-p-flip x ens)))
    :hints (("Goal" :in-theory (e/d (left-boundary-uav
                                     wrapped-get-uav
                                     left-moving-sign-p
                                     flip-direction
                                     LEFT-MOVING-P-FLIP)
                                    ()))))
    
  (defthm shared-state-left-moving-p-flip-leftperimeter-plus
    (implies
     (AND (EQUAL (CURRENT-LOCATION (+ 1 (ensemble-index x ens)) ENS)
                 (ACTUALleftPERIMETER))
          (< (ensemble-index x ens) (max-ens-index ens))
          (UAV-STATE-P ENS)
          (SHARED-STATE ENS))
     (equal (LEFT-MOVING-P-FLIP (+ 1 (ensemble-index x ens)) ens)
            (left-moving-p-flip x ens)))
    :hints (("Goal" :in-theory (e/d (left-boundary-uav
                                     wrapped-get-uav
                                     left-moving-sign-p
                                     flip-direction
                                     LEFT-MOVING-P-FLIP)
                                    ()))))

  )
  
(defthm escort-right-index-flip-is-CO-LOCATED-RIGHT-INDEX-when-on-right-perimeter
   (IMPLIES (AND (EQUAL (CURRENT-LOCATION X ENS)
                        (ACTUALrightPERIMETER))
                 (UAV-STATE-P ENS)
                 (SHARED-STATE ENS))
            (EQUAL (ESCORT-RIGHT-INDEX-FLIP X ENS)
                   (CO-LOCATED-RIGHT-INDEX X ENS)))
   :hints (("Goal" :in-theory (enable ESCORT-RIGHT-INDEX-FLIP
                                      CO-LOCATED-RIGHT-INDEX)
            :induct (ESCORT-RIGHT-INDEX-FLIP X ENS)
            :do-not-induct t)))

(defthm escort-left-index-flip-is-CO-LOCATED-left-INDEX-when-on-right-perimeter
   (IMPLIES (AND (EQUAL (CURRENT-LOCATION X ENS)
                        (ACTUALrightPERIMETER))
                 (UAV-STATE-P ENS)
                 (SHARED-STATE ENS))
            (EQUAL (ESCORT-left-INDEX-FLIP X ENS)
                   (CO-LOCATED-left-INDEX X ENS)))
   :hints (("Goal" :in-theory (enable ESCORT-left-INDEX-FLIP
                                      CO-LOCATED-left-INDEX)
            :induct (ESCORT-left-INDEX-FLIP X ENS)
            :expand (CO-LOCATED-LEFT-INDEX X ENS)
            :do-not-induct t)))

(defthm escort-left-index-flip-is-CO-LOCATED-left-INDEX-when-on-left-perimeter
   (IMPLIES (AND (EQUAL (CURRENT-LOCATION X ENS)
                        (ACTUALleftPERIMETER))
                 (UAV-STATE-P ENS)
                 (SHARED-STATE ENS))
            (EQUAL (ESCORT-left-INDEX-FLIP X ENS)
                   (CO-LOCATED-left-INDEX X ENS)))
   :hints (("Goal" :in-theory (enable ESCORT-left-INDEX-FLIP
                                      CO-LOCATED-left-INDEX)
            :induct (ESCORT-left-INDEX-FLIP X ENS)
            :do-not-induct t)))

(defthm escort-right-index-flip-is-CO-LOCATED-right-INDEX-when-on-left-perimeter
   (IMPLIES (AND (EQUAL (CURRENT-LOCATION X ENS)
                        (ACTUALleftPERIMETER))
                 (UAV-STATE-P ENS)
                 (SHARED-STATE ENS))
            (EQUAL (ESCORT-right-INDEX-FLIP X ENS)
                   (CO-LOCATED-right-INDEX X ENS)))
   :hints (("Goal" :in-theory (enable ESCORT-right-INDEX-FLIP
                                      CO-LOCATED-right-INDEX)
            :induct (ESCORT-right-INDEX-FLIP X ENS)
            :expand (ESCORT-right-INDEX-FLIP X ENS)
            :do-not-induct t)))

;; (in-theory (disable LEFT-MOVING-UAV-SPLIT-OFFSET-FN))

;; (defthm joseph
;;   (implies
;;    (EQUAL (ENSEMBLE-INDEX 1 ENS) 0)
;;    (equal (ESCORT-RIGHT-INDEX-FLIP 1 ENS) 0))
;;   :hints (("Goal" :expand (ESCORT-RIGHT-INDEX-FLIP 1 ENS)
;;            :in-theory (enable MAX-ENS-INDEX
;;                               ENSEMBLE-INDEX))))

;; (in-theory (disable  RIGHTPERIMETERGUESS-co-located-linear))
;; (in-theory (disable  LEFTPERIMETERGUESS-co-located-linear))

;; ;; (defthm LEFTPERIMETERGUESS-on-left-perimeter
;; ;;   (implies
;; ;;    (AND (UAV-STATE-P ENS)
;; ;;         (SHARED-STATE ENS)
;; ;;         (EQUAL (CURRENT-LOCATION X ENS)
;; ;;                (ACTUALLEFTPERIMETER)))
;; ;;    (EQUAL (LEFTPERIMETERGUESS X ENS)
;; ;;           (LEFTPERIMETERGUESS 0 ENS)))
;; ;;   :hints (("Goal" :use LEFTPERIMETERGUESS-co-located-left
;; ;;            :in-theory (disable LEFTPERIMETERGUESS-co-located-left)))
;; ;;   :rule-classes ((:linear :trigger-terms ((LEFTPERIMETERGUESS X ENS)))))

;; ;; (defthm RIGHTPERIMETERGUESS-on-left-perimeter
;; ;;   (implies
;; ;;    (AND (UAV-STATE-P ENS)
;; ;;         (SHARED-STATE ENS)
;; ;;         (EQUAL (CURRENT-LOCATION X ENS)
;; ;;                (ACTUALLEFTPERIMETER)))
;; ;;    (EQUAL (RIGHTPERIMETERGUESS X ENS)
;; ;;           (RIGHTPERIMETERGUESS 0 ENS)))
;; ;;   :hints (("Goal" :use (:instance RIGHTPERIMETERGUESS-co-located-linear
;; ;;                                   (y 0))))
;; ;;   :rule-classes ((:linear :trigger-terms ((LEFTPERIMETERGUESS X ENS)))))

;; (skip-proofs
;;  (defthm CO-LOCATED-RIGHT-INDEX-is-max-ens-index-on-right-perimeter
;;    (implies
;;     (and
;;      (UAV-STATE-P ENS)
;;      (EQUAL (CURRENT-LOCATION X ENS)
;;             (ACTUALrightPERIMETER)))
;;     (equal (CO-LOCATED-RIGHT-INDEX X ENS)
;;            (max-ens-index ens)))))

;; (defthm LEFTPERIMETERGUESS-on-right-perimeter
;;   (implies
;;    (AND (UAV-STATE-P ENS)
;;         (SHARED-STATE ENS)
;;         (EQUAL (CURRENT-LOCATION X ENS)
;;                (ACTUALrightPERIMETER)))
;;    (EQUAL (LEFTPERIMETERGUESS X ENS)
;;           (LEFTPERIMETERGUESS (MAX-ENS-INDEX ENS) ENS)))
;;   :hints (("Goal" :use (:instance LEFTPERIMETERGUESS-co-located-linear
;;                                   (y (MAX-ENS-INDEX ENS)))
;;            :in-theory (disable LEFTPERIMETERGUESS-co-located-left)))
;;   :rule-classes ((:linear :trigger-terms ((LEFTPERIMETERGUESS X ENS)))
;;                  (:forward-chaining :trigger-terms ((LEFTPERIMETERGUESS X ENS)))))

;; (defthm RIGHTPERIMETERGUESS-on-right-perimeter
;;   (implies
;;    (AND (UAV-STATE-P ENS)
;;         (SHARED-STATE ENS)
;;         (EQUAL (CURRENT-LOCATION X ENS)
;;                (ACTUALrightPERIMETER)))
;;    (EQUAL (RIGHTPERIMETERGUESS X ENS)
;;           (RIGHTPERIMETERGUESS (MAX-ENS-INDEX ENS) ENS)))
;;   :hints (("Goal" :use (:instance RIGHTPERIMETERGUESS-co-located-linear
;;                                   (y (MAX-ENS-INDEX ENS)))))
;;   :rule-classes ((:forward-chaining :trigger-terms ((RIGHTPERIMETERGUESS X ENS)))
;;                  (:linear :trigger-terms ((RIGHTPERIMETERGUESS X ENS)))))

;; (skip-proofs
;;  (defthm escort-right-index-flip-is-CO-LOCATED-RIGHT-INDEX-when-on-left-perimeter
;;    (IMPLIES (AND (EQUAL (CURRENT-LOCATION X ENS)
;;                         (ACTUALLEFTPERIMETER))
;;                  (UAV-STATE-P ENS)
;;                  (SHARED-STATE ENS))
;;             (EQUAL (ESCORT-RIGHT-INDEX-FLIP X ENS)
;;                    (CO-LOCATED-RIGHT-INDEX X ENS)))))

;; (skip-proofs
;;  (defthm escort-left-index-flip-is-CO-LOCATED-LEFT-INDEX-when-on-left-perimeter
;;    (IMPLIES (AND (EQUAL (CURRENT-LOCATION X ENS)
;;                         (ACTUALLEFTPERIMETER))
;;                  (UAV-STATE-P ENS)
;;                  (SHARED-STATE ENS))
;;             (EQUAL (ESCORT-LEFT-INDEX-FLIP X ENS)
;;                    (CO-LOCATED-LEFT-INDEX X ENS)))))

;; (skip-proofs
;;  (defthm escort-right-index-flip-is-CO-LOCATED-RIGHT-INDEX-when-on-right-perimeter
;;    (IMPLIES (AND (EQUAL (CURRENT-LOCATION X ENS)
;;                         (ACTUALrightPERIMETER))
;;                  (UAV-STATE-P ENS)
;;                  (SHARED-STATE ENS))
;;             (EQUAL (ESCORT-RIGHT-INDEX-FLIP X ENS)
;;                    (CO-LOCATED-RIGHT-INDEX X ENS)))))

;; (skip-proofs
;;  (defthm escort-left-index-flip-is-CO-LOCATED-LEFT-INDEX-when-on-right-perimeter
;;    (IMPLIES (AND (EQUAL (CURRENT-LOCATION X ENS)
;;                         (ACTUALrightPERIMETER))
;;                  (UAV-STATE-P ENS)
;;                  (SHARED-STATE ENS))
;;             (EQUAL (ESCORT-LEFT-INDEX-FLIP X ENS)
;;                    (CO-LOCATED-LEFT-INDEX X ENS)))))

;; (defthm ensemble-index-len-ens
;;   (equal (ENSEMBLE-INDEX (LEN ENS) ENS)
;;          (max-ens-index ens))
;;   :hints (("Goal" :in-theory (enable max-ens-index ENSEMBLE-INDEX))))

;; (defthm current-location-0
;;   (implies
;;    (and
;;     (syntaxp (not (quotep x)))
;;     (equal (ENSEMBLE-INDEX X ENS) 0))
;;    (equal (CURRENT-LOCATION X ENS)
;;           (CURRENT-LOCATION 0 ENS))))

;; (skip-proofs
;;  (defthm zooie-1
;;    (implies
;;     (and
;;      (shared-state ens)
;;      (EQUAL (CURRENT-LOCATION X ENS)
;;             (ACTUALRIGHTPERIMETER)))
;;     (and
;;      (equal (RIGHTPERIMETERGUESS x ENS)
;;             (ACTUALRIGHTPERIMETER))
;;      (equal (RIGHTCOUNTGUESS x ENS)
;;             (- (max-ens-index ens) (ensemble-index x ens)))))))


;; (skip-proofs
;;  (defthm zooie-2
;;    (implies
;;     (and
;;      (uav-state-p ens)
;;      (shared-state ens)
;;      (EQUAL (CURRENT-LOCATION X ENS)
;;             (ACTUALRIGHTPERIMETER)))
;;     (and
;;      (equal (RIGHTPERIMETERGUESS (MAX-ENS-INDEX ENS) ENS)
;;             (ACTUALRIGHTPERIMETER))))))

;; dag
;; (skip-proofs
;;  (defthm alpha-brave-right
;;    (implies
;;     (and
;;      (shared-state ens)
;;      (EQUAL (CURRENT-LOCATION X ENS)
;;             (ACTUALRIGHTPERIMETER)))
;;     (< (leftPERIMETERGUESS x ENS) (rightPERIMETERGUESS x ENS)))
;;    :rule-classes (:linear)))

;; (skip-proofs
;;  (defthm alpha-brave-left
;;    (implies
;;     (and
;;      (shared-state ens)
;;      (EQUAL (CURRENT-LOCATION X ENS)
;;             (ACTUALRIGHTPERIMETER)))
;;     (< (leftPERIMETERGUESS x ENS) (rightPERIMETERGUESS x ENS)))
;;    :rule-classes (:linear)))

;; (defthm prat-fix-ifix
;;   (equal (prat-fix (ifix x))
;;          (nfix x))
;;   :hints (("Goal" :in-theory (enable ifix prat-fix nfix))))

;; (skip-proofs
;;  (defthm zeph-0
;;    (implies
;;     (and
;;      (UAV-STATE-P ENS)
;;      (EQUAL (CURRENT-LOCATION 0 ENS)
;;             (ACTUALRIGHTPERIMETER)))
;;     (EQUAL (CURRENT-LOCATION 1 ENS)
;;            (ACTUALRIGHTPERIMETER)))))

;; (defthm al-be
;;   (implies
;;    (and
;;     (syntaxp (symbolp x))
;;     (equal (ENSEMBLE-INDEX X ENS) (MAX-ENS-INDEX ENS)))
;;    (equal (CURRENT-LOCATION X ENS)
;;           (CURRENT-LOCATION (MAX-ENS-INDEX ENS) ENS))))


;; (skip-proofs
;;  (defthm it-follows
;;    (implies
;;     (and
;;      (uav-state-p ens)
;;      (EQUAL (CURRENT-LOCATION X ENS)
;;             (ACTUALLEFTPERIMETER)))
;;     (equal (CURRENT-LOCATION 0 ENS)
;;            (ACTUALLEFTPERIMETER)))))


;; (skip-proofs
;;  (defthm bb-2
;;    (implies
;;     (and
;;      (SHARED-STATE ENS)
;;      (EQUAL (CURRENT-LOCATION X ENS)
;;             (ACTUALLEFTPERIMETER)))
;;     (and
;;      (equal (LEFTPERIMETERGUESS X ENS)
;;             (ACTUALLEFTPERIMETER))
;;      (equal (LEFTCOUNTGUESS X ENS)
;;             (ensemble-index x ens))))))

;; (skip-proofs
;;  (defthm zed-2
;;    (implies
;;     (and
;;      (uav-state-p ens)
;;      (equal (CURRENT-LOCATION X ENS)
;;             (ACTUALLEFTPERIMETER))
;;      (<= 0 (+ -1 (ENSEMBLE-INDEX X ENS))))
;;     (EQUAL (CURRENT-LOCATION (+ -1 (ENSEMBLE-INDEX X ENS)) ens)
;;            (ACTUALLEFTPERIMETER)))))

;; (skip-proofs
;;  (defthm zed-3
;;    (implies
;;     (and
;;      (uav-state-p ens)
;;      (equal (CURRENT-LOCATION X ENS)
;;             (ACTUALrightPERIMETER))
;;      (<= (+ 1 (ENSEMBLE-INDEX X ENS))
;;          (MAX-ENS-INDEX ENS)))
;;     (EQUAL (CURRENT-LOCATION (+ 1 (ENSEMBLE-INDEX X ENS)) ens)
;;            (ACTUALrightPERIMETER)))))

;; (skip-proofs
;;  (defcong ens-equiv equal (shared-state ens) 1))


;; (skip-proofs
;;  (defthm abc-1
;;    (implies
;;     (and
;;      (SHARED-STATE ENS)
;;      (equal (current-location x ens)
;;             (current-location (1+ (ensemble-index x ens)) ens)))
;;     (equal (LEFTPERIMETERGUESS (+ 1 (ENSEMBLE-INDEX X ENS)) ENS)
;;            (LEFTPERIMETERGUESS x ENS)))))

;; (skip-proofs
;;  (defthm abc-2
;;    (implies
;;     (and
;;      (SHARED-STATE ENS)
;;      (equal (current-location x ens)
;;             (current-location (1+ (ensemble-index x ens)) ens)))
;;     (and
;;      (equal (LEFTcountGuess (+ 1 (ENSEMBLE-INDEX X ENS)) ENS)
;;             (+ -1 (LEFTcountGUESS x ENS)))
;;      (equal (RIGHTcountGuess (+ 1 (ENSEMBLE-INDEX X ENS)) ENS)
;;             (+ 1 (RIGHTcountGUESS x ENS)))))))

;; #+junk
;; (defthm ESCORT-RIGHT-INDEX-FLIP-is-CO-LOCATED-RIGHT-INDEX-when-left-of-split
;;   (IMPLIES (AND (UAV-STATE-P ENS)
;;                 (SHARED-STATE ENS)
;;                 (<= (CURRENT-LOCATION X ENS)
;;                     (+ (LEFTPERIMETERGUESS X ENS)
;;                        (LEFT-MOVING-UAV-SPLIT-OFFSET-FN
;;                         (ENSEMBLE-INDEX X ENS)
;;                         (SEG-SIZE-FN2 (+ 1 (LEFTCOUNTGUESS X ENS)
;;                                          (RIGHTCOUNTGUESS X ENS))
;;                                       (+ (- (LEFTPERIMETERGUESS X ENS))
;;                                          (RIGHTPERIMETERGUESS X ENS)))))))
;;            (EQUAL (ESCORT-RIGHT-INDEX-FLIP X ENS)
;;                   (CO-LOCATED-RIGHT-INDEX X ENS)))
;;   :hints (("Goal" :induct (ESCORT-RIGHT-INDEX-FLIP X ENS)
;;            :in-theory (enable ESCORT-RIGHT-INDEX-FLIP
;;                               CO-LOCATED-RIGHT-INDEX)
;;            :do-not '(generalize fertilize)
;;            :do-not-induct t)))

;; (defthm ESCORT-RIGHT-INDEX-FLIP-is-CO-LOCATED-RIGHT-INDEX-when-left-of-split
;;   (IMPLIES (AND (UAV-STATE-P ENS)
;;                 (SHARED-STATE ENS)
;;                 (<= (CURRENT-LOCATION X ENS)
;;                     (+ (LEFTPERIMETERGUESS X ENS)
;;                        (LEFT-MOVING-UAV-SPLIT-OFFSET-FN
;;                         (LEFTCOUNTGUESS X ENS)
;;                         (SEG-SIZE-FN2 (+ 1 (LEFTCOUNTGUESS X ENS)
;;                                          (RIGHTCOUNTGUESS X ENS))
;;                                       (+ (- (LEFTPERIMETERGUESS X ENS))
;;                                          (RIGHTPERIMETERGUESS X ENS))))))
                
;;                 )
;;            (EQUAL (ESCORT-RIGHT-INDEX-FLIP X ENS)
;;                   (CO-LOCATED-RIGHT-INDEX X ENS)))
;;   :hints (("Goal" :induct (ESCORT-RIGHT-INDEX-FLIP X ENS)
;;            :in-theory (enable ESCORT-RIGHT-INDEX-FLIP
;;                               CO-LOCATED-RIGHT-INDEX)
;;            :do-not '(generalize fertilize)
;;            :do-not-induct t)))


;; (with-arithmetic
;;  (def::linear LEFT-MOVING-UAV-SPLIT-OFFSET-FN-ordering
;;    (implies
;;     (and
;;      (< 0 (rfix ss))
;;      (< (ifix x) (ifix y)))
;;     (< (LEFT-MOVING-UAV-SPLIT-OFFSET-FN x ss)
;;        (LEFT-MOVING-UAV-SPLIT-OFFSET-FN y ss)))
;;    :hints (("Goal" :in-theory (enable LEFT-MOVING-UAV-SPLIT-OFFSET-FN)))))

;; (in-theory (disable LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX))
;; (in-theory (disable rightmost-right-of-right-segment-boundary-index))

;; (defthm left-neighbor-implication
;;   (implies
;;    (< (CO-LOCATED-LEFT-INDEX X ENS)
;;       (ENSEMBLE-INDEX X ENS))
;;    (equal (CURRENT-LOCATION (+ -1 (ENSEMBLE-INDEX X ENS)) ENS)
;;           (CURRENT-LOCATION X ENS)))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :expand (CO-LOCATED-LEFT-INDEX X ENS))))

;; (skip-proofs
;;  (defthm zoomies
;;    (IMPLIES (AND (UAV-STATE-P ENS)
;;                  (SHARED-STATE ENS)
;;                  (<= (CURRENT-LOCATION X ENS)
;;                      (+ (LEFTPERIMETERGUESS X ENS)
;;                         (LEFT-MOVING-UAV-SPLIT-OFFSET-FN
;;                          (LEFTCOUNTGUESS X ENS)
;;                          (SEG-SIZE-FN2 (+ 1 (LEFTCOUNTGUESS X ENS)
;;                                           (RIGHTCOUNTGUESS X ENS))
;;                                        (+ (- (LEFTPERIMETERGUESS X ENS))
;;                                           (RIGHTPERIMETERGUESS X ENS)))))))
;;             (EQUAL (ESCORT-LEFT-INDEX-FLIP X ENS)
;;                    (LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX
;;                     (ENSEMBLE-INDEX X ENS)
;;                     (SEG-SIZE-FN2 (+ 1 (LEFTCOUNTGUESS X ENS)
;;                                      (RIGHTCOUNTGUESS X ENS))
;;                                   (+ (- (LEFTPERIMETERGUESS X ENS))
;;                                      (RIGHTPERIMETERGUESS X ENS)))
;;                     (+ (CURRENT-LOCATION X ENS)
;;                        (- (LEFTPERIMETERGUESS X ENS))))))))
   
;; (skip-proofs
;;  (defthm foo-foo
;;    (implies
;;     (SHARED-STATE ENS)
;;     (equal (LEFTPERIMETERGUESS (LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX x ss diff) ens)
;;            (LEFTPERIMETERGUESS x ens)))))


(in-theory (disable LEFT-MOVING-UAV-SPLIT-OFFSET-FN))

(with-arithmetic
 (defthm left-moving-uav-split-offset-fn-minus-indexed-seg-size
   (equal (+ (- (INDEXED-SEG-SIZE a ss)) (left-moving-uav-split-offset-fn y ss))
          (left-moving-uav-split-offset-fn (- (ifix y) (ifix a)) ss))
   :hints (("Goal" :in-theory (enable INDEXED-SEG-SIZE left-moving-uav-split-offset-fn)))))

(defthm left-to-right-split-location
  (implies
   (and
    (shared-state ens)
    (< (ensemble-index x ens) (max-ens-index ens))
    (equal (current-location x ens)
           (current-location (+ 1 (ENSEMBLE-INDEX X ENS)) ens)))
   (equal (left-MOVING-UAV-SPLIT-LOCATION (+ 1 (ENSEMBLE-INDEX X ENS)) ens)
          (right-moving-uav-split-location x ens)))
  :hints (("Goal" :in-theory (e/d (UAV->seg-size
                                   UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION
                                   UAV->LEFT-MOVING-UAV-SPLIT-LOCATION
                                   RIGHT-MOVING-UAV-SPLIT-LOCATION
                                   left-moving-uav-split-location)
                                  (UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-TO-LEFT-MOVING-UAV-SPLIT-LOCATION
                                   UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION-TO-RIGHT-MOVING-UAV-SPLIT-LOCATION)))))

(encapsulate
    ()

  (local
   (defthm left-moving-p-flip-right-neighbor
     (implies
      (and
       (uav-state-p ens)
       (shared-state ens)
       (equal (current-location (+ -1 (ENSEMBLE-INDEX X ENS)) ens)
              (CURRENT-LOCATION X ENS))
       (EQUAL (CURRENT-LOCATION X ENS)
              (CURRENT-LOCATION (+ 1 (ENSEMBLE-INDEX X ENS)) ENS))
       (< 0 (ENSEMBLE-INDEX X ENS))
       (< (ENSEMBLE-INDEX X ENS) (MAX-ENS-INDEX ENS))
       (<= (CURRENT-LOCATION X ENS) (left-moving-uav-split-location x ens)))
      (equal (LEFT-MOVING-P-FLIP (+ 1 (ENSEMBLE-INDEX X ENS)) ens)
             (LEFT-MOVING-P-FLIP X ENS)))
     :hints (("Goal" :in-theory (enable LEFT-BOUNDARY-UAV
                                        RIGHT-BOUNDARY-UAV
                                        wrapped-get-uav
                                        flip-direction
                                        left-moving-sign-p
                                        LEFT-MOVING-P-FLIP))
             )))
   
  
  (local
   (defthm escort-right-index-flip-to-co-located-right-when-left-of-split-helper
     (implies
      (and
       (uav-state-p ens)
       (shared-state ens)
       (< 0 (ensemble-index x ens))
       (equal (current-location (+ -1 (ensemble-index x ens)) ens)
              (CURRENT-LOCATION X ENS))
       (<= (CURRENT-LOCATION X ENS) (left-moving-uav-split-location x ens)))
      (EQUAL (ESCORT-RIGHT-INDEX-FLIP X ENS)
             (CO-LOCATED-RIGHT-INDEX X ENS)))
     :hints (("Goal" :in-theory (enable ESCORT-RIGHT-INDEX-FLIP
                                        CO-LOCATED-RIGHT-INDEX)))))

   (defthm escort-right-index-flip-to-co-located-right-when-left-of-split
     (implies
      (and
       (uav-state-p ens)
       (shared-state ens)
       (< (CO-LOCATED-LEFT-INDEX X ENS)
          (ENSEMBLE-INDEX X ENS))
       (<= (CURRENT-LOCATION X ENS) (left-moving-uav-split-location x ens)))
      (EQUAL (ESCORT-RIGHT-INDEX-FLIP X ENS)
             (CO-LOCATED-RIGHT-INDEX X ENS)))
     :hints (("Goal" :use escort-right-index-flip-to-co-located-right-when-left-of-split-helper
              :expand (CO-LOCATED-LEFT-INDEX X ENS))))

   )


(defthm ESCORT->right-MOVING-ESCORT-SPLIT-LOCATION-to-right-moving-uav-split-location
  (implies
   (and
    (uav-state-p ens)
    (shared-state ens))
   (equal (ESCORT->right-MOVING-ESCORT-SPLIT-LOCATION (get-escort x ens))
          (right-moving-uav-split-location (escort-left-index x ens) ens)))
  :hints (("Goal" :in-theory (e/d (GET-ESCORT
                                   UAV->SEG-SIZE
                                   escort->seg-size
                                   ESCORT->SIZE
                                   UAV->LEFT-MOVING-UAV-SPLIT-LOCATION
                                   UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION
                                   ESCORT->right-MOVING-ESCORT-SPLIT-LOCATION
                                   right-moving-uav-split-location)
                                  (UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION-TO-RIGHT-MOVING-UAV-SPLIT-LOCATION
                                   UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-TO-LEFT-MOVING-UAV-SPLIT-LOCATION)))))

(defthm ESCORT->left-MOVING-ESCORT-SPLIT-LOCATION-to-left-moving-uav-split-location
  (implies
   (and
    (uav-state-p ens)
    (shared-state ens))
   (equal (ESCORT->left-MOVING-ESCORT-SPLIT-LOCATION (get-escort x ens))
          (left-moving-uav-split-location (escort-right-index x ens) ens)))
  :hints (("Goal" :in-theory (e/d (GET-ESCORT
                                   UAV->SEG-SIZE
                                   escort->seg-size
                                   ESCORT->SIZE
                                   UAV->LEFT-MOVING-UAV-SPLIT-LOCATION
                                   UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION
                                   ESCORT->LEFT-MOVING-ESCORT-SPLIT-LOCATION
                                   ESCORT->right-MOVING-ESCORT-SPLIT-LOCATION
                                   right-moving-uav-split-location
                                   LEFT-MOVING-UAV-SPLIT-LOCATION)
                                  (UAV->RIGHT-MOVING-UAV-SPLIT-LOCATION-TO-RIGHT-MOVING-UAV-SPLIT-LOCATION
                                   UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-TO-LEFT-MOVING-UAV-SPLIT-LOCATION)))))

;; We will want a better way of doing this .. right?
;; (defthm jester
;;   (equal (+ (LEFTPERIMETERGUESS X ENS)
;;                      (LEFT-MOVING-UAV-SPLIT-OFFSET-FN
;;                           (LEFTCOUNTGUESS X ENS)
;;                           (SEG-SIZE-FN2 (+ 1 (LEFTCOUNTGUESS X ENS)
;;                                            (RIGHTCOUNTGUESS X ENS))
;;                                         (+ (- (LEFTPERIMETERGUESS X ENS))
;;                                            (RIGHTPERIMETERGUESS X ENS)))))
;;          (left-moving-uav-split-location x ens))
;;   :hints (("Goal" :in-theory (e/d (UAV->SEG-SIZE
;;                                    UAV->LEFT-MOVING-UAV-SPLIT-LOCATION
;;                                    left-moving-uav-split-location)
;;                                   (UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-TO-LEFT-MOVING-UAV-SPLIT-LOCATION)))))

(defthm escort-seg-size-to-uav-seg-size
  (implies
   (and
    (uav-state-p ens)
    (shared-state ens))
   (equal (ESCORT->SEG-SIZE (GET-ESCORT X ENS))
          (UAV->seg-size (get-uav x ens))))
  :hints (("Goal" :in-theory (enable ESCORT->SIZE ESCORT->SEG-SIZE UAV->seg-size get-escort))))

(defthm undo-2
  (implies
   (and
    (uav-state-p ens)
    (shared-state ens))
   (equal (+ (LEFT-MOVING-UAV-SPLIT-LOCATION (ESCORT-RIGHT-INDEX X ENS) ENS)
             (- (INDEXED-SEG-SIZE (+ (- (ENSEMBLE-INDEX X ENS))
                                     (ESCORT-RIGHT-INDEX X ENS))
                                  (UAV->seg-size (get-uav x ens)))))
          (LEFT-MOVING-UAV-SPLIT-LOCATION x ens)))
  :hints (("Goal" :in-theory (e/d (UAV->SEG-SIZE
                                   UAV->LEFT-MOVING-UAV-SPLIT-LOCATION
                                   LEFT-MOVING-UAV-SPLIT-LOCATION)
                                  (UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-TO-LEFT-MOVING-UAV-SPLIT-LOCATION)))))

(defthm xx-get-escort
  (equal (escort->xx (get-escort x ens))
         (current-location x ens))
  :hints (("Goal" :in-theory (enable get-escort))))

(defthm rp-get-escort
  (equal (escort->RP (get-escort x ens))
         (RIGHTPERIMETERGUESS (ESCORT-RIGHT-INDEX X ENS) ENS))
  :hints (("Goal" :in-theory (enable get-escort))))

(defthm lp-get-escort
  (equal (escort->LP (get-escort x ens))
         (leftPERIMETERGUESS (ESCORT-left-INDEX X ENS) ENS))
  :hints (("Goal" :in-theory (enable get-escort))))

(defthm lc-get-escort
  (equal (escort->LC (get-escort x ens))
         (LEFTCOUNTGUESS (ESCORT-LEFT-INDEX X ENS) ENS))
  :hints (("Goal" :in-theory (enable get-escort))))

(defthm rc-get-escort
  (equal (escort->RC (get-escort x ens))
         (RIGHTCOUNTGUESS (ESCORT-RIGHT-INDEX X ENS) ENS))
  :hints (("Goal" :in-theory (enable get-escort))))

(defthm ri-get-escort
  (equal (escort->RI (get-escort x ens))
         (ESCORT-RIGHT-INDEX X ENS))
  :hints (("Goal" :in-theory (enable get-escort))))

(defthm li-get-escort
  (equal (escort->LI (get-escort x ens))
         (ESCORT-lEFT-INDEX X ENS))
  :hints (("Goal" :in-theory (enable get-escort))))

(defthm dx-get-escort
  (equal (ESCORT->DX (GET-ESCORT X ENS))
         (UAV->DX (GET-UAV X ENS)))
  :hints (("Goal" :in-theory (enable get-escort))))

(defthm one-off
  (implies
   (< (CO-LOCATED-LEFT-INDEX X ENS)
      (ENSEMBLE-INDEX X ENS))
   (equal (CURRENT-LOCATION (+ -1 (ENSEMBLE-INDEX X ENS)) ENS)
          (CURRENT-LOCATION X ENS)))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints (("Goal" :expand (CO-LOCATED-LEFT-INDEX X ENS))))

(defthm equal-equal-1
  (iff (equal (+ x y) (+ x z))
       (equal (fix y) (fix z))))
              
(defthm equal-equal-2
  (iff (equal (+ x z) (+ y x))
       (equal (fix z) (fix y))))
              

#|
(in-theory (disable LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX))
(in-theory (disable ESCORT-LEFT-INDEX-FLIP ESCORT-right-INDEX-FLIP))

(skip-proofs
 (with-arithmetic
  (defthm stellar-1
   (implies
    (and
     (uav-state-p ens)
     (shared-state ens)
     (<= (CURRENT-LOCATION X ENS)
         (LEFT-MOVING-UAV-SPLIT-LOCATION X ENS)))
    (equal (ESCORT-LEFT-INDEX-FLIP X ENS)
           (LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX
            (ENSEMBLE-INDEX X ENS)
            (UAV->SEG-SIZE (GET-UAV X ENS))
            (+ (CURRENT-LOCATION X ENS)
               (- (LEFTPERIMETERGUESS X ENS))))))
   :hints (("Goal" :induct(ESCORT-LEFT-INDEX-FLIP X ENS)
            :do-not-induct t
            :in-theory (e/d (LEFT-MOVING-UAV-SPLIT-OFFSET-FN
                             UAV->LEFT-MOVING-UAV-SPLIT-LOCATION
                             LEFT-MOVING-UAV-SPLIT-LOCATION
                             ESCORT-LEFT-INDEX-FLIP
                             LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX)
                            (UAV->LEFT-MOVING-UAV-SPLIT-LOCATION-TO-LEFT-MOVING-UAV-SPLIT-LOCATION)
                            )))))
 )

(skip-proofs
 (defthm gulp
   (equal (LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX x ss 0)
          0)))

(skip-proofs
 (defthm ensemble-index-p-LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX
   (implies
    (ensemble-index-p x ens)
    (ensemble-index-p (LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX x ss 0) ens))))

(skip-proofs
 (defthm alpha
   (equal (leftcountguess (LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX x ss diff) ens)
          (+ (leftcountguess x ens)
             (- (LEFTMOST-LEFT-OF-LEFT-SEGMENT-BOUNDARY-INDEX x ss diff)
                (ensemble-index x ens))))))

;;(with-arithmetic
 (defthm get-escort-flip-is-correct
  (implies
   (and
    (uav-state-p ens)
    (shared-state ens))
   (equal (get-escort-flip x ens)
          (escort-flip-spec (ensemble-index x ens)
                            (get-escort (co-located-left-index x ens) ens)
                            (get-escort x ens)
                            (get-escort (co-located-right-index x ens) ens))))
  :hints (("Goal" :in-theory (enable ;;ESCORT->SIZE
                              ;;ESCORT->SEG-SIZE
                              ;;ESCORT->LEFT-MOVING-ESCORT-SPLIT-LOCATION
                              ;;get-escort
                              ))
          (stable-p :in-theory (enable LEFT-BOUNDARY-UAV
                                       RIGHT-BOUNDARY-UAV
                                       WRAPPED-GET-UAV
                                       LEFT-MOVING-P-FLIP
                                       LEFT-MOVING-BOOL-TO-SIGN
                                       LEFT-MOVING-SIGN-P
                                       flip-direction))
          ))
|#

(defthm get-escort-flip-lemma
  (equal (get-escort x (flip ens))
         (if (consp ens)
             (get-escort-flip x ens)
           (get-escort x ens)))
  :hints (("Goal" :do-not-induct t)
          (pattern-hint
           (not (consp ens))
           :expand ((flip nil)))
          (stable-p ::in-theory (enable get-escort
                                        flip-uav
                                        flip-uav-index))
          (pattern-hint
           (:term (left-moving-bool-to-sign (LEFT-MOVING-P-FLIP X ENS)))
           :in-theory (enable left-moving-p-flip))))

(defthm uav-state-p-flip
  (implies
   (and
    (uav-state-p ens)
    (all-co-located-left-coordinated-p ens)
    (all-co-located-right-coordinated-p ens))
   (uav-state-p (flip ens)))
  :otf-flg t
  :hints (("Goal" :do-not-induct t
           :expand (uav-state-p (flip ens))
           :in-theory (enable equal-current-location-implies-bounds
                              leftcountguess-co-located-linear
                              rightcountguess-co-located-linear
                              co-located-left-index-arbitrary-bound
                              co-located-right-index-arbitrary-bound
                              all-ordered-locations-implication
                              ALL-CURRENT-LOCATIONS-BOUNDED-P
                              ALL-ORDERED-LOCATIONS
                              ALL-WITHIN-ESCORT-LEFT-COORDINATED-P
                              ALL-WITHIN-ESCORT-RIGHT-COORDINATED-P
                              ))))


(encapsulate
    ()
  
  (local (in-theory (disable UAV-STATE-EQUIV-1-IMPLIES-EQUAL-MIN-MIN-TIME-TO-IMPACT-FOR-UAV)))
  
  (def::und 3step (ens)
    (declare (xargs :fty ((uav-state) uav-state)))
    (let ((dt (min-min-time-to-impact-for-uav ens)))
      (let ((ens (move dt ens)))
        (let ((ens (share ens)))
          (flip ens)))))
  
  (def::und next-step (dt ens)
    (declare (xargs :fty ((nnrat uav-state) nnrat uav-state)))
    (let ((step (min dt (min-min-time-to-impact-for-uav ens))))
      (let ((ens (move step ens)))
        (let ((ens (share ens)))
          (let ((ens (flip ens)))
            (mvlist (- dt step) ens))))))

  )
  
