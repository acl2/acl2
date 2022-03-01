;;
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")
(include-book "events")
(include-book "coi/util/rewrite-equiv" :dir :system)

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

(in-theory (disable IMPENDING-ESCORT-FOR-UAV
                    (:rewrite IMPENDING-ESCORT-FOR-UAV-IMPLIES-IMPENDING-IMPACT-EVENT-FOR-UAV)
                    (:rewrite IMPENDING-EVENT-FOR-UAV-IMPLIES-IMPENDING-IMPACT-EVENT-FOR-UAV)))

(in-theory (disable WHAT-WE-WANT-TO-SAY-ABOUT-<=LOCATION-ALL))

(local (in-theory (disable LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-IMPLIES-LT-ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT)))

(defthm equal-sum-to-uav-id-equiv
  (implies
   (and (integerp c1) (integerp c2) (< c1 (N)))
   (iff (equal (+ c1 (uav-id-fix id1))
               c2)
        (and (uav-id-p (- c2 c1))
             (uav-id-equiv id1 (- c2 c1)))))
  :hints (("Goal" :in-theory (e/d (uav-id-equiv
                                   uav-id-fix
                                   uav-id-p)
                                  (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV
                                   )))))
(defthm minus-to-times
  (implies
   (syntaxp (any-p x))
   (equal (- x) (* -1 x))))

;; =============================================================
;;
;; update-location-all is one of the fundamental building
;; blocks of our event-based simulator.  It advances the state
;; of ensemble in time and space.
;;
;; =============================================================

(def::un update-uav-location (dt uav)
  (declare (xargs :fty ((nnrat uav) uav)))
  (update-uav uav :location (uav-location-fix (+ (uav->location uav) (* (uav->direction uav) dt)))))

(def::un update-location-uav (dt i ens)
  (declare (xargs :fty ((nnrat uav-id uav-list) uav)))
  (let ((uav (ith-uav i ens)))
    (update-uav-location dt uav)))

;; (defcong rat-equiv equal (rfix x) 1
;;   :hints (("Goal" :in-theory (e/d (rat-equiv)
;;                                   (EQUAL-RAT-FIX-TO-RAT-EQUIV)))))

;; (defcong nnrat-equiv equal (update-location-uav dt i ens) 1
;;   :hints (("Goal" :in-theory (e/d (update-location-uav) nil))))

;; (defcong uav-id-equiv equal (update-location-uav dt i ens) 2
;;   :hints (("Goal" :in-theory (enable update-location-uav))))

;; (def::signature update-location-uav (t t t) uav-p
;;   :hints (("Goal" :in-theory (enable update-location-uav))))

(def::un update-ith-uav (i uav list)
  (declare (xargs :fty ((nat uav uav-list) uav-list)))
  (if (zp i) (cons uav (cdr list))
    (let ((entry (uav-fix! (car list))))
      (cons entry (update-ith-uav (+ -1 i) uav (cdr list))))))

(in-theory (disable QUANT::OPEN-NTH))
;;(in-theory (disable CONS-OF-UAV-FIX-X-NORMALIZE-CONST-UNDER-UAV-LIST-EQUIV))

(defthm len-update-ith-uav
  (equal (len (update-ith-uav i uav list))
         (max (len list) (+ 1 (nfix i))))
  :hints (("Goal" :induct (update-ith-uav i uav list))))

(defun i-j-induction (i j list)
  (if (zp j) (list i j list)
    (i-j-induction (+ -1 i) (+ -1 j) (cdr list))))

(defthm nth-update-ith-uav
  (equal (nth i (update-ith-uav j uav list))
         (if (equal (nfix i) (nfix j)) (uav-fix uav)
           (if (< (nfix i) (max (len list) (+ 1 (nfix j))))
               (uav-fix (nth i list))
             nil)))
  :hints (("GOal" :do-not-induct t
           :in-theory (enable UAV-LIST-FIX)
           :expand ((:free (a b) (nth i (cons a b)))
                    (UPDATE-ITH-UAV J UAV LIST)
                    (UAV-LIST-FIX LIST))
           :induct (i-j-induction i j list))))

;; (def::und fix-dt (dt i ens)
;;   (declare (xargs :fty ((nnrat uav-id uav-list) nnrat)))
;;   (if (impending-impact-event-for-uav i ens)
;;       (min (min-time-to-impact-for-uav i ens) dt)
;;     (min (always-smallest-min-time-to-impending-impact ens) dt)))

(def::un update-location-rec (dt i ens)
  (declare (xargs :measure (uav-id-fix i)
                  :fty ((nnrat uav-id uav-list) uav-list)))
  (let ((i (uav-id-fix i)))
    (let ((uav (update-location-uav dt i ens)))
      (if (zp i) (update-ith-uav i uav ens)
        (update-ith-uav i uav (update-location-rec dt (1- i) ens))))))

;;(defcong nnrat-equiv equal (update-location-rec dt i ens) 1)

(defthm len-update-location-rec
  (equal (len (update-location-rec dt i list))
         (max (len list) (1+ (uav-id-fix i))))
  :hints (("Goal" :in-theory (disable update-location-uav
                                      equal-uav-id-fix-1-to-uav-id-equiv))))

(defthm nth-update-location-rec
  (implies
   (and
    (uav-id-p i)
    (<= i (uav-id-fix j)))
   (equal (nth i (update-location-rec dt j ens))
          (update-location-uav dt i ens)))
  :hints (("Goal" :in-theory (disable update-location-uav)
           :induct (update-location-rec dt j ens))
          (rewrite-equiv-hint equal)
          ))

;;(in-theory (disable UAV->ID-OF-UAV-FIX-UAV-INSTANCE-NORMALIZE-CONST))

(encapsulate
    ()

  (local
   (defthm nth-out-of-bounds
     (implies
      (and
       (natp i)
       (<= (len x) i))
      (equal (nth i x) nil))
     :hints (("GOal" :in-theory (enable nth)))))

  (defthm ith-uav-update-location-rec
    (implies
     (force (<= (uav-id-fix i) (uav-id-fix j)))
     (equal (ith-uav i (update-location-rec dt j ens))
            (update-location-uav dt i ens)))
    :hints (("Goal" :do-not-induct t
             :in-theory (enable ith-uav))))

  )

(def::und update-location-all (dt list)
  (declare (xargs :fty ((nnrat uav-list) uav-list)))
  (update-location-rec dt (1- (N)) list))


(defthm len-update-location-all
  (implies
   (equal (len list) (N))
   (equal (len (update-location-all dt list))
          (N)))
  :hints (("Goal" :in-theory (enable update-location-all))))

(defthm ith-uav-update-location-all
  (equal (ith-uav i (update-location-all dt ens))
         (update-location-uav dt i ens))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable uav-id-fix
                              uav-id-p
                              update-location-all))))

(defthm update-location-all-zero
  (implies
   (and
    (equal (nnrat-fix b) 0)
    (wf-ensemble ens))
   (uav-list-equiv (UPDATE-LOCATION-ALL B ens)
                   ens))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints (("Goal" :in-theory (enable
                              body-implies-uav-location-p
                              uav-list-equiv-pick-a-point-alt))))

(defthm update-location-all-zero-equal
  (implies
   (and
    (equal (nnrat-fix b) 0)
    (wf-ensemble ens))
   (equal (UPDATE-LOCATION-ALL B ens)
          (uav-list-fix ens)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints (("Goal" :in-theory (enable equal-to-uav-list-equiv))))

(defthm sequential-id-list-p-update-location-all
  (implies
   (and
    (equal (len ens) (n))
    (sequential-id-list-p ens))
   (sequential-id-list-p (update-location-all dt ens)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable sequential-id-list-p-reduction)
           :restrict ((sequential-id-list-p-reduction
                       ((list (update-location-all dt ens))))))))

(defthm uav-listp-update-location-rec
  (uav-list-p (update-location-rec dt z ens))
  :hints (("goal" :in-theory (disable less-than-zero-to-uav-id-equiv
                                      uav-id-fix-plus))))

(defthm uav-listp-update-location
  (uav-list-p (update-location-all dt ens))
  :hints (("goal" :in-theory (enable update-location-all))))

(defthm times-direction
  (implies
   (rationalp dt)
   (and (equal (* DT (UAV->DIRECTION x))
               (if (< (UAV->DIRECTION x) 0) (- dt)
                 dt))
        (equal (* (UAV->DIRECTION x) DT)
               (if (< (UAV->DIRECTION x) 0) (- dt)
                 dt)))))

(defthm plus-0
  (implies
   (rationalp x)
   (and (equal (+ x 0) x)
        (equal (+ 0 x) x))))

(with-arithmetic
 (defthm time-constant
   (implies
    (and
     (syntaxp (and (quotep x) (quotep y)))
     (and (rationalp x) (rationalp y) (rationalp z))
     (equal a (* x y)))
    (equal (binary-* x (binary-* y z))
           (binary-* a z)))))

;;
;; So escorts are a problem.  I don't think we can write
;; an "update-location-all" that preserves this
;; property.
;;
;; ** I think what we need is an "update-eventually" ..
;; something that will allow us to take "atomic"
;; steps that are larger than always-min-time.
;;
;; To do this we use step-time.  I don't know .. perhaps
;; there
;;
;;
;; So it appears we cannot avoid escort condition here.
;; If we have malformed escorts, then the time to impact
;; may be non-cellular.

(def::pattern-hint-list standard-hints
  (
   ;;negate-direction-equality ;; theory manipulation
   escort-condition-implies
   shared-boundary
   ordering-rule
   location-pinching-rule
   ))

(defun plus-one-induction-scheme (i j)
  (declare (xargs :measure (nfix (- (uav-id-fix j) (uav-id-fix i)))))
  (if (< (uav-id-fix i) (uav-id-fix j))
      (plus-one-induction-scheme (+ 1 (uav-id-fix i)) j)
    (list i j)))

(in-theory (enable UAV-LOCATION-FIX UAV-LOCATION-p))

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthm ORDERED-LOCATION-UPDATE-LOCATION-helper-helper
       (implies
        (and
         ;;
         ;; Basic properties of the primitive operations
         ;; should not depend on escort-condition (!)
         ;;
         ;;(escort-condition ens)
         ;;(homogenous-escort-direction ens)
         (wf-ensemble ens)

         ;;(not (event-for-uav i ens))
         ;;(not (event-for-uav (1+ (uav-id-fix i)) ens))

         (implies
          (impending-impact-event-for-uav i ens)
          (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))
         (implies
          (impending-impact-event-for-uav (+ 1 (uav-id-fix i)) ens)
          (<= (nnrat-fix dt) (min-time-to-impact-for-uav (+ 1 (uav-id-fix i)) ens)))

         (< (uav-id-fix i) (+ -1 (N))))
        (<= (uav->location (update-location-uav dt i ens))
            (uav->location (update-location-uav dt (+ 1 (uav-id-fix i)) ens))))
       :hints (("Goal" :do-not-induct t
                :in-theory (disable lte-min-time-to-impending-impact-event-implication-1)
                :use ((:instance what-we-want-to-say-about-ordered-location-list-p
                                 (list ens)
                                 (i i)
                                 (j (+ 1 (uav-id-fix i))))))
               (pattern::hint*
                (pattern::hint
                 (not (impending-impact-event-for-uav i ens))
                 :expand ((impending-impact-event-for-uav i ens)))
                (pattern::hint
                 (:and (:replicate (:term (* x y)) (y x) (x y))
                       (:match x (UAV->DIRECTION uav))
                       (:keep uav))
                 :cases ((equal (UAV->DIRECTION uav)  1)
                         (equal (UAV->DIRECTION uav) -1))
                 :repeat t
                 :name times-direction-reduction)
                standard-hints
                ;;ordering-rule
                ;;aux-hints
                )
               (pattern::hint
                expand-min-time-to-impact-for-uav
                )
               (average-hint)
               ))

     (defthm ORDERED-LOCATION-UPDATE-LOCATION-helper
       (implies
        (and
         ;;(escort-condition ens)
         ;;(homogenous-escort-direction ens)
         (wf-ensemble ens)
         ;;(not (exists-uav-with-event ens))
         (lte-min-time-to-impending-impact-event dt ens)
         (< (uav-id-fix i) (+ -1 (N))))
        (<= (uav->location (update-location-uav dt i ens))
            (uav->location (update-location-uav dt (+ 1 (uav-id-fix i)) ens))))
       :rule-classes :linear
       :hints (("Goal" :do-not-induct t
                :in-theory '(not-exists-uav-with-event-implies)
                :use (ORDERED-LOCATION-UPDATE-LOCATION-helper-helper
                      (:instance lte-min-time-to-impending-impact-event-implication-1
                                 (i i))
                      (:instance lte-min-time-to-impending-impact-event-implication-1
                                 (i (+ 1 (uav-id-fix i))))
                      ))))


     ))

  (defthm ORDERED-LOCATION-UPDATE-LOCATION
    (implies
     (and
      ;;(escort-condition ens)
      ;;(homogenous-escort-direction ens)
      (wf-ensemble ens)
      ;;(not (exists-uav-with-event ens))
      (lte-min-time-to-impending-impact-event dt ens)
      (case-split (< (uav-id-fix i) (uav-id-fix j))))
     (<= (uav->location (update-location-uav dt i ens))
         (uav->location (update-location-uav dt j ens))))
    :hints (("Goal" :do-not-induct t
             :in-theory (disable
                         ;; acl2 8.3+ : Had to disable this rule
                         EQUAL-SUM-TO-UAV-ID-EQUIV
                         update-location-uav)
             :induct (plus-one-induction-scheme i j))))

  )

(defthm ORDERED-LOCATION-LIST-P-UPDATE-LOCATION-ALL
  (implies
   (and
    (wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (ORDERED-LOCATION-LIST-P (update-location-all dt ens)))
  :hints (("Goal" :do-not-induct t
           :expand (ORDERED-LOCATION-LIST-QUANT-P (UPDATE-LOCATION-ALL DT ENS))
           :in-theory (e/d (ORDERED-LOCATION-LIST-P-TO-ORDERED-LOCATION-LIST-QUANT-P)
                           (rfix update-location-uav)))
          (and stable-under-simplificationp
               '(:in-theory (enable uav-id-p
                                    uav-id-fix)))))

(defthm wf-ensemble-update-location-all
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (wf-ensemble (update-location-all dt ens))))

;; =============================================================
;; (defcong nnrat-equiv equal (update-location-all dt ens) 1
;;   :hints (("Goal" :in-theory (enable update-location-all))))
;; ===================================================================

;; (def::pattern-hint negate-direction-equality
;;   (:and (:commutes (not (equal A B)) (A B))
;;         (:match A (UAV->DIRECTION uav))
;;         (:match B 1)
;;         (:keep uav))
;;   :restrict ((negate-direction-equality ((uav uav))))
;;   :in-theory (enable negate-direction-equality)
;;   :repeat t)

;; =============================================================


(defthm equal-N-1-reductions
  (implies
   (and
    (equal (N) 1)
    (syntaxp (or (not (quotep x))
                 (not (equal (cadr x) 0)))))
   (and
    (equal (ith-uav x ens)
           (ith-uav 0 ens))
    (equal (uav-id-fix x) 0)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm simplify-<-sums
  (implies
   (and (rationalp x) (rationalp y))
   (and (iff (< 0 (+ (* 1/2 x)
                     (* -1/2 y)))
             (< y x))
        (iff (< 0 (+ (* -1/2 x)
                     (* 1/2 y)))
             (< x y)))))

;; Oy .. should really only happen in the top level ..
(defthmd normalize-equal-plus-times
  (implies
   (and (rationalp dt) (rationalp x) (rationalp y))
   (iff (equal (+ dt x) y)
        (hide (rewrite-equiv (equal dt (- y x))))))
  :hints (("Goal" :expand (:free (x) (hide x)))))

;; DAG -- here it is again ..
;;(in-theory (enable uav-location-fix uav-location-p))

(defthm normalize-equal-zero-sum-locations
  (iff (equal 0 (+ (- (uav->location uav1))
                   (uav->location uav2)))
       (equal (uav->location uav1)
              (uav->location uav2))))

;; DAG -- and again ..
;;(in-theory (enable UAV-LOCATION-FIX uav-location-p))

(defthm p-is-right-perimeter
  (equal (uav-location-fix (p))
         (RIGHT-PERIMETER-BOUNDARY))
  :hints (("Goal" :in-theory (enable RIGHT-PERIMETER-BOUNDARY
                                     uav-location-fix
                                     uav-location-p))))

;; I think for the final proof we will want to rewrite everything in
;; terms of left-perimeter-boundaries and then express boundaries as a
;; product of the indicies and segment length.  We may need non-linear
;; arithmetic to finish the job.

(in-theory (enable equal-uav-id-fix-1-to-uav-id-equiv))

;; DAG -- ugh
;;(in-theory (enable UAV-LOCATION-FIX UAV-LOCATION-P))

(def::pattern-hint daves-right-boundary-is-ordered-rule
  (:and
   (:replicate (:term (UAV-RIGHT-BOUNDARY (ITH-UAV iindex ENS))) (jindex iindex))
   (:not (:equal iindex jindex))
   ;;
   ;; It might be nice to reduce overhead on some of these
   ;; patterns .. chains of inequalities are N^2.
   ;;
   ;; Makes me contemplate whether we could somehow support
   ;; recursive patterns.
   ;;
   ;;(:not (< (UAV-RIGHT-BOUNDARY (ITH-UAV iindex ENS))
   ;;      (UAV-RIGHT-BOUNDARY (ITH-UAV jindex ENS))))
   ;;
   (:call (uav-fix iindex) (i))
   (:call (uav-fix jindex) (j))
   (:not (< (uav-right-boundary (ith-uav iindex ens))
            (uav-right-boundary (ith-uav jindex ens))))
   (:call (lte-index-filter i j) nil)
   (:keep ens iindex jindex)
   )
  :use ((:instance right-boundary-is-ordered
                   (uav1 (ITH-UAV iindex ENS))
                   (uav2 (ITH-UAV jindex ENS)))))

(def::pattern-hint ordered-location-list-p-forward-chaining
  (:and
   (< (uav->location (ith-uav jindex ens))
      (uav->location (ith-uav iindex ens)))
   (:call (uav-fix iindex) (i))
   (:call (uav-fix jindex) (j))
   (:call (lte-index-filter i j) nil)
   (:keep ens iindex jindex))
  :use ((:instance what-we-want-to-say-about-ordered-location-list-p
                   (list ens)
                   (i iindex)
                   (j jindex))))


(defthm times-zero-condition
  (equal (* (if a 0 0) x) 0))

(defthm rearrange-lt
  (implies
   (and (rationalp x) (rationalp y))
   (iff (< (+ (* 1/2 x) (* -1/2 y)) 0)
        (< x y))))

(defthm degenerate-alpha
  (iff (UAV-ID-EQUIV (+ -1 (N)) (+ 2 (UAV-ID-FIX I)))
       (if (< (+ 2 (UAV-ID-FIX I)) (N))
           (UAV-ID-EQUIV I (+ -3 (N)))
         (equal (N) 1)))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (uav-id-fix
                            uav-id-equiv
                            uav-id-fix)
                           (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV
                            ;;EQUAL-UAV-ID-FIX-TO-UAV-ID-EQUIV
                            )))))

(defthm degenerate-beta
  (iff (UAV-ID-EQUIV (+ 2 (UAV-ID-FIX I)) 0)
       (<= (+ -2 (N)) (UAV-ID-FIX I) ))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (uav-id-fix
                            uav-id-p
                            uav-id-equiv
                            uav-id-fix)
                           (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV
                            ;;EQUAL-UAV-ID-FIX-TO-UAV-ID-EQUIV
                            )))))

;; (defthmd woot-woot-2
;;   (implies
;;    (and
;;     (< (uav-id-fix i) (uav-id-fix k))
;;     (uav-id-p (+ -1 (UAV-ID-FIX K))))
;;    (iff (< (+ 1 (UAV-ID-FIX I)) (UAV-ID-FIX K))
;;         (not (hide (rewrite-equiv (uav-id-equiv i (+ -1 (UAV-ID-FIX K))))))))
;;   :hints (("Goal" :do-not '(preprocess)
;;            :expand (:free (x) (hide x))
;;            :in-theory (e/d (uav-id-equiv
;;                             uav-id-fix
;;                             uav-id-p)
;;                            (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV)))))

;; (defthm woot-woot-2-rewrite
;;   (implies
;;    (and
;;     (in-conclusion-check (< (+ 1 (UAV-ID-FIX I)) (UAV-ID-FIX K)) :top :negated)
;;     (< (uav-id-fix i) (uav-id-fix k))
;;     (uav-id-p (+ -1 (UAV-ID-FIX K))))
;;    (iff (< (+ 1 (UAV-ID-FIX I)) (UAV-ID-FIX K))
;;         (not (uav-id-equiv i (+ -1 (UAV-ID-FIX K))))))
;;   :hints (("Goal" :expand (:free (x) (hide x))
;;            :in-theory (enable woot-woot-2))))

;; (def::pattern-hint woot-woot-2-hint
;;   (not (< (+ 1 (UAV-ID-FIX I)) (UAV-ID-FIX K)))
;;   :in-theory (enble woot-woot-2)
;;   :restrict ((woot-woot-2 ((i i) (k k)))))

(defthm zeff
  (implies
   (case-split (uav-id-p (+ 2 (UAV-ID-FIX I))))
   (iff (EQUAL 1 (+ (* 1/2 (UAV-ID-FIX J))
                    (* -1/2 (UAV-ID-FIX I))))
        (uav-id-equiv J (+ 2 (UAV-ID-FIX I)))))
  :hints (("Goal"  :in-theory '(uav-id-equiv
                                uav-id-p
                                uav-id-fix))
          (and stable-under-simplificationp
               '(:in-theory (current-theory :here)))))

(defthm degenerate-case-N-3
  (implies
   (case-split (uav-id-p (+ -3 (N))))
   (iff (EQUAL (N) (+ 3 (UAV-ID-FIX I)))
        (uav-id-equiv I (+ -3 (N)))))
  :hints (("Goal" :in-theory '(natp
                               uav-id-fix
                               uav-id-p
                               uav-id-equiv))))

(defthm impending-event-for-uav-still-impending
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (implies
     (impending-impact-event-for-uav i ens)
     (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens))))
   (iff (impending-event-for-uav i (update-location-all dt ens))
        (impending-event-for-uav i ens)))
  :hints (("Goal" :in-theory (disable NATP-UAV-ID-FIX rationalp-location event-for-uav impending-event-for-uav)
           :expand ((min-time-to-impact-for-uav i ens)
                    (event-for-uav i ens)
                    (impending-event-for-uav i ens)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (impending-impact-event-for-uav
                                  event-for-uav impending-event-for-uav)
                                 (NATP-UAV-ID-FIX rationalp-location))))
          (pattern::hint*
           ordering-rule
           )
          (average-hint)
          ))

(defthm impending-escort-for-uav-still-pending
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (implies
     (impending-impact-event-for-uav i ens)
     (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))

    )
   (iff (impending-escort-for-uav i (update-location-all dt ens))
        (impending-escort-for-uav i ens)))
  :hints (("Goal" :in-theory (disable NATP-UAV-ID-FIX rationalp-location  event-for-uav impending-escort-for-uav)
           :expand ((min-time-to-impact-for-uav i ens)
                    (event-for-uav i ens)
                    (impending-escort-for-uav i ens)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (IMPENDING-IMPACT-EVENT-FOR-UAV
                                  event-for-uav impending-escort-for-uav)
                                 (NATP-UAV-ID-FIX rationalp-location))))
          (pattern::hint*
           ordering-rule
           )
          (average-hint)
          ))

(defthm impending-impact-event-for-uav-still-pending
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (implies
     (impending-impact-event-for-uav i ens)
     (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))
    )
   (iff (impending-impact-event-for-uav i (update-location-all dt ens))
        (impending-impact-event-for-uav i ens)))
  :hints (("Goal" :in-theory (e/d (imminent-event-reduction)
                                  (IMPENDING-ESCORT-FOR-UAV
                                   impending-event-for-uav
                                   )))))

(encapsulate
    ()

  (in-theory (disable UAV-ID-FIX-UAV-ID-P))

  (local (in-theory (disable ;;SIMPLIFY-SUMS-<
                             ;;|(< y (+ (- c) x))|
                             SINGLE-UAV-PERIMETER-ITH-INDEX
                             min-time-to-impact-for-uav
                             )))

  (defthmd min-time-to-impact-decreases-with-update-location-helper
    (implies
     (and
      ;;(escort-condition ens)
      ;;(homogenous-escort-direction ens)
      (wf-ensemble ens)
      ;;(not (event-for-uav i ens))
      (lte-min-time-to-impending-impact-event dt ens)
      (implies
       (not (chasing-neighbor i ens))
       (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))
      )
     (equal (min-time-to-impact-for-uav i (update-location-all dt ens))
            (if (chasing-neighbor i ens)
                (min-time-to-impact-for-uav i ens)
              (- (min-time-to-impact-for-uav i ens)
                 (nnrat-fix dt)))))
    :hints (("Goal" :do-not '(preprocess)
             :expand ((min-time-to-impact-for-uav i (update-location-all dt ens))
                      ;;(min-time-to-impact-for-uav i ens)))
                      ))
            ;;))
            (pattern::hint*
             expand-chasing-neighbor
             expand-min-time-to-impact-for-uav
             ;;escort-condition-implies
             ordering-rule
             ;;standard-hints
             ;;aux-hints
             )
            (and stable-under-simplificationp
                 '(:in-theory (enable UAV-LOCATION-FIX
                                      MIN-TIME-TO-IMPACT-FOR-UAV
                                      chasing-neighbor)))
            (average-hint)
            )
    )
  )

(defthm min-time-to-impact-decreases-with-update-location
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (equal (min-time-to-impact-for-uav i (update-location-all dt ens))
          (if (chasing-neighbor i ens)
              (min-time-to-impact-for-uav i ens)
            (- (min-time-to-impact-for-uav i ens)
               (nnrat-fix dt)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable lte-min-time-to-impending-impact-event-implication-chasing-neighbor)
           :expand (:free (x) (hide x))
           :use min-time-to-impact-decreases-with-update-location-helper)))

(defthm largest-impending-event-index-update-location-all-invariant
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (equal (largest-impending-event-index i (update-location-all dt ens))
          (largest-impending-event-index i ens)))
  :hints (("Goal" :induct (largest-impending-event-index i ens)
           :expand (LARGEST-IMPENDING-EVENT-INDEX I (UPDATE-LOCATION-ALL DT ENS)))))

(defthm smallest-impending-dt-update-location-all-invariant
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (equal (smallest-impending-dt i (update-location-all dt ens))
          (smallest-impending-dt i ens)))
  :hints (("Goal" :in-theory (enable CHASING-NEIGHBOR-IS-NOT-IMPENDING-IMPACT-EVENT-FOR-UAV))))

(defthm smallest-impending-dt-index-update-location-all-invariant
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (equal (smallest-impending-dt-index (update-location-all dt ens))
          (smallest-impending-dt-index ens)))
  :hints (("Goal" :in-theory (enable smallest-impending-dt-index))))

(encapsulate
    ()

  (in-theory (disable min-time-to-impact-for-uav))

  (local
   (defthm equal-nnrat-fix
     (implies
      (and
       (in-conclusion-check (equal (+ (- (nnrat-fix dt)) z) 0) :top t)
       (acl2-numberp z))
      (iff (equal (+ (- (nnrat-fix dt)) z) 0)
           (hide (rewrite-equiv (equal (nnrat-fix dt) z)))))
     :hints (("Goal" :expand (:Free (x) (hide x))))))

  ;;



  ;;(without-subsumption
   (local
    (defthm update-location-all-escort-condition-helper
     (implies
      (and
       (escort-condition ens)
       (wf-ensemble ens)
       (lte-min-time-to-impending-impact-event dt ens))
      (escort-condition-p i j (update-location-all dt ens)))
     :rule-classes nil
     :hints (("Goal"
              :use ((:instance escort-condition-implies
                               (i i)
                               (j j))
                    (:instance lte-min-time-to-impending-impact-event-implication-chasing-neighbor
                               (i i))
                    (:instance lte-min-time-to-impending-impact-event-implication-chasing-neighbor
                               (i j))))
             (pattern::hint*
              location-pinching-rule
              escort-condition-implies
              right-perimeter-escort-condition-implies
              )
             (pattern::hint*
              expand-chasing-neighbor
              expand-min-time-to-impact-for-uav
              )
             (average-hint)
             )))

  (defthm update-location-all-escort-condition
    (implies
     (and
      (escort-condition ens)
      (wf-ensemble ens)
      (lte-min-time-to-impending-impact-event dt ens)
      )
     (escort-condition (update-location-all dt ens)))
    :hints (("Goal" :in-theory '(escort-condition)
             :use (:instance update-location-all-escort-condition-helper
                             (i (mv-nth 0 (ESCORT-CONDITION-WITNESS (UPDATE-LOCATION-ALL DT ENS))))
                             (j (mv-nth 1 (ESCORT-CONDITION-WITNESS (UPDATE-LOCATION-ALL DT ENS))))))))

  )

;;
;; DAG - boy, it sure seems wrong to add a rule
;; like this ..
(defthm UAV-ID-EQUIV-I-FIX-I
  (iff (UAV-ID-EQUIV I (UAV-ID-FIX I)) t))

;;
;; The following rule failed to apply and
;; reported that it could not establish
;; (UAV-ID-EQUIV I (UAV-ID-FIX I))
;;
(defthm adjacent-locations-never-smaller-minus
  (implies
   (and
    (in-conclusion-check (< (UAV->LOCATION (ITH-UAV I ENS))
                            (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX I)) ENS))) :top t)
    (wf-ensemble ens))
   (not (< (UAV->LOCATION (ITH-UAV I ENS))
           (UAV->LOCATION (ITH-UAV (+ -1 (UAV-ID-FIX I)) ENS)))))
  :hints (("Goal" :use ((:instance what-we-want-to-say-about-ordered-location-list-p
                                   (list ens)
                                   (i (+ -1 (UAV-ID-FIX I)))
                                   (j i))))))

(defthm adjacent-locations-never-smaller-plus
  (implies
   (and
    (in-conclusion-check (< (UAV->LOCATION (ITH-UAV (+ 1 (UAV-ID-FIX I)) ENS))
                            (UAV->LOCATION (ITH-UAV I ENS))) :top t)
    (wf-ensemble ens)
    (< (+ 1 (UAV-ID-FIX I)) (N)))
   (not (< (UAV->LOCATION (ITH-UAV (+ 1 (UAV-ID-FIX I)) ENS))
           (UAV->LOCATION (ITH-UAV I ENS)))))
  :hints (("Goal" :use ((:instance what-we-want-to-say-about-ordered-location-list-p
                                   (list ens)
                                   (i i)
                                   (j (+ 1 (UAV-ID-FIX I))))))))

;; So .. this may be saying two different things.
;; We might want a strong version and a weak version.
(defthm event-for-uav-update-location-all
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))
   (iff (event-for-uav i (update-location-all dt ens))
        (and (impending-event-for-uav i ens)
             (equal (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))))
  :hints (("Goal" :in-theory (enable impending-event-for-uav
                                     event-for-uav))
          (pattern::hint*
           ordering-rule
           escort-condition-implies
           (pattern::hint
            (not (impending-impact-event-for-uav i ens))
            :expand ((impending-impact-event-for-uav i ens)))
           )
          (and stable-under-simplificationp
               '(:in-theory (enable min-time-to-impact-for-uav)))
          (average-hint)
          ))


(encapsulate
    ()

  (local (in-theory (disable LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-IMPLICATION-1
                             LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-IMPLICATION-2)))

  (defthm event-for-uav-update-location-all-strong
    (implies
     (and
      (escort-condition ens)
      (wf-ensemble ens)
      (lte-min-time-to-impending-impact-event dt ens))
     (iff (event-for-uav i (update-location-all dt ens))
          (and (impending-event-for-uav i ens)
               (equal (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))))
    :hints (("goal" :in-theory (enable impending-event-for-uav
                                       event-for-uav)
             :use (:instance LTE-MIN-TIME-TO-IMPENDING-IMPACT-EVENT-IMPLICATION-1))
            (pattern::hint*
             ordering-rule
             escort-condition-implies
             (pattern::hint
              (not (impending-impact-event-for-uav i ens))
              :expand ((impending-impact-event-for-uav i ens)))
             )
            (and stable-under-simplificationp
                 '(:in-theory (enable min-time-to-impact-for-uav)))
            (average-hint)
            ))
  )

(defthm escort-event-for-uav-update-location-all
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    (implies
     (impending-event-for-uav i ens)
     (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens))))
   (iff (escort-event-for-uav i (update-location-all dt ens))
        (and (impending-escort-for-uav i ens)
             (equal (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))))
  :hints (("Goal" :in-theory (enable IMPENDING-ESCORT-FOR-UAV
                                     escort-event-for-uav))
          (and stable-under-simplificationp
               '(:in-theory (enable min-time-to-impact-for-uav)))
          (pattern::hint*
           ordering-rule
           escort-condition-implies
           )
          (average-hint)
          ))

(defthm impact-event-for-uav-update-location-all
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))
   (iff (impact-event-for-uav i (update-location-all dt ens))
        (and (impending-impact-event-for-uav i ens)
             (equal (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (IMMINENT-EVENT-REDUCTION
                            impact-event-for-uav)
                           (IMPENDING-ESCORT-FOR-UAV
                            IMPENDING-EVENT-FOR-UAV)))))

(defthm impact-event-for-uav-update-location-all-strong
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (iff (impact-event-for-uav i (update-location-all dt ens))
        (and (impending-impact-event-for-uav i ens)
             (equal (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (IMMINENT-EVENT-REDUCTION
                            impact-event-for-uav)
                           (IMPENDING-ESCORT-FOR-UAV
                            IMPENDING-EVENT-FOR-UAV)))))

;;
;; This tells us that the step-min-time finds at least
;; one event .. in case anyone cares.
;;
(defthmd escort-event-implies-event-for-uav
  (implies
   (and
    (escort-condition ens)
    (SEQUENTIAL-ID-LIST-P ENS)
    (equal (len ens) (N))
    (ordered-location-list-p ens)
    (escort-event-for-uav i ens))
   (or (event-for-uav (+ -1 (uav-id-fix i)) ens)
       (event-for-uav (+ 1 (uav-id-fix i)) ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable escort-event-for-uav))
          (pattern::hint*
           escort-condition-implies
           )
          (and stable-under-simplificationp
               '(:in-theory (enable event-for-uav)))
          ))

(defthm event-for-uav-from-impending-event
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (impending-event-for-uav i ens)
    (nnrat-equiv z (min-time-to-impact-for-uav i ens)))
   (event-for-uav i (update-location-all z ens)))
  :hints (("Goal" :in-theory (disable min-time-to-impact-for-uav
                                      event-for-uav
                                      impending-event-for-uav)
           :expand ((event-for-uav i ens)
                    (impending-event-for-uav i ens)))
          (and stable-under-simplificationp
               '(:in-theory (enable nnrat-fix
                                    nnrat-p
                                    event-for-uav
                                    min-time-to-impact-for-uav
                                    impending-event-for-uav)))
          (pattern::hint*
           standard-hints
           ;;aux-hints
           )

          ))

(defthm escort-event-for-uav-from-impending-escort-event
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (impending-escort-for-uav i ens)
    (nnrat-equiv z (min-time-to-impact-for-uav i ens)))
   (escort-event-for-uav i (update-location-all z ens)))
  :hints (("Goal" :in-theory (disable min-time-to-impact-for-uav
                                      event-for-uav
                                      impending-escort-for-uav)
           :expand ((event-for-uav i ens)
                    (impending-escort-for-uav i ens)))
          (and stable-under-simplificationp
               '(:in-theory (enable nnrat-fix
                                    nnrat-p
                                    event-for-uav
                                    escort-event-for-uav
                                    min-time-to-impact-for-uav
                                    impending-escort-for-uav)))
          (pattern::hint*
           standard-hints
           ;;aux-hints
           )

          ))

(defthm not-event-for-uav-from-not-impending-impact-event
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (not (impending-escort-for-uav i ens))
    (not (impending-event-for-uav i ens))
    (nnrat-equiv z (min-time-to-impact-for-uav i ens)))
   (and (not (escort-event-for-uav i (update-location-all z ens)))
        (not (event-for-uav i (update-location-all z ens)))))
  :hints (("Goal" :in-theory (disable min-time-to-impact-for-uav
                                      event-for-uav
                                      impending-escort-for-uav)
           :expand ((escort-event-for-uav i ens)
                    (event-for-uav i ens)
                    (impending-event-for-uav i ens)
                    (impending-escort-for-uav i ens)))
          (and stable-under-simplificationp
               '(:in-theory (enable nnrat-fix
                                    nnrat-p
                                    event-for-uav
                                    escort-event-for-uav
                                    min-time-to-impact-for-uav
                                    impending-escort-for-uav)))
          (pattern::hint*
           standard-hints
           ;;aux-hints
           )
          ))

(defthm imminent-event-implies-impact-event
  (implies
   (and
    (escort-condition ens)
    ;;(homogenous-escort-direction ens)
    (wf-ensemble ens)
    (nnrat-equiv z (min-time-to-impact-for-uav i ens))
    )
   (iff (impact-event-for-uav i (update-location-all z ens))
        (impending-impact-event-for-uav i ens)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (imminent-event-reduction
                            impact-event-for-uav)
                           (IMPENDING-ESCORT-FOR-UAV
                            IMPENDING-EVENT-FOR-UAV
                            WF-ENSEMBLE)))))


(encapsulate
    ()

  (in-theory (disable min-time-to-impact-for-uav))

  (defun-sk smallest-min-time-to-impact (i ens)
    (forall (j) (<= (min-time-to-impact-for-uav i ens) (min-time-to-impact-for-uav j ens))))

  (in-theory (disable smallest-min-time-to-impact))

  (local
   (defthm smallest-min-time-to-impact-implies
     (implies
      (smallest-min-time-to-impact i ens)
      (<= (min-time-to-impact-for-uav i ens) (min-time-to-impact-for-uav j ens)))
     :hints (("Goal" :use smallest-min-time-to-impact-necc))))

  (defun-sk exists-uav-with-smallest-min-time-to-impact (ens)
    (exists (i) (smallest-min-time-to-impact i ens)))

  (defthm exists-uav-with-smallest-min-time-to-impact-implies
    (implies
     (exists-uav-with-smallest-min-time-to-impact ens)
     (smallest-min-time-to-impact (exists-uav-with-smallest-min-time-to-impact-witness ens) ens)))

  (in-theory (disable exists-uav-with-smallest-min-time-to-impact))

  (defchoose uav-with-smallest-min-time-to-impact (i) (ens)
    (smallest-min-time-to-impact i ens))

  (defthm exists-implies-witness
    (implies
     (exists-uav-with-smallest-min-time-to-impact ens)
     (smallest-min-time-to-impact (uav-with-smallest-min-time-to-impact ens) ens))
    :rule-classes nil
    :hints (("Goal"
             :use (:instance uav-with-smallest-min-time-to-impact
                             (i (EXISTS-UAV-WITH-SMALLEST-MIN-TIME-TO-IMPACT-witness ens))))))

  (defthm uav-with-smallest-min-time-to-impact-property
    (implies
     (exists-uav-with-smallest-min-time-to-impact ens)
     (<= (min-time-to-impact-for-uav (uav-with-smallest-min-time-to-impact ens) ens)
         (min-time-to-impact-for-uav j ens)))
    :hints (("Goal"
             :use (exists-implies-witness
                   (:instance uav-with-smallest-min-time-to-impact
                              (i (uav-with-smallest-min-time-to-impact ens))))
             )))

  )

;;
;; ===================================================================================
;;



;;
;; ===================================================================================
;;

;; (def::un deprecated-smallest-dt (i ens)
;;   (declare (xargs :measure (uav-id-fix i)
;;                   :fty ((uav-id uav-list) uav-id)))
;;   (let ((i (uav-id-fix i)))
;;     (if (zp i) i
;;       (let ((j (deprecated-smallest-dt (1- i) ens)))
;;         (if (< (min-time-to-impact-for-uav i ens)
;;                (min-time-to-impact-for-uav j ens))
;;             (uav-id-fix i)
;;           (uav-id-fix j))))))

;; (defthm deprecated-smallest-dt-is-smallest
;;   (implies
;;    (<= (uav-id-fix k) (uav-id-fix i))
;;    (<= (min-time-to-impact-for-uav (deprecated-smallest-dt i ens) ens)
;;        (min-time-to-impact-for-uav k ens))))

;; ;; This is the top level function that steps time.
;; ;; Let's do this for now .. we can circle back with an
;; ;; incremental version.
;; (defun next-location (ens)
;;   (let ((i (deprecated-smallest-dt (1- (N)) ens)))
;;     (update-location-all (min-time-to-impact-for-uav i ens) ens)))

;; (defthm deprecated-lte-min-time-to-impact-min-time-to-impact-for-uav-deprecated-smallest-dt
;;   (implies
;;    (and
;;     (escort-condition ens)
;;     (homogenous-escort-direction ens)
;;     (wf-ensemble ens)
;;     )
;;    (deprecated-lte-min-time-to-impact (min-time-to-impact-for-uav (deprecated-smallest-dt (1- (N)) ens) ens) ens))
;;   :hints (("Goal" :do-not-induct t
;;            :in-theory (enable deprecated-lte-min-time-to-impact))))

;; (defthm next-location-invariants
;;   (implies
;;    (and
;;     (escort-condition ens)
;;     (homogenous-escort-direction ens)
;;     (wf-ensemble ens))
;;    (and (escort-condition (next-location ens))
;;         (homogenous-escort-direction (next-location ens))
;;         (wf-ensemble (next-location ens))))
;;   :hints (("Goal" :do-not-induct t
;;            :in-theory (disable homogenous-escort-direction-p)
;;            :expand (:free (dt) (homogenous-escort-direction (UPDATE-LOCATION-ALL dt ens))))))

;; (in-theory (disable next-location wf-ensemble))

;; (include-book "coi/defung/defung" :dir :system)

;; (def::ung step-to-event (ens)
;;   (if (exists-uav-with-event ens) ens
;;     (let ((ens (next-location ens)))
;;       (step-to-event ens))))

;; (defthm step-to-event-invariants
;;   (implies
;;    (and
;;     ;;(not (exists-uav-with-event ens))
;;     (escort-condition ens)
;;     (homogenous-escort-direction ens)
;;     (wf-ensemble ens))
;;    (and (escort-condition (step-to-event ens))
;;         (homogenous-escort-direction (step-to-event ens))
;;         (wf-ensemble (step-to-event ens)))))

;; (defthm step-to-event-variant
;;   (implies
;;    (and
;;     (step-to-event-domain ens)
;;     ;;(not (exists-uav-with-event ens))
;;     (escort-condition ens)
;;     (homogenous-escort-direction ens)
;;     (wf-ensemble ens))
;;    (exists-uav-with-event (step-to-event ens)))
;;   :hints (("Goal" :induct (step-to-event ens))))

;; (defun step-events (n ens)
;;   (if (zp n) ens
;;     (let ((ens (if (exists-uav-with-event ens)
;;                    (flip-on-events ens)
;;                  ens)))
;;       (let ((ens (step-to-event ens)))
;;         (step-events (1- n) ens)))))

;; (defthm step-events-invariants
;;   (implies
;;    (and
;;     (escort-condition ens)
;;     (homogenous-escort-direction ens)
;;     (wf-ensemble ens))
;;    (and (escort-condition (step-events n ens))
;;         (homogenous-escort-direction (step-events n ens))
;;         (wf-ensemble (step-events n ens)))))

(defthmd balanced-average
  (implies
   (and
    (wf-ensemble ens)
    (< (uav-id-fix i) (uav-id-fix j))
    (equal (uav-id-fix j) (+ 1 (uav-id-fix i))))
   (iff (EQUAL (UAV-RIGHT-BOUNDARY (ITH-UAV I ENS))
               (AVERAGE (UAV->LOCATION (ITH-UAV I ENS))
                        (UAV->LOCATION (ITH-UAV J ENS))))
        (equal (- (UAV->LOCATION (ITH-UAV I ENS))
                  (UAV-LEFT-BOUNDARY (ITH-UAV I ENS)))
               (- (UAV-RIGHT-BOUNDARY (ITH-UAV J ENS))
                  (UAV->LOCATION (ITH-UAV J ENS))))))
   :hints (("Goal" :nonlinearp t
           :in-theory (e/d (average
                            UAV-RIGHT-BOUNDARY
                            UAV-LEFT-BOUNDARY)
                           (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV
                            rewrite-<-into-average
                            double-average-is-just-sum
                            reconstruct-average
                            rewrite-equality-into-just-average
                            reconstruct-average-difference
                            rewrite-equality-into-average
                            REWRITE-LEFT-BOUNDARY-TO-RIGHT-BOUNDARY
                            )))
          (pattern::hint
           ordering-rule
           )
          ;;(slow-rewrite-with-equiv uav-id-equiv)
          ))

(def::pattern-hint balanced-average
  (:and
   (:commutes (equal X Y) (X Y))
   (:match X (AVERAGE A B))
   (:match Y (UAV-RIGHT-BOUNDARY (ITH-UAV I ENS))))
  :use ((:instance balanced-average
                   (ens ens)
                   (i I)
                   (j (+ 1 (uav-id-fix I))))))

