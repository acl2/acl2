;;
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")
(include-book "datatypes")

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

;; Event classification:
;;
;; min-time-to-impact : The minimum time until something interesting might happen.
;;
;; impact-event-for-uav : either an event or an escort-event
;;
;; escort-event-for-uav : UAV causes neighbor to switch directions (escort)
;; event-for-uav        : UAV will switch directions
;;
;; impending-impact-event-for-uav: tells us that we can predict how long it will
;;                                 be before an event.  Either an event or an
;;                                 escort-event are imminent
;;
;; impending-event-for-uav  : event will happen in min-time-to-impact
;; impending-escort-for-uav : escort will start in min-time-to-impact
;;
;; chasing-neighbor : we are not getting closer to an event because we
;;                    are chasing the neighbor with with whom we will
;;                    have the event.  This should be the negation of
;;                    impending-impact-event-for-uav.
;;
;; (implies
;;   (lte-min-time-to-impending-impact-event dt ens)
;;   (equal (min-time-to-impact-for-uav i (update-location-all dt ens))
;;          (if (chasing-neighbor i ens)
;;              (min-time-to-impact-for-uav i ens)
;;            (- (min-time-to-impact-for-uav i ens)
;;               (nnrat-fix dt)))))
;;
;; (equal (min-time-to-imact-for-uav i ())
;;
;; It feels like we ougt to have a theorem sort of like:
;;
;; (impact-event-for-uav i (update-location-all (min-time-to-impact-for-uav i ens) ens))
;;
;; .. but I don't know if this is useful.  I think it would be more useful
;; if we were attempting to prove something about progress.
;;

;;    0    1    2    3
;; |----+----+----+----
;;        (0,1,2)->

;; (defun-sk event-time (t0 trace)
;;   (exists (i) (event-for-uav i (ensemble t0 trace))))

;; (defchoose next-event-time (tN) (ti trace)
;;   (and (< ti tN)
;;        (event-time tN trace)
;;        (forall (tx) (implies (< tx tN) (not (event-time tx trace))))))

;; For step event, we know that there are no intervening events before
;; the "next event".  This is the "continue" phase of the algoritm.

;; We need to prove that this is always positive in
;; reasonable configurations.

;; =============================================================
;;
;; event-for-uav establishes when the appropriate next action
;; for a UAV is to change direction.
;;
;; =============================================================

(def::un event-for-uav (i ens)
  (declare (type t i ens))
  (let ((i   (uav-id-fix i)))
    (or
     ;; Left-most drone encounters left perimeter
     (and
      (= i 0)
      (< (UAV->direction (ith-uav i ens)) 0)
      (equal (UAV->location (ith-uav i ens))
             (left-perimeter-boundary)))
     ;; Right-most drone encounters right perimeter
     (and
      (= (1+ i) (N))
      (< 0 (UAV->direction (ith-uav i ens)))
      (equal (UAV->location (ith-uav i ens))
             (right-perimeter-boundary)))
     ;; Encounter left drone on or beyond left boudary
     (and
      (< 0 i)
      (< (UAV->direction (ith-uav i ens)) 0)
      (<= (UAV->location (ith-uav i ens))
          (UAV-left-boundary (ith-uav i ens)))
      (equal (UAV->location (ith-uav (1- i) ens))
             (UAV->location (ith-uav i ens)))
      )
     ;; Encounter right drone on or beyond right boundary
     (and
      (< (1+ i) (N))
      (< 0 (UAV->direction (ith-uav i ens)))
      (<= (UAV-right-boundary (ith-uav i ens))
          (UAV->location (ith-uav i ens)))
      (equal (UAV->location (ith-uav i ens))
             (UAV->location (ith-uav (1+ i) ens))))
     )))

(defcong uav-id-equiv equal (event-for-uav i ens) 1)
(defcong uav-list-equiv equal (event-for-uav i ens) 2)

(defthm event-for-uav-left
  (implies
   (and
    (< (UAV->direction (ith-uav i ens)) 0)
    (case-split (< 0 (uav-id-fix i))))
   (iff (event-for-uav i ens)
        (and (<= (UAV->location (ith-uav i ens))
                 (UAV-left-boundary (ith-uav i ens)))
             (equal (UAV->location (ith-uav (+ -1 (uav-id-fix i)) ens))
                    (UAV->location (ith-uav i ens)))))))

(defthm event-for-uav-right
  (implies
   (and
    (< 0 (UAV->direction (ith-uav i ens)))
    (case-split (< (1+ (uav-id-fix i)) (N))))
   (iff (event-for-uav i ens)
        (and (<= (UAV-right-boundary (ith-uav i ens))
                 (UAV->location (ith-uav i ens)))
             (equal (UAV->location (ith-uav i ens))
                    (UAV->location (ith-uav (+ 1 (uav-id-fix i)) ens)))))))

(defthm event-for-uav-0
  (implies
   (and
    (< (UAV->direction (ith-uav i ens)) 0)
    (= (uav-id-fix i) 0))
   (iff (event-for-uav i ens)
        (equal (UAV->location (ith-uav i ens))
               (left-perimeter-boundary)))))

(defthm event-for-uav-N
  (implies
   (and
    (< 0 (UAV->direction (ith-uav i ens)))
    (= (1+ (uav-id-fix i)) (N)))
   (equal (event-for-uav i ens)
          (equal (UAV->location (ith-uav i ens))
                 (right-perimeter-boundary)))))

(in-theory (disable event-for-uav))

(defthmd test-event-for-uav-rules
  (iff (EVENT-FOR-UAV I ENS)
       (let ((i (uav-id-fix i)))
         (or
          ;; Left-most drone encounters left perimeter
          (and
           (= i 0)
           (< (UAV->direction (ith-uav i ens)) 0)
           (equal (UAV->location (ith-uav i ens))
                  (left-perimeter-boundary)))
          ;; Right-most drone encounters right perimeter
          (and
           (= (1+ i) (N))
           (< 0 (UAV->direction (ith-uav i ens)))
           (equal (UAV->location (ith-uav i ens))
                  (right-perimeter-boundary)))
          ;; Encounter left drone on or beyond left boudary
          (and
           (< 0 i)
           (< (UAV->direction (ith-uav i ens)) 0)
           (<= (UAV->location (ith-uav i ens))
               (UAV-left-boundary (ith-uav i ens)))
           (equal (UAV->location (ith-uav (1- i) ens))
                  (UAV->location (ith-uav i ens)))
           )
          ;; Encounter right drone on or beyond right boundary
          (and
           (< (1+ i) (N))
           (< 0 (UAV->direction (ith-uav i ens)))
           (<= (UAV-right-boundary (ith-uav i ens))
               (UAV->location (ith-uav i ens)))
           (equal (UAV->location (ith-uav i ens))
                  (UAV->location (ith-uav (1+ i) ens))))
          ))))

(defthm degenerate-event-scenario
  (implies
   (and (syntaxp (not (quotep i)))
        (equal (N) 1))
   (equal (EVENT-FOR-UAV I ENS)
          (EVENT-FOR-UAV 0 ENS)))
  :hints (("Goal" :in-theory (enable event-for-uav))))

(defun-sk exists-uav-with-event (ens)
  (declare (type t ens))
  (exists (i) (event-for-uav i ens))
  :strengthen t)

(encapsulate
    ()

  (quant::congruence exists-uav-with-event (ens)
    (exists (i) (event-for-uav i ens))
    :congruences ((ens uav-list-equiv)))

  )

(defthmd not-exists-uav-with-event-implies
  (implies
   (not (exists-uav-with-event ens))
   (not (event-for-uav i ens))))

(in-theory (disable exists-uav-with-event))

;; ===================================================================

;; (def::un cellular-escort-event-for-uav-left (left uav)
;;   (declare (xargs :fty ((uav uav) bool)))
;;   (and (< 0 (UAV->direction left))
;;        (< (UAV-left-boundary uav) (UAV->location uav))
;;        (equal (UAV->location left)
;;               (UAV->location uav))))

;; (def::un cellular-escort-event-for-uav-right (uav right)
;;   (declare (xargs :fty ((uav uav) bool)))
;;   (and (< (UAV->direction right) 0)
;;        (< (UAV->location uav) (UAV-right-boundary uav))
;;        (equal (UAV->location right)
;;               (UAV->location uav))))

;; (def::un cellular-escort-event-for-uav (left uav right)
;;   (declare (xargs :fty ((uav uav uav) bool)))
;;   (if (< (UAV->direction uav) 0)
;;       (and (< 0 (uav->id uav))
;;            (cellular-escort-event-for-uav-left left uav))
;;     (and (< (uav->id uav) (+ -1 (N)))
;;          (cellular-escort-event-for-uav-right uav right))))

(def::und escort-event-for-uav (i ens)
  (declare (xargs :fty ((uav-id uav-list) bool)))
  (let ((uav (ith-uav i ens)))
    (if (< (UAV->direction uav) 0)
        ;; Going left
        (and (< 0 i)
             (let ((left (ith-uav (+ -1 i) ens)))
               (and (< 0 (UAV->direction left))
                    (< (UAV-left-boundary uav) (UAV->location uav))
                    (equal (UAV->location left)
                           (UAV->location uav)))))
      (and (< (1+ i) (N))
           (let ((right (ith-uav (+ 1 i) ens)))
             (and (< (UAV->direction right) 0)
                  (< (UAV->location uav) (UAV-right-boundary uav))
                  (equal (UAV->location right)
                         (UAV->location uav))))))))

;; (defthmd cellularize-escort-event-for-uav
;;   (implies
;;    (SEQUENTIAL-ensemble-p ens)
;;    (equal (escort-event-for-uav i ens)
;;           (cellular-escort-event-for-uav
;;            (ith-uav (1- (uav-id-fix i)) ens)
;;            (ith-uav i ens)
;;            (ith-uav (1+ (uav-id-fix i)) ens))))
;;   :hints (("GOal" :in-theory (enable escort-event-for-uav))))

(defthm not-event-and-escort
  (implies
   (wf-ensemble ens)
   (or (not (escort-event-for-uav i ens))
       (not (event-for-uav i ens))))
  :hints (("Goal" :in-theory (enable escort-event-for-uav
                                     event-for-uav))
          (pattern::hint
           ordering-rule
           ))
  :rule-classes ((:forward-chaining :trigger-terms ((escort-event-for-uav i ens)
                                                    (event-for-uav i ens)))))


(def::und impact-event-for-uav (i ens)
  (declare (xargs :fty ((uav-id uav-list) bool)))
  (or (escort-event-for-uav i ens)
      (event-for-uav i ens)))

(defthm not-impact-event-implies-no-event
  (implies
   (not (impact-event-for-uav i ens))
   (and
    (not (escort-event-for-uav i ens))
    (not (event-for-uav i ens))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("GOal" :in-theory (enable impact-event-for-uav ))))

(in-theory (disable (:rewrite not-impact-event-implies-no-event)))

;; It is impossible to talk about the drone velocity at every time.
;; During an event, the velocity is both + and -

;; Time-to-event

(encapsulate
    ()

  ;;
  ;; I went back and forth on whether it was possible to define a new
  ;; function, (average x y), and prove enough rules about it to
  ;; automate all of our proofs without opening it up.  [I wanted to
  ;; avoid opening it up because it introduces explicit fractional
  ;; terms .. which ACL2 can sometimes struggle with.]  I have had
  ;; problems with that in the past .. and I had problems with it this
  ;; time too.  We ended up with a mixed bag .. sometimes we enable
  ;; the definition and sometimes we don't need to.  You can see here
  ;; some of the messy lemmas we ended up using to try to avoid
  ;; opening things up.  Not pretty. Sigh.
  ;;

  (local (include-arithmetic))

  (def::un average (left right)
    (declare (xargs :fty ((rational rational) rational)))
    (/ (+ left right) 2))

  (defthm average-x-x
    (equal (average x x)
           (rfix x)))

  (defthm positive-average
    (implies
     (and
      (<= 0 x)
      (<= 0 y))
     (<= 0 (average x y)))
    :rule-classes (:rewrite :linear))

  (defthm average-lower-bound
    (implies
     (and
      (rationalp x)
      (rationalp y)
      (<= x y))
     (<= x (average x y)))
    :rule-classes (:rewrite :linear))

  (defthm average-upper-bound
    (implies
     (and
      (rationalp x)
      (rationalp y)
      (<= x y))
     (<= (average x y) y))
    :rule-classes (:rewrite :linear))

  (defthm normalize-difference
    (implies
     (and
      (rationalp x)
      (rationalp y)
      (<= x y))
     (equal (+ y (- (average x y)))
            (+ (average x y) (- x))))
    :hints (("Goal" :do-not '(preprocess))))

  (defthm equal-average-zero
    (implies
     (and
      (rationalp x)
      (rationalp y)
      (<= 0 x)
      (<= 0 y))
     (and (iff (equal (average x y) x)
               (equal y x))
          (iff (equal (average x y) y)
               (equal y x)))))

  (defthm average-common-sum
    (implies
     (and
      (rationalp a) (rationalp x) (rationalp y))
     (equal (average (+ a x)
                     (+ a y))
            (+ a (average x y)))))

  (defthm average-common-difference
    (implies
     (and
      (rationalp a) (rationalp x) (rationalp y))
     (and (equal (average (+ a x)
                          (+ (- a) y))
                 (average x y))
          (equal (average (+ (- a) x)
                          (+ a y))
                 (average x y)))))

  (defthmd double-average-is-just-sum
    (implies
     (and (rationalp x) (rationalp y))
     (and (equal (* -2 (average x y))
                 (- (+ x y)))
          (equal (* 2 (average x y))
                 (+ x y)))))

  (defthm subtracting-average-from-sum-is-just-average
    (implies
     (and (rationalp a) (rationalp b))
     (and (equal (+ a (+ b (- (average a b))))
                 (average a b))
          (equal (+ b (+ a (- (average a b))))
                 (average a b)))))

  (defthmd rewrite-equality-into-just-average
    (implies
     (and
      (rationalp dt)
      (<= (uav->location uavi) (uav->location uavj)))
     (iff (equal (+ (- (uav->location uavi))
                    (* 2 dt))
                 (uav->location uavj))
          (equal dt (average (uav->location uavi) (uav->location uavj))))))

  (defthmd rewrite-equality-into-average
    (implies
     (and
      (rationalp dt)
      (<= (uav->location uavi) (uav->location uavj)))
     (and
      (iff (equal (+ (uav->location uavj)
                     (* -2 dt))
                  (uav->location uavi))
           (equal dt
                  (- (average (uav->location uavi) (uav->location uavj))
                     (uav->location uavi))))
      (iff (equal (+ (uav->location uavi)
                     (* 2 dt))
                  (uav->location uavj))
           (equal dt
                  (- (average (uav->location uavi) (uav->location uavj))
                     (uav->location uavi)))))))

  (defthm equal-average-difference-zero
    (implies
     (and (rationalp x) (rationalp y))
     (and
      (iff (equal (+ (- x) (average x y)) 0)
           (equal x y))
      (iff (equal (+ (- y) (average x y)) 0)
           (equal x y)))))

  (defthmd rewrite-<-into-average
    (implies
     (rationalp dt)
     (iff (< (+ (- dt) (uav->location uavj))
             (+ dt (uav->location uavi)))
          (if (< (uav->location uavi) (uav->location uavj))
              (< (- (uav->location uavj)
                    (average (uav->location uavi)
                             (uav->location uavj)))
                 dt)
            (if (< (uav->location uavj) (uav->location uavi))
                (< (- (uav->location uavj)
                      (average (uav->location uavj)
                               (uav->location uavi)))
                   dt)
              (< 0 dt))))))

  (defthmd reconstruct-average-difference
    (implies
     (and (rationalp x) (rationalp y)
          (<= x y))
     (equal (+ (* 1/2 y)
               (* -1/2 x))
            (- (average x y) x)))
    :rule-classes (:rewrite
                   (:rewrite :corollary
                             (implies
                              (and (rationalp x) (rationalp y)
                                   (<= x y))
                              (equal (+ (* -1/2 x)
                                        (* 1/2 y))
                                     (- (average x y) x))))))



  (defthmd reconstruct-average
    (implies
     (and (rationalp x) (rationalp y))
     (equal (+ (* 1/2 x)
               (* 1/2 y))
            (if (< x y)
                (average x y)
              (if (< y x)
                  (average y x)
                x)))))

  (defthm distributed-<-average
    (implies
     (and
      (rationalp B)(rationalp LI) (rationalp LJ))
     (iff (< (+ LI B) (+ (- LJ) (AVERAGE LJ LI)))
          (< B (- (AVERAGE LJ LI))))))

  (defthmd rewrite-<-into-average-alt-1
    (implies
     (rationalp dt)
     (iff (< (+ (* -2 dt)
                (uav->location uavj))
             (uav->location uavi))
          (if (< (uav->location uavi) (uav->location uavj))
              (< (- (average (uav->location uavi) (uav->location uavj))
                    (uav->location uavi))
                 dt)
            (if (< (uav->location uavj) (uav->location uavi))
                (< (- (average (uav->location uavj) (uav->location uavi))
                      (uav->location uavi))
                   dt)
              (< 0 dt))))))

  (in-theory (enable rewrite-<-into-average
                     rewrite-<-into-average-alt-1
                     double-average-is-just-sum
                     reconstruct-average
                     rewrite-equality-into-just-average
                     reconstruct-average-difference
                     rewrite-equality-into-average))
  (in-theory (disable average))

  )

(defmacro average-theory ()
  `(e/d (average
         location-linear
         right-boundary-is-ordered-linear
         )
        (rewrite-<-into-average
         rewrite-<-into-average-alt-1
         double-average-is-just-sum
         reconstruct-average
         rewrite-equality-into-just-average
         reconstruct-average-difference
         rewrite-equality-into-average
         )))

(defmacro in-average-theory ()
  `(in-theory (average-theory)))

(defmacro average-hint()
  `(and stable-under-simplificationp
        '(:in-theory (average-theory))))

(defmacro with-average-theory (&rest args)
  `(encapsulate
       ()
     (local (in-average-theory))
     ,@args
     ))

(defun tcdr (list)
  (if (not (consp list)) nil
    (if (not (consp (cdr list))) nil
      (cons (car list) (tcdr (cdr list))))))

(defun tcar (list)
  (if (not (consp list)) nil
    (if (not (consp (cdr list))) (car list)
      (tcar (cdr list)))))

(defmacro local-preamble (&rest args)
  `(encapsulate
       ()
     (local
      (progn
        ,@(tcdr args)
        ))
     ,(tcar args)
     ))

;; =====================================================================
;;
;; impending-escort-for-uav tells us that in min-time-to-impact we will
;; engage an escort.  We can predict how long it will be before an
;; event but that it will take multiple steps to get there.
;;
;; =====================================================================
(def::un impending-escort-for-uav (i ens)
  (declare (xargs :fty ((uav-id uav-list) bool)))
  (let ((uav (ith-uav i ens)))
    (if (< (uav->direction uav) 0)
        ;; Moving left
        (if (uav-id-equiv i 0) nil
          (let* ((left (ith-uav (+ -1 i) ens))
                 (avg  (average(UAV->location left) (UAV->location uav))))
            ;; Moving right
            (and (< 0 (uav->direction left))
                 ;; DAG: Why not <= ?
                 ;;
                 ;; This makes this predicate disjoint from
                 ;; impending-event-for-uav
                 ;;
                 (< (UAV-left-boundary uav) avg))))
      ;; Moving right
      (if (uav-id-equiv i (+ -1 (N))) nil
        (let* ((right (ith-uav (+ 1 i) ens))
               (avg   (average (UAV->location uav) (UAV->location right))))
          ;; Moving left
          (and (< (uav->direction right) 0)
               (< avg (UAV-right-boundary uav))))))))

(defthm not-impending-escort-implies-not-escort-event
  (implies
   (WF-ENSEMBLE ENS)
   (or (IMPENDING-Escort-FOR-UAV I ENS)
       (not (escort-event-for-uav i ens))))
  :hints (("Goal" :in-theory (enable IMPENDING-Escort-FOR-UAV escort-event-for-uav))
          (pattern::hint*
           ordering-rule
           escort-condition-implies
           ))
  :rule-classes ((:forward-chaining :trigger-terms ((IMPENDING-Escort-FOR-UAV I ENS)
                                                    (escort-event-for-uav i ens)))))
(in-theory (disable impending-escort-for-uav))

;; =====================================================================
;;
;; impending-event-for-uav tells us that in min-time-to-imact we will have
;; an actual event.
;;
;; =====================================================================
(def::un impending-event-for-uav (i ens)
  (declare (xargs :fty ((uav-id uav-list) bool)))
  (let ((uav (ith-uav i ens)))
    (if (< (uav->direction uav) 0)
        ;; Moving left
        (or (uav-id-equiv i 0)
            (let* ((left (ith-uav (+ -1 i) ens))
                   (avg  (average (UAV->location left) (UAV->location uav))))
              (or (and (< 0 (uav->direction left))
                       (<= avg (UAV-left-boundary uav)))
                  (and (< (uav->direction left) 0)
                       (equal (uav->location uav)
                              (uav->location left))
                       (<= (UAV-left-boundary uav) (uav->location uav))))))
      ;; Moving right
      (or (uav-id-equiv i (+ -1 (N)))
          (let* ((right (ith-uav (+ 1 i) ens))
                 (avg   (average (UAV->location uav) (UAV->location right))))
            (or (and (< (uav->direction right) 0)
                     (<= (UAV-right-boundary uav) avg))
                (and (< 0 (uav->direction right))
                     (equal (uav->location uav)
                            (uav->location right))
                     (<= (uav->location uav) (UAV-right-boundary uav)))))))))

(defthm not-impending-event-implies-not-event
  (implies
   (and
    ;; Gosh it would be nice to get rid of this (?)
    (escort-condition ens)
    (WF-ENSEMBLE ENS))
   (or (IMPENDING-EVENT-FOR-UAV I ENS)
       (not (event-for-uav i ens))))
  :hints (("Goal" :in-theory (enable IMPENDING-EVENT-FOR-UAV event-for-uav))
          (pattern::hint*
           ordering-rule
           escort-condition-implies
           ))
  :rule-classes ((:forward-chaining :trigger-terms ((IMPENDING-EVENT-FOR-UAV I ENS)
                                                    (event-for-uav i ens)))))

(in-theory (disable impending-event-for-uav))

(defthm not-pending-and-impending
  (or (not (impending-escort-for-uav i ens))
      (not (impending-event-for-uav i ens)))
  :hints ('(:in-theory (enable impending-escort-for-uav
                               impending-event-for-uav)))
  :rule-classes ((:forward-chaining :trigger-terms ((impending-escort-for-uav i ens)
                                                    (impending-event-for-uav i ens)))))

;; =====================================================================
;;
;; impending-impact-event-for-uav tells us that we can predict how long it will
;; be before an event.
;;
;; =====================================================================
(def::un impending-impact-event-for-uav (i ens)
  (declare (xargs :fty ((uav-id uav-list) bool)))
  (let ((uav (ith-uav i ens)))
    (if (< (uav->direction uav) 0)
        ;; Moving left
        (or (uav-id-equiv i 0)
            (let* ((left (ith-uav (+ -1 i) ens)))
              (if (< 0 (uav->direction left))
                  ;; Moving right
                  t ;; (<= avg (UAV-left-boundary uav))
                ;; Moving left
                (and (equal (uav->location uav)
                            (uav->location left))
                     (<= (UAV-left-boundary uav) (uav->location uav))))))
      ;; Moving right
      (or (uav-id-equiv i (+ -1 (N)))
          (let* ((right (ith-uav (+ 1 i) ens)))
            (if (< (uav->direction (ith-uav (+ 1 i) ens)) 0)
                ;; Moving left
                t ;; (<= (UAV-right-boundary uav) avg)
              ;; Moving right
              (and (equal (uav->location uav)
                          (uav->location right))
                   (<= (uav->location uav) (UAV-right-boundary uav)))))))))

;; Clearly we should never prove thing directly about this ..
(defthmd imminent-event-reduction
  (iff (impending-impact-event-for-uav i ens)
       (or (impending-event-for-uav i ens)
           (impending-escort-for-uav i ens)))
  :hints ('(:in-theory (enable IMPENDING-ESCORT-FOR-UAV
                               IMPENDING-EVENT-FOR-UAV
                               IMPENDING-IMPACT-EVENT-FOR-UAV))
          (pattern::hint*
           escort-condition-implies
           )))

(in-theory (disable IMPENDING-IMPACT-EVENT-FOR-UAV))

(defthm impending-event-for-uav-implies-impending-impact-event-for-uav
  (implies
   (impending-event-for-uav i ens)
   (impending-impact-event-for-uav i ens))
  :hints (("Goal" :in-theory (enable imminent-event-reduction)))
  :rule-classes (:rewrite :forward-chaining))

(defthm impending-escort-for-uav-implies-impending-impact-event-for-uav
  (implies
   (impending-escort-for-uav i ens)
   (impending-impact-event-for-uav i ens))
  :hints (("Goal" :in-theory (enable imminent-event-reduction)))
  :rule-classes (:rewrite :forward-chaining))

(defthm not-impending-impact-event-implies-not-impact-event
  (implies
   (and
    (WF-ENSEMBLE ENS)
    (escort-condition ens))
   (or (IMPENDING-impact-event-FOR-UAV I ENS)
       (not (impact-event-for-uav i ens))))
  :hints (("Goal" :in-theory (e/d (IMMINENT-EVENT-REDUCTION
                                   impact-event-for-uav)
                                  (IMPENDING-IMPACT-EVENT-FOR-UAV))))
  :rule-classes ((:forward-chaining :trigger-terms ((IMPENDING-impact-event-FOR-UAV i ens)
                                                    (impact-event-for-uav i ens)))))

(defun chasing-neighbor (i ens)
  (let ((i (uav-id-fix i)))
    (if (< (uav->direction (ith-uav i ens)) 0)
        (and (not (uav-id-equiv i 0))
             (< (uav->direction (ith-uav (+ -1 i) ens)) 0)
             (not
              (equal (UAV->location (ith-uav (+ -1 i) ens))
                     (UAV->location (ith-uav i ens)))))
      (and (not (uav-id-equiv i (+ -1 (N))))
           (< 0 (uav->direction (ith-uav (+ 1 i) ens)))
           (not
            (equal (UAV->location (ith-uav i ens))
                   (UAV->location (ith-uav (+ 1 i) ens))))))))

(defthmd chasing-neighbor-is-not-impending-impact-event-for-uav
  (implies
   (and
    (escort-condition ens)
    (wf-ensemble ens)
    )
   (iff (chasing-neighbor i ens)
        (not (impending-impact-event-for-uav i ens))))
  :hints (("Goal" :in-theory (enable event-for-uav
                                     impending-impact-event-for-uav))
          (pattern::hint*
           escort-condition-implies
           location-pinching-rule
           ordering-rule
           )
          ))

(def::pattern-hint expand-chasing-neighbor
  (chasing-neighbor i ens)
  :expand ((chasing-neighbor i ens)))

(in-theory (disable chasing-neighbor impending-impact-event-for-uav))

;; ===================================================================
;; min-time-to-impact-for-uav
;; ===================================================================

(def::un min-time-to-impact-for-uav (i ens)
  (declare (xargs :fty ((uav-id uav-list) rational)))
  (let* ((uav  (ith-uav i ens)))
    (cond
     ;; UAV is moving left ..
     ((< (UAV->direction uav) 0)
      (cond
       ;; Leftmost UAV heading towards left boundary
       ((uav-id-equiv i 0)
        (- (UAV->location uav)
           (left-perimeter-boundary)))
       (t
        (let ((left (ith-uav (+ -1 i) ens)))
          ;; Abnormal condition
          (if (< (UAV->location uav) (UAV->location left)) 0
            (let ((avg (average (UAV->location left) (UAV->location uav) )))
              ;;
              ;; |--------|--------|--------|
              ;;       L  | x   <U
              ;;
              ;; This has to be conditional based on escort.
              ;;
              (cond
               ((and (equal (UAV->location left)
                            (UAV->location uav))
                     (< (UAV->direction left) 0))
                ;; escort condition ..
                (if (<= (uav-left-boundary uav) (uav->location uav))
                    (- (uav->location uav) (uav-left-boundary uav))
                  0))
               (t
                (- (UAV->location uav) avg)))))))))
     ;; UAV is moving right ..
     (t
      (cond
       ((uav-id-equiv i (+ -1 (N)))
        (- (right-perimeter-boundary)
           (UAV->location uav)))
       (t
        (let ((right (ith-uav (+ 1 i) ens)))
          ;; Abnormal conditon
          (if (< (UAV->location right) (UAV->location uav)) 0
            (let ((avg (average (UAV->location uav) (UAV->location right))))
              ;;
              ;; |--------|--------|--------|
              ;;       U> | x    R
              ;;
              (cond
               ((and (equal (UAV->location uav)
                            (UAV->location right))
                     (< 0 (UAV->direction right)))
                ;; escort condition ..
                (if (<= (uav->location uav) (uav-right-boundary uav))
                    (- (uav-right-boundary uav) (uav->location uav))
                  0))
               (t
                (- avg (UAV->location uav)))))))))))))

(def::pattern-hint expand-min-time-to-impact-for-uav
  (:or (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens))
       (< (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))
  :slow t
  :expand ((min-time-to-impact-for-uav i ens)))

(defthm rationalp-min-time-to-impact-for-uav
  (rationalp (min-time-to-impact-for-uav i ens))
  :rule-classes (:type-prescription))

(encapsulate
    ()

  (local (include-arithmetic))

  (defthm nneg-min-time-to-impact-for-uav
    (<= 0 (min-time-to-impact-for-uav i ens))
    :rule-classes (:rewrite :linear))

  )

(defthm min-time-to-impact-fix-uav-id
  (implies
   (not (uav-id-p i))
   (equal (MIN-TIME-TO-IMPACT-FOR-UAV I ENS)
          (MIN-TIME-TO-IMPACT-FOR-UAV 0 ENS))))

(defthm min-time-to-impact-for-uav-upper-bound-left
  (implies
   (< (uav->direction (ith-uav i ens)) 0)
   (<= (min-time-to-impact-for-uav i ens)
       (uav->location (ith-uav i ens))))
  :rule-classes (:rewrite :linear))

(in-theory (disable (:linear min-time-to-impact-for-uav-upper-bound-left)))
(add-priority 1 (:linear min-time-to-impact-for-uav-upper-bound-left))

(defthm min-time-to-impact-for-uav-upper-bound-right
  (implies
   (< 0 (uav->direction (ith-uav i ens)))
   (<= (min-time-to-impact-for-uav i ens) (- (RIGHT-PERIMETER-BOUNDARY) (uav->location (ith-uav i ens)))))
  :rule-classes (:rewrite :linear))

(in-theory (disable (:linear min-time-to-impact-for-uav-upper-bound-right)))
(add-priority 1 (:linear min-time-to-impact-for-uav-upper-bound-right))

(in-theory (disable MIN-TIME-TO-IMPACT-FOR-UAV))

;; ===================================================================

(defun-sk lte-min-time-to-impending-impact-event (dt ens)
  (forall (i)
    (implies (impending-impact-event-for-uav i ens)
             (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens))))
  :strengthen t)

(quant::congruence lte-min-time-to-impending-impact-event (dt ens)
  (forall (i)
    (implies (impending-impact-event-for-uav i ens)
             (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens))))
  :congruences ((dt nnrat-equiv)))

(in-theory (disable lte-min-time-to-impending-impact-event))

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
    (escort-condition ens)
    (wf-ensemble ens)
    (lte-min-time-to-impending-impact-event dt ens))
   (<= (nnrat-fix dt) (min-time-to-impact-for-uav i ens)))
  :hints (("GOal" :in-theory (enable chasing-neighbor-is-not-impending-impact-event-for-uav)))
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

;; DAG - move back
(defthm equal-N-to-bounded-inequality-1
  (implies
   (and
    (syntaxp (quotep c))
    (in-conclusion-check (equal c (N)) :top :negated))
   (iff (equal c (N))
        (and (<= c (N))
             (<= (N) c)))))

(encapsulate
    ()

  (local (include-arithmetic))

  (defthm degenerate-zed
    (implies
     (equal (N) 1)
     (equal (UAV-RIGHT-BOUNDARY (ITH-UAV 0 ENS))
            (right-perimeter-boundary)))
    :hints (("Goal" :in-theory (enable SEGMENT-LENGTH
                                       RIGHT-PERIMETER-BOUNDARY
                                       UAV-LEFT-BOUNDARY
                                       UAV-RIGHT-BOUNDARY
                                       ith-uav))))

  )

(encapsulate
    ()


  (local
   (defthm positive-min-time-to-impact-helper
     (implies
      (and
       (escort-condition ens)
       ;;(homogenous-escort-direction ens)
       (wf-ensemble ens)
       ;;We need something stronger .. no events for anyone ..
       (not (event-for-uav i ens))
       (implies
        (< 0 (uav-id-fix i))
        (not (event-for-uav (1- (uav-id-fix i)) ens)))
       (implies
        (< (uav-id-fix i) (+ -1 (N)))
        (not (event-for-uav (1+ (uav-id-fix i)) ens)))
       )
      (< 0 (min-time-to-impact-for-uav i ens)))
     :hints (("Goal" :in-theory (enable
                                        MIN-TIME-TO-IMPACT-FOR-UAV
                                        equal-uav-id-fix-1-to-uav-id-equiv))
             (pattern::hint
              (not (equal (UAV->DIRECTION uav) 1))
              :restrict ((negate-direction-equality ((uav uav))))
              :in-theory (enable negate-direction-equality
                                 equal-uav-id-fix-1-to-uav-id-equiv)
              :name  negate-direction-equality
              )
             (pattern::hint*
              escort-condition-implies
              shared-boundary
              ordering-rule
              location-pinching-rule
              )
             (pattern::hint
              (not (equal (n) 2))
              :cases ((or (equal (n) 1)
                          (< 2 (n)))))
             (pattern::hint
              (:and
               (not (event-for-uav i ens))
               (:syntaxp (or (quotep i) (symbolp i))))
              :expand ((event-for-uav i ens)))

             (pattern::hint
              (not (event-for-uav i ens))
              :expand ((event-for-uav i ens)))

             )))

  (defthm positive-min-time-to-impact-for-uav
     (implies
      (and
       (not (exists-uav-with-event ens))
       (escort-condition ens)
       (wf-ensemble ens))
      (< 0 (min-time-to-impact-for-uav i ens)))
     :rule-classes (:linear :rewrite)
     :hints (("Goal" :in-theory nil
              :use (positive-min-time-to-impact-helper))
             (pattern::hint
              (event-for-uav i ens)
              :use ((:instance not-exists-uav-with-event-implies
                               (i i))))
              ))

  )

(defthm force-equal-dt-rewrite
  (implies
   (in-conclusion-check (equal (nnrat-fix dt) z) :top t)
   (iff (equal (nnrat-fix dt) z)
        (hide (rewrite-equiv (equal (nnrat-fix dt) z)))))
  :hints (("Goal" :expand (:free (x) (hide x)))))

(defthm nnrat-p-difference
  (implies
   (and
    (nnrat-p x)
    (nnrat-p y)
    (force (<= y x)))
   (nnrat-p (+ x (- y))))
  :hints (("Goal" :in-theory (enable nnrat-p))))

;; (defthm nnrat-p-min-time-to-event-for-uav
;;   (nnrat-p (min-time-to-event-for-uav i ens))
;;   :rule-classes (:rewrite
;;                  (:forward-chaining :trigger-terms ((min-time-to-event-for-uav i ens)))))

(defthm nnrat-p-min-time-to-impact-for-uav
  (nnrat-p (min-time-to-impact-for-uav i ens))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((min-time-to-impact-for-uav i ens)))))

;; In the direction this guy is moving, either it is the most
;; extreme UAV or there is another uav with an impending event.

;; The current UAV is facing right but does not have an
;; impending event (which means the next UAV is facing
;; right as well).  We need to find the first UAV facing
;; left -or- the UAV on the end.
(encapsulate
    (
     ((impending-event-index *) => *)
     )

  (local
   (encapsulate
       ()

     (defun next-positive-index (i ens)
       (declare (xargs :normalize nil))
       (if (< 0 (UAV->direction (ith-uav i ens))) (uav-id-fix i)
         (if (not (uav-id-p i)) -1
           (if (zp i) -1
             (next-positive-index (1- (uav-id-fix i)) ens)))))

     (defthm next-positive-index-is-smaller
       (<= (next-positive-index i ens) (uav-id-fix i))
       :rule-classes (:rewrite :linear))

     (defthm uav-id-p-next-positive-index
       (implies
        (< 0 (UAV->direction (ith-uav 0 ens)))
        (uav-id-p (next-positive-index i ens)))
       :rule-classes (:rewrite
                      (:forward-chaining :trigger-terms ((next-positive-index i ens)))))

     (defthm existential-uav-id-p-next-positive-index
       (implies
        (and
         (equal (UAV->direction (ith-uav k ens)) 1)
         (<= (uav-id-fix k) (uav-id-fix i)))
        (uav-id-p (next-positive-index i ens))))

     (defthmd converging-uavs
       (implies
        (and
         (< (UAV->direction (ith-uav (+ 1 (uav-id-fix i)) ens)) 0)
         (uav-id-p (next-positive-index i ens)))
        (and (< 0 (UAV->direction (ith-uav (next-positive-index i ens) ens)))
             (< (UAV->direction (ith-uav (+ 1 (next-positive-index i ens)) ens)) 0))))

     (defthm next-positive-index-lower-bound
       (implies
        (and
         (<= (uav-id-fix k) (uav-id-fix i))
         (< 0 (UAV->direction (ith-uav k ens))))
        (<= (uav-id-fix k) (next-positive-index i ens)))
       :rule-classes (:rewrite :linear))

     (defthm sigh
       (implies
        (uav-id-p x)
        (acl2-numberp x)))

     (defthm linear-what-we-want-to-say-about-ordered-location-list-p
       (implies
        (and
         (ordered-location-list-p list)
         (equal (len list) (N))
         (<= (uav-id-fix i) (uav-id-fix j)))
        (<= (uav->location (ith-uav i list))
            (uav->location (ith-uav j list))))
       :rule-classes (:linear)
       :hints (("Goal" :in-theory (enable what-we-want-to-say-about-ordered-location-list-p))))

     (defthmd difference-is-non-negative
       (implies
        (and
         (ordered-location-list-p ens)
         (equal (len ens) (N))
         (<= (+ 1 (uav-id-fix i)) (+ -1 (N)))
         (< (UAV->direction (ith-uav (+ 1 (uav-id-fix i)) ens)) 0)
         (< 0 (UAV->direction (ith-uav k ens)))
         (<= (uav-id-fix k) (uav-id-fix i)))
        (and
         (<= (UAV->location (ith-uav k ens))
             (UAV->location (ith-uav (+ 1 (uav-id-fix i)) ens)))
         (<= (UAV->location (ith-uav k ens))
             (UAV->location (ith-uav (next-positive-index i ens) ens)))
         (<= (UAV->location (ith-uav (next-positive-index i ens) ens))
             (UAV->location (ith-uav (+ 1 (next-positive-index i ens)) ens)))
         (<= (UAV->location (ith-uav (+ 1 (next-positive-index i ens)) ens))
             (UAV->location (ith-uav (+ 1 (uav-id-fix i)) ens)))))
       :hints (("Goal" :do-not-induct t
                :in-theory (e/d ()
                                (next-positive-index-is-smaller))
                :use (next-positive-index-is-smaller
                      (:instance what-we-want-to-say-about-ordered-location-list-p
                                 (list ens)
                                 (i k)
                                 (j (+ 1 (uav-id-fix i))))
                      (:instance what-we-want-to-say-about-ordered-location-list-p
                                 (list ens)
                                 (i k)
                                 (j (next-positive-index i ens)))
                      (:instance what-we-want-to-say-about-ordered-location-list-p
                                 (list ens)
                                 (i (next-positive-index i ens))
                                 (j (+ 1 (next-positive-index i ens))))
                      (:instance what-we-want-to-say-about-ordered-location-list-p
                                 (list ens)
                                 (i (+ 1 (next-positive-index i ens)))
                                 (j (+ 1 (uav-id-fix i))))))
               (and stable-under-simplificationp
                    '(:in-theory (enable uav-id-fix uav-id-p)))
               ))

     ;;
     ;; DAG: You are looking for a stronger inequality
     ;;
     (defthm the-difference-between-two-opposing-uavs-is-gte-the-minimum-difference
       (implies
        (and
         (ordered-location-list-p ens)
         (equal (len ens) (N))
         (<= (+ 1 (uav-id-fix i)) (+ -1 (N)))
         (< (UAV->direction (ith-uav (+ 1 (uav-id-fix i)) ens)) 0)
         (< 0 (UAV->direction (ith-uav k ens)))
         (<= (uav-id-fix k) (uav-id-fix i)))
        (<= (- (UAV->location (ith-uav (+ 1 (next-positive-index i ens)) ens))
               (UAV->location (ith-uav (next-positive-index i ens) ens)))
            (- (UAV->location (ith-uav (+ 1 (uav-id-fix i)) ens))
               (UAV->location (ith-uav k ens)))))
       :hints (("Goal" :do-not-induct t
                :use difference-is-non-negative)))

     (defun impending-event-index (ens)
       (if (< 0 (UAV->direction (ith-uav (+ -1 (N)) ens)))
           (+ -1 (N))
         (if (< (UAV->direction (ith-uav 0 ens)) 0)
             0
           (next-positive-index (+ -2 (N)) ens))))

     (defthm pending-event-for-uav-pending-event-index-helper
       (impending-impact-event-for-uav (impending-event-index ens) ens)
       :hints (("Subgoal 3" :in-theory (enable IMPENDING-IMPACT-EVENT-FOR-UAV))
               ("Subgoal 1" :in-theory (enable IMPENDING-IMPACT-EVENT-FOR-UAV))
               ("Subgoal 2" :in-theory (enable natp
                                               uav-id-p
                                               uav-id-fix)
                :use (:instance converging-uavs
                                (i (+ -2 (N)))))
               (and stable-under-simplificationp
                    '(:in-theory (enable IMPENDING-IMPACT-EVENT-FOR-UAV)))
               ))

     ))

  (def::signature impending-event-index (t) uav-id-p)

  (local (in-theory (disable impending-event-index)))

  (defthm pending-event-for-uav-pending-event-index
    (impending-impact-event-for-uav (impending-event-index ens) ens))

  )

;; break
;;

(def::un largest-impending-event-index (i ens)
  (declare (xargs :fty ((uav-id uav-list) uav-id)
                  :measure (uav-id-fix i)))
  (if (zp i) i
    (if (impending-impact-event-for-uav i ens) i
      (largest-impending-event-index (1- i) ens))))

(defthm largest-impending-event-index-property
  (implies
   (and
    (impending-impact-event-for-uav k ens)
    (<= (uav-id-fix k) (uav-id-fix i)))
   (<= (uav-id-fix k) (largest-impending-event-index i ens))))

(def::un smallest-impending-dt (i ens)
  (declare (xargs :measure (uav-id-fix i)
                  :fty ((uav-id uav-list) uav-id)))
  (if (zp i) i
    (let ((j (smallest-impending-dt (1- i) ens)))
      (if (not (impending-impact-event-for-uav j ens)) i
        (if (and (impending-impact-event-for-uav i ens)
                 (< (min-time-to-impact-for-uav i ens)
                    (min-time-to-impact-for-uav j ens)))
            i
          j)))))

(defthmd smallest-impending-dt-is-smallest
  (implies
   (and
    (impending-impact-event-for-uav k ens)
    (<= (uav-id-fix k) (uav-id-fix i)))
   (and
    (impending-impact-event-for-uav (smallest-impending-dt i ens) ens)
    (<= (min-time-to-impact-for-uav (smallest-impending-dt i ens) ens)
        (min-time-to-impact-for-uav k ens))))
  :hints (("Goal" :do-not-induct t
           :induct (smallest-impending-dt i ens))))

(def::und smallest-impending-dt-index (ens)
  (delare (xargs :fty ((uav-list) uav-id)))
  (let ((i (largest-impending-event-index (+ -1 (N)) ens)))
    (smallest-impending-dt i ens)))

(defthm smallest-impending-dt-index-properties
  (and (impending-impact-event-for-uav (smallest-impending-dt-index ens) ens)
       (implies
        (impending-impact-event-for-uav k ens)
        (<= (min-time-to-impact-for-uav (smallest-impending-dt-index ens) ens)
            (min-time-to-impact-for-uav k ens))))
  :rule-classes ((:rewrite :corollary
                           (impending-impact-event-for-uav (smallest-impending-dt-index ens) ens))
                 (:linear :corollary
                          (implies
                           (impending-impact-event-for-uav k ens)
                           (<= (min-time-to-impact-for-uav (smallest-impending-dt-index ens) ens)
                               (min-time-to-impact-for-uav k ens)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable smallest-impending-dt-index)
           :use ((:instance largest-impending-event-index-property
                            (k (impending-event-index ens))
                            (i (+ -1 (N))))
                 (:instance smallest-impending-dt-is-smallest
                            (k (impending-event-index ens))
                            (i (largest-impending-event-index (+ -1 (n)) ens)))
                 (:instance smallest-impending-dt-is-smallest
                            (i (largest-impending-event-index (+ -1 (n)) ens)))))))


(in-theory (disable smallest-impending-dt-index))

(def::und always-smallest-min-time-to-impending-impact (ens)
  (declare (xargs :fty ((uav-list) nnrat)))
  (let ((i (smallest-impending-dt-index ens)))
    (min-time-to-impact-for-uav i ens)))

(defthm always-smallest-min-time-to-impending-impact-is-smallest
  (implies
   (impending-impact-event-for-uav k ens)
   (<= (always-smallest-min-time-to-impending-impact ens)
       (min-time-to-impact-for-uav k ens)))
  :hints (("Goal" :in-theory (enable always-smallest-min-time-to-impending-impact)))
  :rule-classes ((:linear :trigger-terms ((min-time-to-impact-for-uav k ens)))))

(defthm lte-always-smallest-min-time-to-impending-impact-implies-lte-min-time-to-impending-impact-event
  (implies
   (and
    (<= (nnrat-fix dt) (always-smallest-min-time-to-impending-impact ens))
    (wf-ensemble ens))
   (lte-min-time-to-impending-impact-event dt ens))
  :hints (("Goal" :in-theory (enable lte-min-time-to-impending-impact-event)
           :do-not-induct t))
  :rule-classes (:rewrite
                 :forward-chaining
                 (:forward-chaining
                  :corollary (implies
                              (and
                               (< (nnrat-fix dt) (always-smallest-min-time-to-impending-impact ens))
                               (wf-ensemble ens))
                              (lte-min-time-to-impending-impact-event dt ens)))))

(defthm lte-min-time-to-impending-impact-event-implies-lt-always-smallest-min-time-to-impending-impact
  (implies
   (and
    (lte-min-time-to-impending-impact-event dt ens)
    (wf-ensemble ens))
   (<= (nnrat-fix dt) (always-smallest-min-time-to-impending-impact ens)))
  :hints (("GOal" :in-theory (enable ALWAYS-SMALLEST-MIN-TIME-TO-IMPENDING-IMPACT)))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable SMALLEST-IMPENDING-DT-INDEX-PROPERTIES))

(encapsulate
    ()

  (local (include-arithmetic))

  (local
   (encapsulate
       (
        ((next-impending-event-right * *) => *)
        )


     (local
      (encapsulate
          ()

        (defun next-negative-direction-right (i ens)
          (declare (xargs :measure (- (N) (uav-id-fix i))))
          (let* ((i (uav-id-fix i))
                 (j (+ 1 i)))
            (if (<= (N) j) i
              (if (< (uav->direction (ith-uav j ens)) 0) j
                (next-negative-direction-right j ens)))))

        (defthm next-negative-direction-right-lower-bound
          (<= (uav-id-fix i) (next-negative-direction-right i ens))
          :rule-classes (:linear))

        (defthmd next-negative-direction-right-is-usually-bigger
          (iff (< (uav-id-fix i) (next-negative-direction-right i ens))
               (not (equal (uav-id-fix i) (+ -1 (N))))))

        (def::signature next-negative-direction-right (t t) uav-id-p)

        (defthmd next-negative-direction-right-direction
          (implies
           (< 0 (uav->direction (ith-uav i ens)))
           (if (< 0 (uav->direction (ith-uav (next-negative-direction-right i ens) ens)))
               (equal (next-negative-direction-right i ens) (+ -1 (N)))
             (and (< (uav->direction (ith-uav (next-negative-direction-right i ens) ens)) 0)
                  (< 0 (uav->direction (ith-uav (+ -1 (next-negative-direction-right i ens)) ens)))))))

        (defun next-impending-event-right (i ens)
          (let ((j (next-negative-direction-right i ens)))
            (if (impending-event-for-uav j ens) j
              (+ -1 j))))

        (defthm greater-than-implies-not-zero
          (implies
           (and
            (uav-id-p x)
            (< (uav-id-fix i) x))
           (not (UAV-ID-EQUIV x 0)))
          :hints (("GOal" :in-theory (e/d (uav-id-equiv
                                           uav-id-fix
                                           uav-id-p
                                           )
                                          (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV)))))

        ))

     (local
      (in-theory (disable IMPENDING-EVENT-FOR-UAV
                          ;;OPEN-MIN-TIME-TO-IMPACT-FOR-UAV
                          NEXT-NEGATIVE-DIRECTION-RIGHT
                          (NEXT-NEGATIVE-DIRECTION-RIGHT))))

     (defthm min-time-to-impact-for-uav-next-impending-event-right-upper-bound
       (implies
        (and
         (wf-ensemble ens)
         ;;(escort-condition ens)
         (< 0 (uav->direction (ith-uav i ens))))
        ;; If it is positive, we are done.
        ;; if it is negative, we must think.
        (<= (min-time-to-impact-for-uav (next-impending-event-right i ens) ens)
            (- (right-perimeter-boundary)
               (uav->location (ith-uav i ens)))))
       :rule-classes :linear
       :hints (("Goal" :do-not-induct t
                :do-not '(generalize eliminate-destructors fertilize)
                :in-theory (e/d () (next-impending-event-right))
                :cases ((< (uav->direction (ith-uav (next-impending-event-right i ens) ens)) 0)))
               (and stable-under-simplificationp
                    '(:use (next-negative-direction-right-is-usually-bigger
                            next-negative-direction-right-direction
                            (:instance what-we-want-to-say-about-ordered-location-list-p
                                       (list ens)
                                       (i i)
                                       (j (+ -1 (N)))))
                           :in-theory (e/d (next-impending-event-right)
                                           )))
               (pattern::hint
                (not (IMPENDING-EVENT-FOR-UAV (+ -1 (N)) ENS))
                :in-theory (enable IMPENDING-EVENT-FOR-UAV))
               (pattern::hint
                (:and
                 (UAV-ID-EQUIV I (+ -1 (N)))
                 (:term (NEXT-NEGATIVE-DIRECTION-RIGHT I ENS)))
                :expand ((NEXT-NEGATIVE-DIRECTION-RIGHT I ENS)))
               (and stable-under-simplificationp
                    '(:in-theory (e/d (MIN-TIME-TO-IMPACT-FOR-UAV)
                                      nil)
                                 :use ((:instance what-we-want-to-say-about-ordered-location-list-p
                                                  (list ens)
                                                  (i (+ -1 (next-impending-event-right i ens)))
                                                  (j (next-impending-event-right i ens)))
                                       (:instance what-we-want-to-say-about-ordered-location-list-p
                                                  (list ens)
                                                  (i i)
                                                  (j (+ -1 (next-impending-event-right i ens))))
                                       )))
               ))

     (defthm impending-event-next-negative-direction-right
       (implies
        (and
         (wf-ensemble ens)
         (< 0 (uav->direction (ith-uav i ens))))
        (and (<= (uav-id-fix i) (uav-id-fix (next-impending-event-right i ens)))
             (impending-impact-event-for-uav (next-impending-event-right i ens) ens)))
       :hints (("Goal" :do-not-induct t
                :use (next-negative-direction-right-is-usually-bigger
                      next-negative-direction-right-direction))
               (pattern::hint
                (:and
                 (UAV-ID-EQUIV I (+ -1 (N)))
                 (:term (NEXT-NEGATIVE-DIRECTION-RIGHT i ens)))
                :expand ((NEXT-NEGATIVE-DIRECTION-RIGHT i ens)))
               (and stable-under-simplificationp
                    '(:in-theory (enable IMPENDING-IMPACT-EVENT-FOR-UAV
                                         IMPENDING-EVENT-FOR-UAV)))
               ))

     ))

  (defthm lte-min-time-to-impending-impact-event-bounded-by-location-right
    (implies
     (and
      (< 0 (uav->direction (ith-uav i ens)))
      (lte-min-time-to-impending-impact-event dt ens)
      (wf-ensemble ens))
     (<= (nnrat-fix dt)
         (- (right-perimeter-boundary)
            (uav->location (ith-uav i ens)))))
    :rule-classes ((:linear :trigger-terms ((uav->location (ith-uav i ens))))
                   :rewrite)
    :hints (("Goal" :in-theory (e/d ()
                                    (lte-min-time-to-impending-impact-event-implication-1
                                     wf-ensemble
                                     IMPENDING-IMPACT-EVENT-FOR-UAV
                                     )
                                    )
             :use ((:instance lte-min-time-to-impending-impact-event-implication-1
                              (i (uav-id-fix (next-impending-event-right i ens))))))))


  )

;; (defun bind-smallest-dt-in-clause (clause)
;;   (if (not (consp clause)) nil
;;     (let ((entry (car clause)))
;;       (case-match entry
;;         (('not ('< ('nnrat-fix dt) ('always-smallest-min-time-to-impending-impact &)))
;;          (acons 'dt dt nil))
;;         (& (bind-smallest-dt-in-clause (cdr clause)))))))

;; (set-state-ok t)
;; (defun find-smallest-dt-fn (mfc state)
;;   (declare (xargs :mode :program)
;;            (ignore state))
;;   (let ((clause (mfc-clause mfc)))
;;     (bind-smallest-dt-in-clause clause)))

;; (defmacro find-smallest-dt ()
;;   `(find-smallest-dt-fn mfc state))

(encapsulate
    ()

  (local
   (encapsulate
       (
        ((next-impending-event-left * *) => *)
        )

     ;; DAG -- this is really annoying (!)
     ;; (The proof broke when I added these rules)
     (local (in-theory (disable NATP-UAV-ID-FIX rationalp-location)))

     (local
      (encapsulate
          ()

        (defun next-negative-direction-left (i ens)
          (declare (xargs :measure (uav-id-fix i)))
          (let* ((i (uav-id-fix i))
                 (j (+ -1 i)))
            (if (< j 0) i
              (if (< 0 (uav->direction (ith-uav j ens))) j
                (next-negative-direction-left j ens)))))

        (defthm next-negative-direction-left-upper-bound
          (<= (next-negative-direction-left i ens)
              (uav-id-fix i))
          :rule-classes :linear)

        (local (in-theory (disable  LESS-THAN-ZERO-TO-UAV-ID-EQUIV)))

        (defthmd next-negative-direction-left-is-usually-bigger
          (iff (< (next-negative-direction-left i ens) (uav-id-fix i))
               (not (equal (uav-id-fix i) 0))))
        (def::signature next-negative-direction-left (t t) uav-id-p)

        (defthmd next-negative-direction-left-direction
          (implies
           (< (uav->direction (ith-uav i ens)) 0)
           (if (< (uav->direction (ith-uav (next-negative-direction-left i ens) ens)) 0)
               (equal (next-negative-direction-left i ens) 0)
             (and (< 0 (uav->direction (ith-uav (next-negative-direction-left i ens) ens)))
                  (< (uav->direction (ith-uav (+ 1 (next-negative-direction-left i ens)) ens)) 0)))))

        (defun next-impending-event-left (i ens)
          (let ((j (next-negative-direction-left i ens)))
            (if (impending-event-for-uav j ens) j
              (+ 1 j))))

        (defthm less-tham-implies-not-N-1
          (implies
           (and
            (uav-id-p x)
            (< x (uav-id-fix i)))
           (not (UAV-ID-EQUIV x (+ -1 (N)))))
          :hints (("GOal" :in-theory (e/d (uav-id-equiv
                                           uav-id-fix
                                           uav-id-p
                                           )
                                          (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV)))))

        ))

     (local
      (in-theory (disable IMPENDING-EVENT-FOR-UAV
                          ;;OPEN-MIN-TIME-TO-IMPACT-FOR-UAV
                          NEXT-NEGATIVE-DIRECTION-LEFT
                          (NEXT-NEGATIVE-DIRECTION-LEFT))))

     (local
      (defthm reorg
        (implies
         (uav-id-p x)
         (iff (equal (N) (+ 2 x))
              (and (not (equal (N) 1))
                   (uav-id-equiv x (+ (N) -2)))))
        :hints (("GOal" :in-theory (e/d (uav-id-equiv
                                         uav-id-fix
                                         uav-id-p
                                         )
                                        (EQUAL-UAV-ID-FIX-1-TO-UAV-ID-EQUIV))))))

     (defthm min-time-to-impact-for-uav-next-impending-event-left-upper-bound
       (implies
        (and
         (wf-ensemble ens)
         ;;(escort-condition ens)
         (< (uav->direction (ith-uav i ens)) 0))
        (<= (min-time-to-impact-for-uav (next-impending-event-left i ens) ens)
            (- (uav->location (ith-uav i ens))
               (LEFT-PERIMETER-BOUNDARY))))
       :rule-classes (:linear)
       :hints (("Goal" :do-not-induct t
                :do-not '(generalize eliminate-destructors fertilize)
                :in-theory (e/d ()
                                (next-impending-event-left))
                :cases ((< (uav->direction (ith-uav (next-impending-event-left i ens) ens)) 0)))
               (and stable-under-simplificationp
                    '(:use (next-negative-direction-left-is-usually-bigger
                            next-negative-direction-left-direction
                            (:instance what-we-want-to-say-about-ordered-location-list-p
                                       (list ens)
                                       (i 0)
                                       (j i)))
                           :in-theory (e/d (next-impending-event-left)
                                           )))
               (pattern::hint
                (not (IMPENDING-EVENT-FOR-UAV 0 ENS))
                :in-theory (enable IMPENDING-EVENT-FOR-UAV))
               (pattern::hint
                (UAV-ID-EQUIV I 0)
                :in-theory (e/d (NEXT-NEGATIVE-DIRECTION-LEFT)
                                nil))
               (and stable-under-simplificationp
                    '(:in-theory (e/d (MIN-TIME-TO-IMPACT-FOR-UAV)
                                      nil)
                                 :use ((:instance what-we-want-to-say-about-ordered-location-list-p
                                                  (list ens)
                                                  (i (next-impending-event-left i ens))
                                                  (j (+ 1 (next-impending-event-left i ens))))
                                       (:instance what-we-want-to-say-about-ordered-location-list-p
                                                  (list ens)
                                                  (i (+ 1 (next-impending-event-left i ens)))
                                                  (j i))
                                       )))
               (and stable-under-simplificationp
                    '(:expand ((NEXT-NEGATIVE-DIRECTION-LEFT I ENS)
                               (IMPENDING-EVENT-FOR-UAV (+ -2 (N)) ENS))))
               ))

     (defthm impending-event-next-negative-direction-left
       (implies
        (and
         (wf-ensemble ens)
         (< (uav->direction (ith-uav i ens)) 0))
        (and (<= (uav-id-fix (next-impending-event-left i ens)) (uav-id-fix i))
             (impending-impact-event-for-uav (next-impending-event-left i ens) ens)))
       :hints (("Goal" :do-not-induct t
                :use (next-negative-direction-left-is-usually-bigger
                      next-negative-direction-left-direction))
               (pattern::hint
                (UAV-ID-EQUIV I 0)
                :in-theory (e/d (NEXT-NEGATIVE-DIRECTION-LEFT)
                                nil))
               (and stable-under-simplificationp
                    '(:in-theory (enable IMPENDING-IMPACT-EVENT-FOR-UAV
                                         IMPENDING-EVENT-FOR-UAV)))
               ))

     ))

  (defthm lte-min-time-to-impending-impact-event-bounded-by-location-left
    (implies
     (and
      (< (uav->direction (ith-uav i ens)) 0)
      (lte-min-time-to-impending-impact-event dt ens)
      (wf-ensemble ens))
     (<= (nnrat-fix dt)
         (- (uav->location (ith-uav i ens))
            (left-perimeter-boundary))))
    :rule-classes ((:linear :trigger-terms ((uav->location (ith-uav i ens))))
                   :rewrite)
    :hints (("Goal" :in-theory (e/d ()
                                    (lte-min-time-to-impending-impact-event-implication-1
                                     wf-ensemble
                                     IMPENDING-IMPACT-EVENT-FOR-UAV
                                     )
                                    )
             :use ((:instance lte-min-time-to-impending-impact-event-implication-1
                              (i (uav-id-fix (next-impending-event-left i ens))))))))


  )
