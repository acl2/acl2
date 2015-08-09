#|$ACL2s-Preamble$;
;; Julien Schmaltz
;; File: circuit-scheduling.lisp
;; here we define a function that realises a circuit switching
;; technique, we prove it correct and we prove that it is a valid
;; instance of the scheduling function of GeNoC.
;; Revised: Nov 13th 2005, JS

(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")
(include-book "../../../generic-modules/GeNoC-scheduling")
(include-book "intersect")
(include-book "../../ntkstate/simple/simple")
(include-book "../../synchronization/circuit-global/circuit")
(include-book "../../genoc/simple-ct-global/trlst-equal")

;;-----------------------------------------------------
;;
;; DEFINITION OF THE CIRCUIT SWITCHED SCHEDULING POLICY
;;
;;-----------------------------------------------------


(defun test_prev_routes (r? prev)
  ;; function that returns a route that uses nodes
  ;; that are not in prev or returns nil if there is no
  ;; such route.
  (cond ((endp r?)
         nil)
        ((endp prev)
         t)
        ((no_intersectp r? (car prev))
         (test_prev_routes r? (cdr prev)))
        (t
         nil)))

(defun ct-scheduler (TrLst Scheduled Arrived prev measureAcc ntkstate)
  (if (endp trlst)
    (mv (rev Scheduled) (rev Arrived) (rev measureAcc) ntkstate)
    (let ((v (car TrLst)))
      (mv-let (newntkstate r?)
              (inst-test_routes ntkstate v)
              (if (test_prev_routes r? prev)
                ;; if there is a possible route, then remove
                ;; it and add it to to prev
                (ct-scheduler (cdr TrLst)
                              Scheduled
                              (cons v Arrived)
                              (cons r? prev)
                              (cons 0 measureAcc)
                              newntkstate)
                ;; otherwise the transaction is delayed
                (ct-scheduler (cdr TrLst)
                              (cons v Scheduled)
                              Arrived
                              prev
                              (cons (len (car (RoutesV (car TrLst)))) measureAcc)
                              newntkstate))))))

;; returns t if there's no route possible in
;; the current ntkstate
(defun no-good-routes (TrLst ntkstate)
  (if (endp trlst)
    t
    (mv-let (newntkstate r?)
            (inst-test_routes ntkstate (car trlst))
            (if (not r?)
              (no-good-routes (cdr TrLst) newntkstate)
              nil))))

(defun sum-of-lst (lst)
  (if (endp lst)
    0
    (nfix (+ (car lst) (sum-of-lst (cdr lst))))))

;; returns a list of the lengths of the routes of the travels in TrLst
(defun RouteLengths-TrLst (TrLst)
  (if (endp TrLst)
    nil
    (cons (len (car (RoutesV (car TrLst)))) (RouteLengths-TrLst (cdr TrLst)))))
; the measure is a list of lengths of the routes
(defun ct-initial-measure (trlst nodeset ntkstate order)
  (declare (ignore nodeset ntkstate order))
  (sum-of-lst (RouteLengths-TrLst trlst)))
(defun ct-legal-measure (measure TrLst NodeSet ntkstate order)
  (declare (ignore nodeset ntkstate order))
  (equal measure (sum-of-lst (RouteLengths-Trlst trlst))))
(defun ct-get_next_priority (x)
  x)

; circuit scheduling assume that:
; 1.) the TrLst is not empty
; 2.) there is at least one route possible
; 3.) the current measure is a list with the lengths of the current routes
(defun ct-scheduling-assumptions (TrLst NodeSet ntkstate order)
  (declare (ignore NodeSet order))
 ; (and (not (endp TrLst))
       (not (no-good-routes TrLst ntkstate)))


;Scheduling:
; IN:  List of Travels
;      Measure
;      NodeSet
;      ntkstate
;     order
; OUT: List of En Route TMs
;      List of Arrived Travels
;      Valid networkstate
(defun ct-scheduling (TrLst NodeSet ntkstate order)
  (if (not (ct-scheduling-assumptions TrLst NodeSet ntkstate order))
    (mv (totmissives TrLst) nil nil ntkstate)
    ; otherwise: schedule the travels
    (mv-let (newTrlst Arrived newmeasure newntkstate)
            (ct-scheduler TrLst nil nil nil nil ntkstate)
            (mv (totmissives newTrlst)
                Arrived
                (sum-of-lst newmeasure)
                (update-ntkstate newntkstate newtrlst)))))

;-------------------------------------
; the instantiations used in this file
;------------------------------------
(defmacro inst-scheduling (TrLst NodeSet ntkstate order)
         (list 'ct-scheduling TrLst NodeSet ntkstate order))
(defmacro inst-scheduling-assumptions (TrLst NodeSet ntkstate order)
         (list 'ct-scheduling-assumptions TrLst NodeSet ntkstate order))
(defmacro inst-legal-measure (measure TrLst nodeset ntkstate order)
         (list 'ct-legal-measure measure TrLst nodeset ntkstate order))
(defmacro inst-initial-measure (TrLst nodeset ntkstate order)
         (list 'ct-initial-measure TrLst nodeset ntkstate order))
(defmacro inst-get_next_priority (order)
         (list 'ct-get_next_priority order))


;-----------------------------------------------
;
; PROVING COMPLIANCE TO GENERIC SCHEDULING
;
;
; The proof is completely equal to the proof
; of packet-scheduling.
;
;-----------------------------------------------

;-------------------------------
; non-tail recursive functions
; for ct-scheduler
;-------------------------------
(defun ct-scheduler-nt-car (TrLst prev ntkstate)
  ;; car is the first output and corresponds to the scheduled travels
  (if (endp TrLst)
    nil
    (let ((v (car TrLst)))
      (mv-let (newntkstate r?)
              (inst-test_routes ntkstate v)
              (if (test_prev_routes r? prev)
                  (ct-scheduler-nt-car (cdr TrLst) (cons r? prev)
                                       newntkstate)
                  (cons v (ct-scheduler-nt-car (cdr TrLst) prev
                                               newntkstate)))))))
(defthm ct-scheduler-nt-equal
  (equal (car (ct-scheduler TrLst Scheduled ArrivedAcc prev measureAcc ntkstate))
         (append (rev scheduled) (ct-scheduler-nt-car TrLst prev ntkstate)))
  :hints (("Goal" :in-theory (disable ct-test_routes))))

(defun ct-scheduler-nt-mv1 (TrLst prev ntkstate)
  (if (endp TrLst)
    nil
    (let ((v (car TrLst)))
      (mv-let (newntkstate r?)
              (inst-test_routes ntkstate v)
              (if (test_prev_routes r? prev)
                (cons v (ct-scheduler-nt-mv1 (cdr TrLst) (cons r? prev)
                                             newntkstate))
                  (ct-scheduler-nt-mv1 (cdr TrLst) prev
                                       newntkstate))))))
(defthm ct-scheduler-nt-mv1-equal
  (equal (mv-nth 1 (ct-scheduler TrLst Scheduled  ArrivedAcc prev measureAcc ntkstate))
         (append (rev ArrivedAcc) (ct-scheduler-nt-mv1 TrLst prev ntkstate)))
  :hints (("Goal" :in-theory (disable ct-test_routes))))

(defun ct-scheduler-nt-mv2 (TrLst prev ntkstate)
  (if (endp TrLst)
    nil
    (let ((v (car TrLst)))
      (mv-let (newntkstate r?)
              (inst-test_routes ntkstate v)
              (if (test_prev_routes r? prev)
                  (cons 0
                        (ct-scheduler-nt-mv2 (cdr TrLst) (cons r? prev)
                                             newntkstate))
                  (cons (len (car (RoutesV (car TrLst))))
                        (ct-scheduler-nt-mv2 (cdr TrLst) prev
                                             newntkstate)))))))
(defthm ct-scheduler-nt-mv2-equal
  (equal (mv-nth 2 (ct-scheduler TrLst Scheduled ArrivedAcc prev measureAcc ntkstate))
         (append (rev measureAcc) (ct-scheduler-nt-mv2 TrLst prev ntkstate)))
  :hints (("Goal" :in-theory (disable ct-test_routes))))
(defthm ct-scheduler-nt-mv3-equal
  (equal (mv-nth 3 (ct-scheduler TrLst Scheduler ArrivedAcc prev measureAcc ntkstate))
         ntkstate))

(defthm ntkstate-test-routes-mv0
  (equal (mv-nth 0 (ct-test_routes ntkstate v)) ntkstate))
(defthm ntkstate-test-routes-car
  (equal (car (ct-test_routes ntkstate v)) ntkstate))



;;---------------------------------------------------------------------
;;
;; PROOF OF DECREASING MEASURE
;;
;;---------------------------------------------------------------------
(defthm good_route-implies-smaller-routes
  (mv-let (newntkstate r?)
          (inst-test_routes ntkstate (car TrLst))
          (implies (test_prev_routes r? prev)
                   (< (car (ct-scheduler-nt-mv2 TrLst prev newntkstate))
                      (car (RouteLengths-TrLst TrLst))))))

(defun elts-<= (x y)
  (if (endp x)
      (endp y)
      (and (<= (car x) (car y))
           (natp (car x)) (natp (car y))
           (elts-<= (cdr x) (cdr y)))))

(defthm elts-<=-implies-sum-<=
  (implies (elts-<= x y)
           (<= (sum-of-lst x) (sum-of-lst y))))

(defthm plus-<
  (implies (and (< x1 y1)
                (<= x y))
           (< (+ x1 x)
              (+ y1 y))))

(defthm smaller-car-implies-smaller-sum
  (implies (and (< (car x) (car y))
                (elts-<= x y))
      (< (sum-of-lst x) (sum-of-lst y))))

(defthm scheduled-routes-<=-original
  (elts-<= (ct-scheduler-nt-mv2 TrLst prev ntkstate)
           (RouteLengths-TrLst TrLst)))

(defthm good-route-implies-smaller-measure
  (mv-let (newntkstate r?)
          (inst-test_routes ntkstate (car TrLst))
          (declare (ignore newntkstate))
          (implies (and (consp TrLst)
                        r?)
                   (< (sum-of-lst (ct-scheduler-nt-mv2 TrLst nil ntkstate))
                      (sum-of-lst (RouteLengths-TrLst TrLst)))))
  :hints (("Goal" :in-theory (disable get_buff orgv routesv
                                      sum-of-lst good_route-implies-smaller-routes))))

(defthm good-route-possible-implies-smaller-measure
  (implies (not (no-good-routes TrLst ntkstate))
           (< (sum-of-lst (ct-scheduler-nt-mv2 TrLst nil ntkstate))
              (sum-of-lst (RouteLengths-TrLst TrLst))))
  :hints (("Subgoal *1/3" :use (:instance good-route-implies-smaller-measure))
          ("Subgoal *1/2" :use (:instance good-route-implies-smaller-measure))

))

;;---------------------------------------------------------------------
;;
;; PROOF OF GeNoC CONSTRAINTS
;;
;;---------------------------------------------------------------------
;; 1/ proof that the measure decreases if assumptions are met
;; -----------------------------------
(defthm ct-measure-decreases
    (implies (and (ct-legal-measure measure trlst nodeset ntkstate order)
                  (ct-scheduling-assumptions trlst NodeSet ntkstate order))
             (O< (mv-nth 2 (ct-scheduling TrLst NodeSet ntkstate order))
                 (acl2-count measure))))


;;----------------------------------------------------------

;; 2/ we prove that the ids of the delayed and scheduled travels
;; are part of the initial travel list
;; -----------------------------------
(in-theory (disable update-ntkstate))
(defthm subsetp-scheduled-id-ct
  (subsetp (V-ids (ct-scheduler-nt-car TrLst prev ntkstate))
           (V-ids TrLst)))
(defthm subsetp-delayed-id-ct
  (subsetp (V-ids (ct-scheduler-nt-mv1 TrLst prev ntkstate))
           (V-ids TrLst)))
;------------------------------------------------------------------

;; 3/ we prove that the list of scheduled travels is a
;; valid travel list
;; --------------------------------------------------


;; proof for the scheduled travels
;; -------------------------------
(local
 (defthm validfields-trlst-ct-sched
   (implies (ValidFields-TrLst TrLst nodeset)
            (ValidFields-TrLst (ct-scheduler-nt-car TrLst prev ntkstate) nodeset))))

(local
 (defthm not-member-V-ids-ct-sched
   (implies (not (member-equal e (V-ids TrLst)))
            (not
             (member-equal
              e
              (V-ids
               (ct-scheduler-nt-car TrLst prev ntkstate)))))))

(defthm no-duplicatesp-ct-sched
  (implies (no-duplicatesp-equal (V-ids TrLst))
           (no-duplicatesp-equal
            (V-ids (ct-scheduler-nt-car TrLst prev ntkstate)))))

(defthm cons-v-ids
  (equal (consp (v-ids TrLst))
         (consp TrLst)))

(defthm TrLstp-scheduled-ct
  (implies (TrLstp TrLst nodeset)
           (TrLstp (ct-scheduler-nt-car TrLst prev ntkstate) nodeset)))

;; proof for the delayed travels
;; -----------------------------
(local
 (defthm validfields-trlst-ct-del
   (implies (ValidFields-TrLst TrLst nodeset)
            (ValidFields-TrLst
             (ct-scheduler-nt-mv1 TrLst prev ntkstate) nodeset))))

(local
 (defthm not-member-V-ids-ct-del
   (implies (not (member-equal e (V-ids TrLst)))
            (not
             (member-equal
              e
              (V-ids
               (ct-scheduler-nt-mv1 TrLst prev ntkstate)))))))

(local (defthm no-duplicatesp-ct-del
         (implies (no-duplicatesp-equal (V-ids TrLst))
                  (no-duplicatesp-equal
                   (V-ids (ct-scheduler-nt-mv1 TrLst prev ntkstate))))))

(defthm TrLstp-delayed-ct
  (implies (TrLstp TrLst nodeset)
           (TrLstp (ct-scheduler-nt-mv1 TrLst prev ntkstate) nodeset)))
;;--------------------------------------------------------------------


;; 4/ correctness of the scheduled travels
;; ------------------------------------------------------

(defthm extract-sublst-cons
  (implies (not (member-equal id Ids))
           (equal (extract-sublst (cons (list id org frm routes flit time) L)
                                  Ids)
                  (extract-sublst L Ids))))


(defthm test_prev_routes-member-equal
  (mv-let (newntkstate r?)
          (inst-good_route? ntkstate org dest routes)
          (declare (ignore newntkstate))
          (implies r?
                   (member-equal r? routes))))

(defthm no-duplicatesp-equal-append
  ;; to move to misc
  (implies (no-duplicatesp-equal (append (list x) (v-ids y)))
           (not (member-equal x (v-ids y)))))


(defthm ct-scheduled-correctness
  (let ((arrived (ct-scheduler-nt-mv1 TrLst prev st)))
    (implies (TrLstp TrLst nodeset)
             (s/d-travel-correctness
              arrived
              (extract-sublst TrLst (V-ids arrived)))))
  :hints (("GOAL"
           :in-theory (disable len extract-sublst))
          ("Subgoal *1/9"
           :in-theory (disable len ct-test_routes))
          ("Subgoal *1/5"
           :in-theory (disable len ct-test_routes))))



;; 5/ We prove that Delayed is equal to filtering TrLst
;; according to the ids of Delayed
;; ----------------------------------------------------
(defthm ct-delayed-correctness
  (let ((traveling (ct-scheduler-nt-car TrLst prev st)))
    (implies (TrLstp TrLst nodeset)
             (subsetp
              (V-ids traveling) (v-ids Trlst))))
  :hints (("GOAL"
           :in-theory (disable len ct-test_routes)
           :do-not '(eliminate-destructors)))
  :rule-classes nil)


(defthm ct-delayed-correctness-org
  (let ((traveling (ct-scheduler-nt-car TrLst prev st)))
    (implies (TrLstp TrLst nodeset)
             (subsetp (V-orgs traveling) (v-orgs Trlst))))
  :hints (("GOAL"
           :in-theory (disable len ct-test_routes)
           :do-not '(eliminate-destructors)))
  :rule-classes nil)


(defthm ct-delayed-correctness-frm
  (let ((traveling (ct-scheduler-nt-car TrLst prev st)))
    (implies (TrLstp TrLst nodeset)
             (subsetp
              (V-frms traveling) (v-frms Trlst))))
  :hints (("GOAL"
           :in-theory (disable len ct-test_routes)
           :do-not '(eliminate-destructors)))
  :rule-classes nil)


(defthm ct-delayed-correctness-destination
  (let ((traveling (ct-scheduler-nt-car TrLst prev st)))
    (implies (TrLstp TrLst nodeset)
             (subsetp
              (Tm-dests (totmissives traveling)) (Tm-dests (totmissives Trlst)))))
  :hints (("GOAL"
           :in-theory (disable len ct-test_routes)
           :do-not '(eliminate-destructors))
          ("Subgoal *1/9" :in-theory (e/d (ct-test_routes)
                                          (ct-chk_avail))))
  :rule-classes nil)


(defthm ct-delayed-correctness-destination-m
  (let ((traveling (ct-scheduler-nt-car TrLst prev st)))
    (implies (TrLstp TrLst nodeset)
             (subsetp
              (m-dests (tomissives(totmissives traveling)))
              (m-dests (tomissives (totmissives Trlst))))))
  :hints (("GOAL"
           :in-theory (disable len ct-test_routes ct-chk_avail)
           :do-not '(eliminate-destructors))
          ("Subgoal *1/9" :in-theory (e/d (ct-test_routes)
                                          (ct-chk_avail trlstp))))
  :rule-classes nil)


(defthm ct-delayed-correctness-ultime
  (implies (Trlstp trlst nodeset)
           (equal (tomissives (totmissives (ct-scheduler-nt-car TrLst prev st)))
                  (tomissives (totmissives (extract-sublst
                                            trlst
                                            (v-ids (ct-scheduler-nt-car TrLst prev st)))))))
  :hints (("GOAL"
           :in-theory (disable len ct-test_routes))
          ("Subgoal *1/9" :in-theory (e/d (ct-test_routes)
                                          (ct-chk_avail)))))

(defthm equal-tmids-vids-pkttraveling
  (equal (v-ids (ct-scheduler-nt-car TrLst prev p))
         (tm-ids (totmissives (ct-scheduler-nt-car TrLst prev p))))
  :rule-classes nil)


(defthm equal-mids-tmids-vids-pkttraveling
  (equal (v-ids (ct-scheduler-nt-car TrLst prev p))
         (m-ids (tomissives (totmissives (ct-scheduler-nt-car TrLst prev p)))))
  :hints (("Goal" :in-theory (disable ct-test_routes)))
  :rule-classes nil)

(defthm ct-delayed-correctness-ultime-totmissives
  (implies (Trlstp trlst nodeset)
           (equal (tomissives
                   (totmissives (ct-scheduler-nt-car TrLst prev st)))
                  (tomissives
                   (totmissives
                    (extract-sublst trlst
                                    (tm-ids (totmissives (ct-scheduler-nt-car TrLst prev st))))))))
  :hints (("GOAL"
           :in-theory (disable trlstp len extract-sublst ct-test_routes))))

(defthm ct-delayed-correctness-ultime-totmissives-bis
  (implies (Trlstp trlst nodeset)
           (equal (tomissives (totmissives (ct-scheduler-nt-car TrLst prev p)))
                  (tomissives  (extract-sublst (totmissives trlst)
                                               (tm-ids (totmissives (ct-scheduler-nt-car TrLst prev p)))))))
  :hints (("Goal"   :do-not-induct t
                    :in-theory (disable trlstp len ct-test_routes))))



(defthm ct-delayed-correctness-ultime-totmissives-final
  (implies (Trlstp trlst nodeset)
           (equal (tomissives (totmissives (ct-scheduler-nt-car TrLst prev p)))
                  (extract-sublst (tomissives(totmissives trlst))
                                  (tm-ids (totmissives (ct-scheduler-nt-car TrLst prev p))))))

  :hints (("Goal"   :do-not-induct t
                    :use ((:instance ToTMissives-extract-sublst (L trslt)
                           (ids (v-ids (ct-scheduler-nt-car TrLst prev p))))
                          (:instance ToMissives-extract-sublst (L (totmissives TRlst)) (ids (v-ids (ct-scheduler-nt-car TrLst prev p))))
                          )
                    :in-theory (disable extract-sublst v-ids default-car assoc-equal
                                        nth-with-large-index nth-add1
                                        len ct-scheduler-nt-car trlstp))))

; -----------------------------------------------------------

;; -----------------------------------------------------------
;; 6/ we prove that the ids of the delayed travels are distinct
;; from those of the scheduled travels
;; ------------------------------------------------------------

(defthm not-in-cons
  (implies (and (not-in x y)
                (not (member-equal e x)))
           (not-in x (cons e y))))

(defthm not-in-v-ids-ct
  (implies (trlstp trlst nodeset)
           (not-in (v-ids (ct-scheduler-nt-car TrLst prev ntkstate))
                   (v-ids (ct-scheduler-nt-mv1 TrLst prev ntkstate))))
  :hints (("Goal" :in-theory (disable ct-test_routes))))
(defthm not-in-v-ids-ct2
  (implies (trlstp trlst nodeset)
           (not-in (v-ids (ct-scheduler-nt-mv1 TrLst prev ntkstate))
                   (v-ids (ct-scheduler-nt-car TrLst prev ntkstate))))
  :hints (("Goal" :in-theory (disable ct-test_routes))))
(defthm subsetp-output-input
  (subsetp (append (V-ids (ct-scheduler-nt-car TrLst prev st))
                   (V-ids (ct-scheduler-nt-mv1 TrLst prev st )))
           (V-ids TrLst))
    :hints (("Goal" :in-theory (disable ct-test_routes))))

(defthm subsetp-input-output
  (subsetp (V-ids TrLst)
           (append (V-ids (ct-scheduler-nt-car TrLst prev st))
                   (V-ids (ct-scheduler-nt-mv1 TrLst prev st))))
    :hints (("Goal" :in-theory (disable ct-test_routes))))


(defthm input=output
  (let ((out (ct-scheduling trlst NodeSet ntkstate order)))
    (implies (true-listp trlst)
             (trlst-equal (append (mv-nth 0 out) (mv-nth 1 out))
                          trlst)))
  :hints (("Goal" :use ((:instance subsetp-input-output (prev nil) (st ntkstate))
                        (:instance subsetp-output-input (prev nil) (st ntkstate))))))

(defthm nil-trlstp
  (trlstp nil nodeset))


;; -----------------------------------------------------------
;; Compliance to generic model
;; ------------------------------------------------------------

(definstance genericscheduling check-compliance-ct-scheduling
  :functional-substitution
  ((scheduling ct-scheduling)
   (scheduling-assumptions ct-scheduling-assumptions)
   (legal-measure ct-legal-measure)
   (initial-measure ct-initial-measure)
   (get_next_priority ct-get_next_priority)
   (ValidParamsp 2DMesh-Validparamsp)
   (NodeSetGenerator 2DMesh-NodeSetGenerator)
   (loadbuffers inst-Loadbuffers)
   (readbuffers inst-Readbuffers)
   (StateGenerator inst-StateGenerator)
   (ValidstateParamsp inst-ValidStateParamsp)
   (req_trans inst-req_trans)
   (process_req inst-process_req)
   (chk_avail inst-chk_avail)
   (good_route? inst-good_route?)
   (test_routes inst-test_routes))
  :rule-classes nil
  :otf-flg t
  :hints (("goal" :do-not-induct t
                  :in-theory (disable trlstp))
; Matt K.: The following subgoal hint was changed to "8.2'" from "8" because of
; the change after ACL2 Version 3.6.1 to speed up evaluation of calls of mv-let
; (which was a change to the way ACL2 translates mv-let expressions in theorems
; into internal form).  It seems that this mv-let change may have affected the
; way make-event expansion is done here.
          ("Subgoal 7.2'" ; changed after v4-3 from "Subgoal 8.2'", for tau system
           :use ((:instance tomissives-extract-sublst (l (totmissives trlst))
                            (ids (tm-ids (totmissives trlst))))
                 (:instance totmissives-extract-sublst (l trlst)
                            (ids (v-ids trlst)))
                 (:instance extract-sublst-identity)))))

(in-theory (enable update-ntkstate))#|ACL2s-ToDo-Line|#
