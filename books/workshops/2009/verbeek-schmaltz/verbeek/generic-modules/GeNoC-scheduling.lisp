#|$ACL2s-Preamble$;
; Julien Schmaltz
;; Generic Scheduling Module of GeNoC
;; Feb 16th 2005
;; File: GeNoC-scheduling.lisp
;; Amr HELMY Revised and modified January 24th 2008
;;edited by Amr HELMY, Laurence Pierre august 22nd of august 2007

;;Amr helmy
;;31st october 2007

(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")
(include-book "GeNoC-nodeset")
(include-book "GeNoC-misc") ;; imports also GeNoC-types
(include-book "GeNoC-ntkstate")#|ACL2s-ToDo-Line|#
;
;; Inputs: TrLst = ( ... (Id org frm route) ...), measure, NodeSet, and
;; the current network state
;; outputs: TrLst updated, arrived missives, new state of the network,
;; measure updated


(defspec GenericScheduling
  ;; Function Scheduling represents the scheduling policy of the
  ;; network.
  ;; arguments: TrLst measure P
  ;; outputs: newTrLst Arrived newP newMeasure
  (((scheduling * *  * *) => (mv * * * *))
   ((get_next_priority *)=> *)
   ((scheduling-assumptions *  * * *) => *)
   ((legal-measure * * * * *) => *)
   ((initial-measure * * * *) => *))

  (local (defun get_next_priority (port)
           port))
  (local (defun scheduling-assumptions (TrLst NodeSet ntkstate order)
           (declare (ignore TrLst NodeSet ntkstate order))
           nil))
  (local (defun legal-measure (measure trlst nodeset ntkstate order)
           (declare (ignore measure trlst nodeset ntkstate order))
           nil))
  (local (defun initial-measure (trlst nodeset ntkstate order)
           (declare (ignore trlst nodeset ntkstate order))
           nil))
  (local (defun scheduling (TrLst NodeSet ntkstate order)
           ;; local witness
           (mv
            ;; TrLst updated
            (if (not (scheduling-assumptions TrLst NodeSet ntkstate order))
                (totmissives TrLst)
              nil)
            ;; arrived messages
            ;(if (is-base-measure measure)
                nil
            ;  TrLst)
            ;; measure is nil
            nil
            ;; ntkstate preserved
            ntkstate)
            ))

  ;; Proof obligations (also named constraints)
  ;; -----------------------------------------
  (defthm scheduled-nil-nil
    ;; the result of the scheduling function in the case of empty
    ;; input list is equal to nil
    (equal (car (scheduling nil nodeset  ntkstate order)) nil))

  ;; 1/ Types of newTrLst, Arrived and P (state)
  ;; ---------------------------------
  ;; The type of newTrLst is a valid traveling missives list

  (defthm tmissivesp-newTrlst
    (implies (trlstp TrLst nodeset)
             (tmissivesp (mv-nth 0 (scheduling TrLst NodeSet ntkstate order))
                         NodeSet)))

  ;; so is the list of Arrived
  (defthm trlstp-Arrived      ;; OK
    (implies (trlstp TrLst nodeset)
             (trlstp (mv-nth 1 (scheduling TrLst NodeSet ntkstate order))
                     nodeset)))

  ;; the state list P is a ValidState
  (defthm Valid-state-ntkstate
    (implies (validstate ntkstate)
             (validstate (mv-nth 3 (scheduling TrLst NodeSet ntkstate order)))))


  ;; 2/ the measure provided to GeNoC must be decreasing.
  ;; ------------------------------------------------------
  ;; scheduling-assumptions must be a boolean
  (defthm booleanp-assumptions
    (booleanp (scheduling-assumptions TrLst NodeSet ntkstate order))
    :rule-classes :type-prescription)

  ;; legal-measure nust be a boolean
  (defthm booleanp-legal-measure
    (booleanp (legal-measure measure trlst nodeset ntkstate order))
    :rule-classes :type-prescription)

  ;; the measure must decrease on each call of scheduling
  (defthm measure-decreases
    (implies (and (legal-measure measure trlst nodeset ntkstate order)
                  (scheduling-assumptions trlst NodeSet ntkstate order))
             (O< (acl2-count (mv-nth 2 (scheduling TrLst NodeSet ntkstate order)))
                 (acl2-count measure))))


  ;; 3/ Correctness of the arrived missives
  ;; ------------------------------------------------------------------
  ;; For any arrived missive arr, there exists a unique travel
  ;; tr in the initial TrLst, such that IdV(arr) = IdV(tr)
  ;; and FrmV(arr) = FrmV(tr) and RoutesV(arr) is a
  ;; sublist of RoutesV(tr).
  ;; In ACL2, the uniqueness of the ids is given by the predicate
  ;; TrLstp.
  ;; -------------------------------------------------------------------

  ;; First, let us define this correctness
  (defun s/d-travel-correctness (arr-TrLst TrLst/arr-ids)
    (if (endp arr-TrLst)
        (if (endp TrLst/arr-ids)
            t
          nil)
      (let* ((arr-tr (car arr-TrLst))
             (tr (car TrLst/arr-ids)))
        (and (equal (FrmV arr-tr) (FrmV tr))
             (equal (IdV arr-tr) (IdV tr))
             (equal (OrgV arr-tr) (OrgV tr))
             (equal (FlitV arr-tr) (FlitV tr))
             (equal (timeV arr-tr) (TimeV tr))
             (subsetp (RoutesV arr-tr) (RoutesV tr))
             (s/d-travel-correctness (cdr arr-TrLst)
                                     (cdr TrLst/arr-ids))))))


  (defthm s/d-travel-correctness-unitary
    (implies (trlstp x nodeset)
             (s/d-travel-correctness x x)))

  (defthm arrived-travels-correctness
    (mv-let (newTrLst Arrived newMeasure newstate )
            (scheduling TrLst  NodeSet  ntkstate order)
            (declare (ignore newTrLst newMeasure newstate ))
            (implies (TrLstp TrLst nodeset)
                     (s/d-travel-correctness
                      Arrived
                      (extract-sublst TrLst (V-ids Arrived)))))
    :hints (("Goal" :in-theory (disable trlstp))))

  (defthm subsetp-arrived-newTrLst-ids
    ;; this should be provable from the two lemmas above
    ;; but it will always be trivial to prove, and it is
    ;; useful in subsequent proofs.
    (mv-let (newTrLst Arrived newMeasure newstate )
            (scheduling TrLst NodeSet ntkstate order)
            (declare (ignore newMeasure newstate ))
            (implies (TrLstp TrLst nodeset)
                     (and (subsetp (v-ids Arrived) (v-ids Trlst))
                          (subsetp (Tm-ids newTrLst) (v-ids TrLst))))))


  ;; 4. Correctness of the newTrLst travels
  ;; -------------------------------------
  ;; the correctness of the newTrLst travels differs from
  ;; the correctness of the Arrived travels because,
  ;; for the Arrived travels we will generally keep only
  ;; one route, but for the newTrLst travels we will not modify
  ;; the travels and keep all the routes. In fact, by
  ;; converting a travel back to a missive we will remove the
  ;; routes.
  ;; ---------------------------------------------------------

  ;; the list newTrLst is equal to filtering the initial
  ;; TrLst according to the Ids of newTrLst



  (defthm newTrLst-travel-correctness       ;; OK
    ;; the correctness of newtrlst is the equivalence of the transformation
    ;;of the newtrlst into missives, and the transformation of the
    ;;initial trlst (input to the scheduling function)
    ;;into tmissives and then to missives
    ;; this rule will cause an infinite number of rewrites that's why
    ;; it's in rule-classes nil, we have to create an instance to use
    ;; it
    (mv-let (newTrLst Arrived  newMeasure newstate )
            (scheduling TrLst NodeSet  ntkstate order)
            (declare (ignore Arrived newMeasure newstate))
            (implies (TrLstp TrLst nodeset)
                     (equal (tomissives newTrLst)
                            (extract-sublst (tomissives(totmissives
                                                        TrLst))
                                            (Tm-ids newTrLst)))))

    :rule-classes nil)

  ;; 6/ if scheduling assumptions are not met, measure is nil
  (defthm mv-nth-2-scheduling-on-zero-measure      ;; OK
    ;; if the scheduling measure is 0
    ;; the new measure is equal to the initial one
    (implies (and (not (scheduling-assumptions TrLst NodeSet ntkstate order))
                  (TrLstp trlst nodeset))
             (equal (mv-nth 2 (scheduling TrLst NodeSet ntkstate order))  ;; new measure
              nil)))

  (defthm mv-nth-0-scheduling-on-zero-measure    ;; OK
    ;; if the scheduling measure is 0
    ;; the set of newTrLst s is equal to the initial TrLst
    (implies (not (scheduling-assumptions TrLst NodeSet ntkstate order))
             (equal
              (mv-nth 0 (scheduling TrLst NodeSet ntkstate order))
              (totmissives TrLst))))

  ;; 7/ The intersection of the ids of the Arrived travels and those
  ;; of the newTrLst travels is empty
  ;; -----------------------------------------------------------------

  (defthm not-in-newTrLst-Arrived         ;; OK
    (mv-let (newTrLst Arrived  newmeasure newstate )
            (scheduling TrLst NodeSet ntkstate order)
            (declare (ignore  newmeasure newstate ))
            (implies (TrLstp TrLst nodeset)
                     (not-in (Tm-ids newTrLst) (v-ids Arrived)))))

  ;; some constraints required because we do not have a definition
  ;; for scheduling
  (defthm consp-scheduling      ;; OK
    ;; for the mv-nth
    (consp (scheduling TrLst NodeSet ntkstate order))
    :rule-classes :type-prescription)

  (defthm true-listp-car-scheduling      ;; OK
    (implies (true-listp TrLst)
             (true-listp (mv-nth 0 (scheduling TrLst NodeSet
                                               ntkstate order ))))

    :rule-classes :type-prescription)

  (defthm true-listp-mv-nth-1-sched-1      ;; OK
    (implies (true-listp TrLst)
             (true-listp (mv-nth 1 (scheduling TrLst NodeSet
                                               ntkstate order))))

    :rule-classes :type-prescription)

  (defthm true-listp-mv-nth-1-sched-2      ;; OK
    (implies (TrLstp TrLst nodeset)
             (true-listp (mv-nth 1 (scheduling TrLst NodeSet
                                               ntkstate order))))

    :rule-classes :type-prescription)

  ) ;; end of scheduling


(defthm correctroutesp-s/d-travel-correctness    ;; OK
  ;; correctroutesp between trlst/ids and it's transformation into
  ;; tmissves, and the s/d-travel-correctness, between trlst/ids and
  ;; trlst1
  ;; implies the correctroutesp between trlst1 and trlst/ids
  (implies (and (CorrectRoutesp TrLst/ids (ToTMissives TrLst/ids) NodeSet)
                (s/d-travel-correctness TrLst1 TrLst/ids))
           (CorrectRoutesp TrLst1
                           (ToTMissives TrLst/ids) NodeSet)))


(defthm scheduling-preserves-route-correctness      ;; OK
  ;; we prove that sheduling preserve the correctness of the routes
  ;; after the transformation
  (mv-let (newTrLst Arrived newmeasure newstate )
          (scheduling TrLst NodeSet ntkstate order)
          (declare (ignore newTrLst newstate newmeasure ))
          (implies (and (CorrectRoutesp TrLst (ToTMissives TrLst) NodeSet)
                        (TrLstp TrLst nodeset))
                   (CorrectRoutesp Arrived
                                   (ToTMissives
                                    (extract-sublst
                                     TrLst
                                     (V-ids Arrived)))
                                   NodeSet)))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory
           (disable mv-nth ;; to have my rules used
                    ToTMissives-extract-sublst TrLstp))))


(defthm TMissivesp-mv-nth-0-scheduling       ;; OK
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (CorrectRoutesp TrLst (ToTMissives TrLst) NodeSet)
                  (ValidParamsp Params)
                  (TrLstp TrLst nodeset))
             (TMissivesp (mv-nth 0 (scheduling TrLst NodeSet
                                               ntkstate order))
                         NodeSet)))

  :hints (("Goal"
           :use
           (:instance tmissivesp-newTrlst
                      (nodeset (NodeSetGenerator Params))))))

