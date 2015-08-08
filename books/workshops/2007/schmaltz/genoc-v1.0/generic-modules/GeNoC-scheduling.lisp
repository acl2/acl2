; Julien Schmaltz
;; Generic Scheduling Module of GeNoC
;; Feb 16th 2005
;; File: GeNoC-scheduling.lisp
;; Rev. Nov. 22nd 2005
;; JS: NodeSet is not necessary in practice and fundamentally
;; so I remove it from the scheduling definition
(in-package "ACL2")
(include-book "GeNoC-nodeset")
(include-book "GeNoC-misc") ;; imports also GeNoC-types

;; Inputs: TrLst = ( ... (Id frm route) ...)
;; outputs: Scheduled and Delayed (which are both TrLst)
(encapsulate
 ;; Function Scheduling represents the scheduling policy of the
 ;; network.
 ;; arguments: TrLst att
 ;; outputs: Scheduled Delayed newatt
 (((scheduling * *) => (mv * * *)))

 (local (defun consume-attempts (att)
          ;; function that consumes one attempt for each node
          ;; which has still at least one left
	  (if (zp (SumOfAttempts att))
              att
            (let* ((top (car att))
                   (node (car top))
                   (atti (cadr top)))
              (if (zp atti)
                  (cons top
                        (consume-attempts (cdr att)))
                (cons (list node (1- atti))
                      (consume-attempts (cdr att))))))))

 (local (defun scheduling (TrLst att)
          ;; local witness
          (mv
           ;; scheduled frames
           (if (zp (SumOfAttempts att))
               nil  ;; no attempt left -> nothing is scheduled
             TrLst)  ;; otherwise everything is scheduled
           ;; delayed frames
           (if (zp (SumOfAttempts att))
               TrLst ;; no attempt left -> everything is delayed
             nil) ;; otherwise nothing is delayed
           (if (zp (SumOfAttempts att))
               att ;; no attempt left -> no modification on att
             (consume-attempts att))))) ;; newatt has less attempts than att

 ;; Proof obligations (also named constraints)
 ;; -----------------------------------------

 ;; 1/Type of Scheduled and Delayed travels
 ;; ---------------------------------------
 ;; The list of scheduled travels is a valid travel list
 (defthm trlstp-scheduled
   (implies (trlstp TrLst)
            (trlstp (mv-nth 0 (scheduling TrLst att)))))

 ;; so is the list of delayed travels
 (defthm trlstp-delayed
   (implies (trlstp TrLst)
            (trlstp (mv-nth 1 (scheduling TrLst att)))))

 ;; 2/ consume at least one attempt to ensure termination.
 ;; ------------------------------------------------------
 (defthm consume-at-least-one-attempt
   ;; the scheduling policy should consume at least one attempt
   ;; this is a sufficient condition to prove that
   ;; the full network function terminates
   (mv-let (Scheduled Delayed newatt)
	   (scheduling TrLst att)
	   (declare (ignore Scheduled Delayed))
	   (implies (not (zp (SumOfAttempts att)))
		    (< (SumOfAttempts newatt) (SumOfAttempts att)))))

 ;; 3/ Correctness of the scheduled travels
 ;; ------------------------------------------------------------------
 ;; For any scheduled travel sched-tr, there exists a unique travel
 ;; tr in the initial TrLst, such that IdV(sched-tr) = IdV(tr)
 ;; and FrmV(sched-tr) = FrmV(tr) and RoutesV(sched-tr) is a
 ;; sublist of RoutesV(tr).
 ;; In ACL2, the uniqueness of the ids is given by the predicate
 ;; TrLstp.
 ;; -------------------------------------------------------------------

 ;; First, let us define this correctness
 (defun s/d-travel-correctness (sd-TrLst TrLst/sd-ids)
   ;; sd-TrLst is the list of scheduled or delayed travels
   ;; TrLst/sd-ids is the filtering of the initial TrLst
   ;; according to the ids of the scheduled or delayed travels
   (if (endp sd-TrLst)
       (if (endp TrLst/sd-ids)
           t
         nil)
     (let* ((sd-tr (car sd-TrLst))
            (tr (car TrLst/sd-ids)))
       (and (equal (FrmV sd-tr) (FrmV tr))
            (equal (IdV sd-tr) (IdV tr))
            (subsetp (RoutesV sd-tr) (RoutesV tr))
            (s/d-travel-correctness (cdr sd-TrLst)
                                    (cdr TrLst/sd-ids))))))

 (defthm scheduled-travels-correctness
   (mv-let (Scheduled Delayed newatt)
           (scheduling TrLst att)
           (declare (ignore Delayed newatt))
           (implies (TrLstp TrLst)
                    (s/d-travel-correctness
                     scheduled
                     (extract-sublst TrLst (V-ids Scheduled))))))

 (defthm subsetp-scheduled-delayed-ids
   ;; this should be provable from the two lemmas above
   ;; but it will always be trivial to prove, and it is
   ;; useful in subsequent proofs.
   (mv-let (scheduled delayed newatt)
           (scheduling TrLst att)
           (declare (ignore newatt))
           (implies (TrLstp TrLst)
                    (and (subsetp (v-ids scheduled) (v-ids Trlst))
                         (subsetp (v-ids delayed) (v-ids TrLst))))))

 ;; 4. Correctness of the delayed travels
 ;; -------------------------------------
 ;; the correctness of the delayed travels differs from
 ;; the correctness of the scheduled travels because,
 ;; for the scheduled travels we will generally keep only
 ;; one route, but for the delayed travels we will not modify
 ;; the travels and keep all the routes. In fact, by
 ;; converting a travel back to a missive we will remove the
 ;; routes.
 ;; ---------------------------------------------------------

 ;; the list Delayed is equal to filtering the initial
 ;; TrLst according to the Ids of Delayed

 (defthm delayed-travel-correctness
   ;; this is a looping rule !!! should be disabled and used
   ;; at the right time
   (mv-let (Scheduled Delayed newatt)
           (scheduling TrLst att)
           (declare (ignore newatt scheduled))
           (implies (TrLstp TrLst)
                    (equal Delayed
                           (extract-sublst TrLst (V-ids Delayed)))))
   :rule-classes nil)


 ;; 6/ if the initial AttLst contains only 0, we do not modify it
 (defthm mv-nth-2-scheduling-on-zero-attlst
   ;; if every attempt has been consumed
   ;; the new att is equal to the initial one
   (implies (and (zp (SumOfAttempts att))
                 (TrLstp trlst))
            (equal
             (mv-nth 2 (scheduling TrLst att));; new att
             att)))

 (defthm mv-nth-1-scheduling-on-zero-attlst
   ;; if every attempt has been consumed
   ;; the set of delayed orders is equal to the initial TrLst
   (implies (zp (SumOfAttempts att))
            (equal
             (mv-nth 1 ;; delayed travels
                     (scheduling TrLst att))
             TrLst)))

 ;; 7/ The intersection of the ids of the scheduled travels and those
 ;; of the delayed travels is empty
 ;; -----------------------------------------------------------------

 (defthm not-in-delayed-scheduled
   (mv-let (scheduled delayed newatt)
           (scheduling TrLst att)
           (declare (ignore newatt))
           (implies (TrLstp TrLst)
                    (not-in (v-ids delayed) (v-ids scheduled)))))

 ;; some constraints required because we do not have a definition
 ;; for scheduling
 (defthm consp-scheduling
   ;; for the mv-nth
   (consp (scheduling TrLst att))
   :rule-classes :type-prescription)

 (defthm true-listp-car-scheduling
   (implies (true-listp TrLst)
            (true-listp (mv-nth 0 (scheduling TrLst att))))
   :rule-classes :type-prescription)

 (defthm true-listp-mv-nth-1-sched
   (implies (TrLstp TrLst)
            (true-listp (mv-nth 1 (scheduling TrLst att))))
   :rule-classes :type-prescription)
) ;; end of scheduling

(defthm checkroutes-member-equal
  (implies (and (checkroutes routes m NodeSet)
                (member-equal r Routes))
           (validroutep r m)))

(defthm checkroutes-subsetp-validroute
  (implies (and (checkroutes routes m NodeSet)
                (consp r)
                (subsetp r routes))
           (and (validroutep (car r) m)
                (subsetp (car r) NodeSet))))

(defthm checkroutes-subsetp
  (implies (and (checkroutes routes m NodeSet)
                (subsetp routes1 routes))
           (checkroutes routes1 m NodeSet)))

(defthm correctroutesp-s/d-travel-correctness
  (implies (and (CorrectRoutesp TrLst/ids (ToMissives TrLst/ids) NodeSet)
                (s/d-travel-correctness TrLst1 TrLst/ids))
           (CorrectRoutesp TrLst1
                           (ToMissives TrLst/ids) NodeSet)))


(defthm scheduling-preserves-route-correctness
  (mv-let (Scheduled Delayed newatt)
          (scheduling TrLst att)
          (declare (ignore Delayed newatt))
          (implies (and (CorrectRoutesp TrLst (ToMissives TrLst) NodeSet)
                        (TrLstp TrLst))
                   (CorrectRoutesp Scheduled
                                   (ToMissives
                                    (extract-sublst
                                       TrLst
                                       (V-ids scheduled)))
                                   NodeSet)))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :in-theory
           (disable mv-nth ;; to have my rules used
                    tomissives-extract-sublst TrLstp))))

(defthm scheduling-preserves-route-correctness-delayed
  (mv-let (Scheduled Delayed newatt)
          (scheduling TrLst att)
          (declare (ignore scheduled newatt))
          (implies (and (CorrectRoutesp TrLst (ToMissives TrLst) NodeSet)
                        (TrLstp TrLst))
                   (CorrectRoutesp Delayed
                                   (ToMissives Delayed)
                                   NodeSet)))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :use
           ((:instance delayed-travel-correctness))
           :in-theory (disable tomissives-extract-sublst TrLstp))))

;; the three defthms are similar to the three used to prove
;; missivesp-extract-sublst in GeNoC.lisp ... (proof by analogy)

(defthm valid-trlstp-assoc-equal
  (implies (and (TrLstp L)
                (member-equal e (V-ids L)))
           (TrLstp (list (assoc-equal e L)))))

(defthm TrLstp-cons
  ;; lemma used in the next defthm
  ;; if we cons a valid travel to a filtered valid list
  ;; of travel, we obtain a valid list of travel if the
  ;; consed travel has an id less than the first of the filter
  ;; and this id is not in the filter
  (implies (and (trlstp (extract-sublst L ids))
                (trlstp (list (assoc-equal e L)))
                (not (member-equal e ids))
                (subsetp ids (V-ids L)))
           (trlstp (cons (assoc-equal e L)
                         (extract-sublst L ids)))))

(defthm trlstp-extract-sublst
  (implies (and (TrLstp TrLst) (subsetp ids (v-ids TrLst))
                (no-duplicatesp ids) (true-listp ids))
           (trlstp (extract-sublst TrLst ids)))
  :hints (("GOAL"
           :in-theory (disable TrLstp))))

(defthm extract-sublst-subsetp-v-ids
  (implies (and (subsetp ids (V-ids l))
                (true-listp ids)
                (TrLstp l))
           (equal (v-ids (extract-sublst l ids))
                  ids)))

(defthm Missivesp-mv-nth-1-scheduling
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (CorrectRoutesp TrLst (ToMissives TrLst) NodeSet)
                  (ValidParamsp Params)
                  (TrLstp TrLst))
             (Missivesp (ToMissives
                         (mv-nth 1
                                 (scheduling TrLst att)))
                        NodeSet)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use ((:instance delayed-travel-correctness)
                 (:instance trlstp-delayed))
           :in-theory (disable Missivesp trlstp-delayed
                               TOMISSIVES-EXTRACT-SUBLST
                               TrLstp mv-nth))))
