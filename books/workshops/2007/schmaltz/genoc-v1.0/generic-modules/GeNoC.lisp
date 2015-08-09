;; Julien Schmaltz
;; Generic Routing Module of GeNoC
;; June 20th 2005
;; File: GeNoC-routing.lisp

(in-package "ACL2")

;; we import the previous books
(include-book "GeNoC-scheduling") ;; imports GeNoC-misc and GeNoC-nodeset
(include-book "GeNoC-routing")

(in-theory (disable mv-nth))

;;------------------------------------------------------------------------
;;
;;                        GeNoC_t
;;
;;------------------------------------------------------------------------

;; Tail definition of GeNoC_t
;; --------------------------
(defun GeNoC_t (M NodeSet att TrLst)
  ;; The composition of Routing and Scheduling is built by function GeNoC_t.
  ;; It takes as arguments:
  ;; - a list of missives, M
  ;; - the set of existing nodes, NodeSet
  ;; - the list of attempts, att
  ;; - an accumulator of travels, TrLst
  ;;
  ;; we set the measure to be SumOfAttempts(att)
  (declare (xargs :measure (SumOfAttempts att)))
  (if (zp (SumOfAttempts att))
      ;; if every attempt has been consumed, we return the accumulator
      ;; TrLst and the remaining missives M
      (mv TrLst M)
    ;; else,
    (let ((V (Routing M NodeSet)))
      ;; we compute the routes. This produces the travel list V.
      (mv-let (Scheduled Delayed newAtt)
              ;; we call function scheduling
              (Scheduling V att)
              ;; we enter the recursive call and accumulate the
              ;; scheduled travels
              (GeNoC_t (ToMissives Delayed) NodeSet newAtt
                       (append Scheduled TrLst))))))


;; Correctness of GeNoC_t
;; ----------------------
(defun CorrectRoutes-GeNoC_t (routes m-dest)
  ;; GeNoC_t is correct if every element ctr of the output list
  ;; is such that (a) FrmV(ctr) = FrmM(m) and (b) forall r in
  ;; RoutesV(ctr) Last(r) = DestM(m). For the m such that
  ;; IdM(m) = IdV(ctr).
  ;; This function checks that (b) holds.
  (if (endp routes)
      t
    (let ((r (car routes)))
      (and (equal (car (last r)) m-dest)
           (CorrectRoutes-GeNoC_t (cdr routes) m-dest)))))

(defun GeNoC_t-correctness1 (TrLst M/TrLst)
  ;; we complement the correctness of GeNoC_t
  (if (endp TrLst)
      (if (endp M/TrLst)
          t
        nil)
    (let* ((tr (car TrLst))
           (v-frm (FrmV tr))
           (routes (RoutesV tr))
           (m (car M/TrLst))
           (m-frm (FrmM m))
           (m-dest (DestM m)))
      (and (equal v-frm m-frm)
           (CorrectRoutes-GeNoC_t routes m-dest)
           (GeNoC_t-correctness1 (cdr TrLst)
                                 (cdr M/TrLst))))))

(defun GeNoC_t-correctness (TrLst M)
  ;; before checking correctness we filter M
  ;; according to the ids of TrLst
  (let ((M/TrLst (extract-sublst M (V-ids TrLst))))
    (GeNoC_t-correctness1 TrLst M/TrLst)))


;; Non tail definition of GeNoC_t
;; ------------------------------
(defun GeNoC_t-non-tail-Comp (M NodeSet att)
  ;; we define a non tail function that computes the
  ;; first output of GeNoC_t, i.e the completed transactions
  (declare (xargs :measure (SumOfAttempts att)))
  (if (zp (SumOfAttempts att))
      ;; if every attempt has been consumed, we return the accumulator
      ;; TrLst and the remaining missives M
      nil
    ;; else,
    (let ((V (Routing M NodeSet)))
      ;; we compute the routes. This produces the travel list V.
      (mv-let (Scheduled Delayed newAtt)
              ;; we call function scheduling
              (Scheduling V att)
              ;; we enter the recursive call and accumulate the
              ;; scheduled travels
              (append (GeNoC_t-non-tail-Comp (ToMissives Delayed)
                                             NodeSet newAtt)
                      Scheduled)))))

;; we now prove that this function is right

(defthm true-listp-GeNoC_t-non-tail-comp
  (true-listp (GeNoC_t-non-tail-Comp M NodeSet att))
  :rule-classes :type-prescription)

(defthm GeNoC_t-non-tail-=-tail-comp
  (implies (true-listp TrLst)
           (equal (car (GeNoC_t M NodeSet att TrLst))
                  (append (GeNoC_t-non-tail-Comp M NodeSet Att)
                          TrLst))))

;; Proof of GeNoC_t correctness
;; ----------------------------

;; first we add a lemma that tells ACL2 that
;; converting the travels that are routed and delayed
;; produced a valid list of missives
(defthm missivesp-mv-nth1-scheduling-routing
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (Missivesp M NodeSet)
                  (ValidParamsp Params))
             (Missivesp
              (ToMissives (mv-nth 1
                                  (scheduling (routing M NodeSet)
                                              att)))
              NodeSet)))
  :hints (("GOAL"
           :in-theory (disable
                       TrLstp Missivesp))))



;; the recursive call of genoc_t-non-tail-comp calls append
;; we put the append at the top.
;; to do so we add the two rules below:

(defthm v-ids-append
  ;; the ids of an append is the append of the ids
  (equal (v-ids (append a b))
         (append (v-ids a) (v-ids b))))

(defthm extract-sublst-append
  ;; filtering according to an append is the append
  ;; of the filtering.
  (equal (extract-sublst M (append id1 id2))
         (append (extract-sublst M id1)
                 (extract-sublst M id2))))


;; then to split the proof is two cases, we replace the
;; append by a conjunction.
;; the rule below allows this decomposition:

(defthm correctroutess1-append
  (implies (and (equal (len a) (len c))
                (equal (len b) (len d)))
           (equal (genoc_t-correctness1 (append a b)
                                        (append c d))
                  (and (Genoc_T-Correctness1 a c)
                       (Genoc_T-Correctness1 b d)))))

;; To have this lemma used we need to prove some
;; additional properties between len and extract-sublst
;; and len and v-ids (e.g. a is a call to v-ids)

(defthm len-extract-sublst
  (equal (len (extract-sublst L ids))
         (len ids)))

(defthm len-v-ids
  (equal (len (v-ids x))
         (len x)))

;; now we need to prove some lemmas so that previous rules
;; (from GeNoC-misc) about extract-sublst, tomissives, etc could
;; fire.

(defthm subsetp-trans
  ;; transitivity of subsetp
  (implies (and (subsetp x y)
                (subsetp y z))
           (subsetp x z)))

(defthm v-ids-GeNoC_t-non-tail-comp
  ;; the ids of the output of genoc_t-non-tail-comp is a
  ;; subset of those of M
  ;; for this theorem the rule ids-routing is useful
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (Missivesp M NodeSet)
                  (ValidParamsp Params))
             (let ((Gnt (Genoc_T-Non-Tail-Comp M NodeSet att)))
               (subsetp (V-ids Gnt) (M-ids M)))))
  :hints (("GOAL"
           :in-theory
           (disable missivesp TrLstp))
          ("Subgoal *1/3"
           :use
           ((:instance subsetp-scheduled-delayed-ids
                       (TrLst (Routing M (NodeSetGenerator Params)))))
           :in-theory
           (disable subsetp-scheduled-delayed-ids Missivesp TrLstp))))

(defthm not-in-no-duplicatesp-equal-append
  ;; if x is not in y and both do not have duplicates then
  ;; their append has no duplicate too
  (implies (and (no-duplicatesp-equal x)
                (not-in x y)
                (no-duplicatesp-equal y))
           (no-duplicatesp-equal (append x y))))

(defthm subsetp-not-in
  ;; if a list y and no element in common with z
  ;; then any sublist x of y has no element in z
  (implies (and (not-in delayed scheduled)
                (subsetp x delayed))
           (not-in x scheduled)))

(defthm not-in-v-ids-genoc_t-non-tail-comp
  ;; if the ids of a list have no common element with
  ;; another ids then the output of genoc_t-non-tail-comp does
  ;; not introduce any new id
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (not-in (m-ids delayed) Sched-ids)
                  (Missivesp delayed NodeSet)
                  (ValidParamsp Params))
             (not-in (v-ids (genoc_t-non-tail-comp delayed NodeSet att))
                     Sched-ids)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :in-theory (disable missivesp))))

(defthm fwd-trlstp
  ;; because we disable trlstp, this rule adds its content
  ;; as hypotheses
  (implies (TrLstp TrLst)
           (and (validfields-trlst trlst)
                (true-listp trlst)
                (no-duplicatesp-equal (v-ids trlst))))
  :rule-classes :forward-chaining)

(defthm v-ids-GeNoC_t-non-tail-comp-no-dup
  ;; the ids of the output of genoc_t-non-tail-comp have no dup
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (Missivesp M NodeSet)
                  (ValidParamsp Params))
             (let ((Gnt (Genoc_T-Non-Tail-Comp M NodeSet att)))
               (no-duplicatesp-equal (V-ids Gnt)))))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :induct (genoc_t-non-tail-comp M (nodeSetGenerator Params) att)
           :in-theory (disable missivesp TrLstp))
          ("Subgoal *1/2"
           :use
           ((:instance
             not-in-v-ids-genoc_t-non-tail-comp
             (delayed (tomissives
                       (mv-nth 1 (scheduling
                                  (routing M (nodeSetGenerator Params))
                                  att))))
             (att (mv-nth 2 (scheduling
                             (routing M (nodeSetGenerator Params))
                             att)))
             (Sched-ids (v-ids (mv-nth 0 (scheduling
                                          (routing M (nodeSetGenerator Params))
                                          att)))))
            (:instance trlstp-scheduled
                       (TrLst (routing M (Nodesetgenerator Params)))))
           :in-theory
           (disable trlstp-scheduled mv-nth trlstp
                    not-in-v-ids-genoc_t-non-tail-comp Missivesp))))

(defthm extract-sublst-subsetp-m-ids
  ;; filtering a list l according to a subset ids of its identifiers
  ;; produces a list the ident. of which are ids
  (implies (and (subsetp ids (M-ids l))
                (true-listp ids)
                (Validfields-M l))
           (equal (M-ids (extract-sublst l ids))
                  ids)))

(defthm ToMissives-Delayed/Rtg
  ;; we prove that the conversion of the delayed travels
  ;; into a list of missives is equal to the filtering
  ;; of the initial list of missives M according to the ids
  ;; of the delayed travels.
  (let ((NodeSet (NodeSetGenerator Params)))
    (mv-let (Scheduled/Rtg Delayed/Rtg newAtt)
            (scheduling (Routing M NodeSet) att)
            (declare (ignore Scheduled/Rtg newAtt))
            (implies (and (Missivesp M NodeSet)
                          (ValidParamsp Params))
                     (equal (ToMissives Delayed/Rtg)
                            (extract-sublst M (V-ids Delayed/Rtg))))))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize fertilize)
           :use ((:instance ToMissives-extract-sublst
                            (L (Routing M (NodeSetGenerator Params)))
                            (ids
                             (V-ids (mv-nth 1
                                            (scheduling
                                             (Routing M (NodeSetGenerator Params))
                                             att)))))
                 (:instance delayed-travel-correctness
                            (TrLst (Routing M (NodeSetGenerator Params))))
                 (:instance subsetp-scheduled-delayed-ids
                            (TrLst (Routing M (NodeSetGenerator Params)))))
           :in-theory (disable TrLstp Missivesp
                               ToMissives-extract-sublst
                               subsetp-scheduled-delayed-ids))))

(defthm valid-missive-assoc-equal
  ;; a list of a member of a valid list of missives
  ;; is a valid list of missives
  (implies (and (Missivesp M NodeSet)
                (member-equal e (M-ids M)))
           (Missivesp (list (assoc-equal e M)) NodeSet)))

(defthm missivesp-cons
  ;; lemma used in the next defthm
  ;; if we cons a valid missive to a filtered valid list
  ;; of missives, we obtain a valid list of missives if the
  ;; the id of the consed missive is not in the filter
  (implies (and (missivesp (extract-sublst M ids) nodeset)
                (missivesp (list (assoc-equal e M)) nodeset)
                (not (member-equal e ids))
                (subsetp ids (M-ids M)))
           (missivesp (cons (assoc-equal e M)
                            (extract-sublst M ids))
                      nodeset)))


(defthm missivesp-extract-sublst
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (missivesp M NodeSet)
                  (ValidParamsp Params)
                  (true-listp ids)
                  (no-duplicatesp-equal ids)
                  (subsetp ids (M-ids M)))
             (Missivesp (extract-sublst M ids) NodeSet)))
  :hints (("GOAL"
           :in-theory (disable missivesp))
          ("Subgoal *1/1"
           :in-theory (enable missivesp))))


(defthm fwd-missivesp
  ;; as missivesp is disabled we prove this rule to add
  ;; the content of missivesp as hypotheses
  (implies (missivesp M NodeSet)
           (and (Validfields-M M)
                (subsetp (M-orgs M) NodeSet)
                (subsetp (M-dests M) NodeSet)
                (True-listp M)
                (No-duplicatesp (M-ids M))))
  :rule-classes :forward-chaining)


(defthm v-ids_G_nt_sigma_subsetp-v-ids-delayed/rtg
  ;; this lemma is used in the subsequent proofs
  ;; it makes a fact "explicit"
  (let ((NodeSet (NodeSetGenerator Params)))
    (mv-let (scheduled/rtg delayed/rtg newAtt)
            (scheduling (routing M NodeSet) att)
            (declare (ignore scheduled/rtg))
            (implies (and (Missivesp M NodeSet)
                          (ValidParamsp Params))
                     (subsetp
                      (V-ids
                       (genoc_t-non-tail-comp
                        (extract-sublst M (v-ids delayed/rtg))
                        NodeSet newAtt))
                      (V-ids delayed/rtg)))))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use
           ((:instance subsetp-scheduled-delayed-ids
                       (TrLst (Routing M (NodeSetGenerator Params))))
            (:instance trlstp-delayed
                       (TrLst (routing M (NodeSetGenerator Params))))
            ;; the following is required because in the conclusion of the
            ;; rule there is no call to extract-sublst
            (:instance v-ids-GeNoC_t-non-tail-comp
                       (M (extract-sublst
                           M
                           (V-ids (mv-nth 1 (scheduling
                                             (routing M (NodeSetGenerator Params))
                                             att)))))
                       (att (mv-nth 2 (scheduling
                                       (routing M (NodeSetGenerator Params))
                                       att)))))
           :in-theory (disable subsetp-scheduled-delayed-ids
                               trlstp-delayed
                               v-ids-GeNoC_t-non-tail-comp
                               trlstp missivesp))))


;; Scheduled/Rtg does not modify frames
;; ---------------------------------------

(defthm s/d-travel-v-frms
  (implies (and (TrLstp sd-trlst)
                (s/d-travel-correctness sd-trlst TrLst/sd-ids))
           (equal (V-frms sd-trlst) (V-frms TrLst/sd-ids))))

(defthm m-frms-to-v-frms
  ;; this rule is only used to rewrite the next theorem to
  ;; the previous one.
  (equal (m-frms (toMissives x))
         (v-frms x)))

(defthm Scheduled-v-frms-m-frms
  ;; we prove that the frames of the scheduled travels
  ;; are equal to the frames of the conversion of the initial list of travels
  ;; filtered according to the ids of the scheduled travels
  (mv-let (Scheduled Delayed newAtt)
          (scheduling TrLst att)
          (declare (ignore Delayed newAtt))
          (implies (and (TrLstp TrLst)
                        (ValidParamsp Params))
                   (equal
                    (V-frms scheduled)
                    (M-frms
                     (ToMissives (extract-sublst TrLst
                                                 (v-ids scheduled)))))))
  :hints (("GOAL"
           :use ((:instance s/d-travel-v-frms
                            (sd-trlst
                             (mv-nth 0 (scheduling TrLst att)))
                            (TrLst/sd-ids
                           (extract-sublst
                            TrLst
                            (v-ids
                             (mv-nth 0 (scheduling TrLst att))))))
               (:instance scheduled-travels-correctness))
           :in-theory (disable TrLstp s/d-travel-v-frms mv-nth))))

(in-theory (disable m-frms-to-v-frms))

(defthm Scheduled/Rtg_not_modify_frames
  ;; we prove the the frames of the scheduled travels produced
  ;; by scheduling and routing are equal to the frames
  ;; of the initial list of missives
  (let ((NodeSet (NodeSetGenerator Params)))
  (mv-let (Scheduled/Rtg Delayed/Rtg newAtt)
          (scheduling (routing M NodeSet) att)
          (declare (ignore Delayed/Rtg newAtt))
          (implies (and (Missivesp M NodeSet)
                        (ValidParamsp Params))
                   (equal (V-frms Scheduled/Rtg)
                          (M-frms
                           (extract-sublst
                            M (v-ids Scheduled/Rtg)))))))
  :hints (("GOAL"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize fertilize)
           :use ((:instance Scheduled-v-frms-m-frms
                            (TrLst (routing M (NodeSetGenerator Params))))
                 (:instance subsetp-scheduled-delayed-ids
                            (TrLst (routing M (NodeSetGenerator Params)))))
           :in-theory (disable TrLstp Missivesp
                               subsetp-scheduled-delayed-ids
                               scheduled-v-frms-m-frms))))

(defthm correctroutesp-vm-frms-gc1
  ;; the correctness of routes and equality of frames imply
  ;; the main predicate (correctness of genoc_t-non-tail-comp)
  (implies (and (correctroutesp L (extract-sublst M (v-ids L))
                                NodeSet)
                (equal (V-frms L)
                       (m-frms (extract-sublst M (v-ids L)))))
           (Genoc_T-Correctness1 L
                                 (extract-sublst m (v-ids L)))))

(defthm GC1_scheduled/Rtg
  ;; we prove the correctness of the scheduled travels
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (And (missivesp M NodeSet)
                  (ValidParamsp Params))
             (mv-let (scheduled/rtg delayed/rtg newAtt)
                     (scheduling (routing M NodeSet) att)
                     (declare (ignore delayed/rtg newAtt))
                     (genoc_t-correctness1
                      scheduled/rtg
                      (extract-sublst M (v-ids scheduled/rtg))))))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize fertilize)
           :use
           ((:instance Scheduled/Rtg_not_modify_frames)
            (:instance subsetp-scheduled-delayed-ids
                       (TrLst (Routing M (NodeSetGenerator Params))))
            (:instance
             scheduling-preserves-route-correctness
             (NodeSet (NodeSetGenerator Params))
             (TrLst (routing M (NodeSetGenerator Params))))
            (:instance correctroutesp-vm-frms-gc1
                       (NodeSet (NodeSetGenerator Params))
                       (L (mv-nth 0 (scheduling
                                     (routing m (NodeSetGenerator Params))
                                     att)))))
           :in-theory (disable TrLstp Missivesp
                               Correctroutesp-Vm-Frms-Gc1
                               subsetp-scheduled-delayed-ids
                               Scheduling-Preserves-Route-Correctness
                               Scheduled/Rtg_not_modify_frames))))

(defthm GeNoC_t-thm
  ;; now we can prove the correctness of GeNoC_t
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (Missivesp M NodeSet)
                  (ValidParamsp Params))
             (mv-let (Cplt Abt)
                     (GeNoC_t M NodeSet att nil)
                     (declare (ignore Abt))
                     (GeNoC_t-correctness Cplt M))))
  :otf-flg t
  :hints (("GOAL"
           :induct (GeNoC_t-non-tail-comp M (NodeSetGenerator Params) Att)
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable TrLstp Missivesp)
           :do-not-induct t)
          ("Subgoal *1/2"
           :use
           ((:instance trlstp-delayed
                       (TrLst (routing M (NodeSetGenerator Params))))
            (:instance subsetp-scheduled-delayed-ids
                       (TrLst (Routing M (NodeSetGenerator Params))))
            (:instance GC1_scheduled/Rtg))
           :in-theory (e/d (mv-nth)
                           (TrLstp missivesp trlstp-delayed
                                   subsetp-scheduled-delayed-ids
                                   GC1_scheduled/Rtg)))))

;;------------------------------------------------------------
;;      Definition and Validation of GeNoC
;;------------------------------------------------------------

;; we load the generic definitions of the interfaces
(include-book "GeNoC-interfaces")

;; ComputeMissives
;; --------------
(defun ComputeMissives (Transactions)
  ;; apply the function p2psend to build a list of missives
  ;; from a list of transactions
  (if (endp Transactions)
      nil
    (let* ((trans (car Transactions))
           (id (IdT trans))
           (org (OrgT trans))
           (msg (MsgT trans))
           (dest (DestT trans)))
      (cons (list id org (p2psend msg) dest)
            (ComputeMissives (cdr Transactions))))))

;; ComputeResults
;; -------------
(defun ComputeResults (TrLst)
  ;; apply the function p2precv to build a list of results
  ;; from a list of travels
  (if (endp TrLst)
      nil
    (let* ((tr (car TrLst))
           (id (IdV tr))
           (r (car (routesV tr)))
           (dest (car (last r)))
           (frm (FrmV tr)))
      (cons (list id dest (p2precv frm))
            (ComputeResults (cdr TrLst))))))

;; GeNoC
;; -----
(defun GeNoC (Trs NodeSet att)
  ;; main function
  (mv-let (Responses Aborted)
          (GeNoC_t (ComputeMissives Trs) NodeSet att nil)
          (mv (ComputeResults Responses) Aborted)))

;; GeNoC Correctness
;; -----------------
(defun genoc-correctness (Results Trs/ids)
  ;; Trs/ids is the initial list of transactions filtered according
  ;; to the ids of the list of results.
  ;; We check that the messages and the destinations of these two lists
  ;; are equal.
  (and (equal (R-msgs Results)
              (T-msgs Trs/ids))
       (equal (R-dests Results)
              (T-dests Trs/ids))))

(defthm M-ids-computesmissives
  ;; lemma for the next defthm
  (equal (M-ids (computemissives Trs))
         (T-ids trs)))

(defthm missivesp-computemissives
  (implies (transactionsp trs NodeSet)
           (missivesp (ComputeMissives trs) NodeSet)))


(defun all-frms-equal-to-p2psend (TrLst Trs)
  ;; check that every frame of TrLst is equal to the application
  ;; of p2psend to the corresponding message in the list of
  ;; transactions Trs
  (if (endp TrLst)
      (if (endp Trs)
          t
        nil)
    (let* ((tr (car TrLst))
           (trans (car Trs))
           (tr-frm (FrmV tr))
           (t-msg (MsgT trans)))
      (and (equal tr-frm (p2psend t-msg))
           (all-frms-equal-to-p2psend (cdr TrLst) (cdr Trs))))))

(defthm GC1-=>-all-frms-equal-to-p2psend
  (implies (GeNoC_t-correctness1 TrLst (ComputeMissives Trs))
           (all-frms-equal-to-p2psend TrLst Trs)))

(defthm all-frms-equal-r-msgs-t-msgs
  ;; if frames have been computed by p2psend then
  ;; computeresults applies p2precv. We get thus the initial msg.
  (implies (and (all-frms-equal-to-p2psend TrLst Trs)
                (validfields-trlst TrLst))
           (equal (R-msgs (ComputeResults TrLst))
                  (T-msgs Trs))))

(defthm R-ids-computeresults
  (equal (R-ids (computeresults x))
         (V-ids x)))

(defthm m-dests-computemissives
  (equal (M-dests (computeMissives trs))
         (T-dests trs)))


(defthm GC1-r-dest-m-dests
  (implies (and (GeNoC_t-correctness1 TrLst M/TrLst)
                (validfields-trlst TrLst)
                (Missivesp M/TrLst NodeSet))
           (equal (R-dests (ComputeResults TrLst))
                  (M-dests M/TrLst))))

(defthm validfields-append
  ;; lemma for the next defthm
  (implies (and (validfields-trlst l1)
                (validfields-trlst l2))
           (validfields-trlst (append l1 l2))))


(defthm validfields-trlst-GeNoC_nt
  ;; to use the lemma all-frms-equal-to-p2psend we need to establish
  ;; that GeNoC_nt contains travels with validfields
  ;; and that it contains no duplicated ids
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (Missivesp M NodeSet)
                  (ValidParamsp Params))
             (validfields-trlst (genoc_t-non-tail-comp M NodeSet att))))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :induct (Genoc_T-Non-Tail-Comp M (NodeSetGenerator Params) att))
          ("Subgoal *1/2"
           :use ((:instance trlstp-delayed
                            (TrLst (Routing M (NodeSetGenerator Params))))
                 (:instance trlstp-scheduled
                            (TrLst (Routing M (NodeSetGenerator Params))))
                 (:instance Missivesp-mv-nth-1-scheduling
                            (TrLst (routing M (NodeSetGenerator Params)))))
           :in-theory (disable trlstp-delayed trlstp-scheduled
                               Missivesp-mv-nth-1-scheduling))))

;; the next four lemmas are similar to those used to prove
;; the lemma tomissives-extract-sublst .... (proof by analogy)

(defthm computemissives-append
  (equal (computemissives (append a b))
         (append (computemissives a) (computemissives b))))

(defthm member-equal-assoc-equal-not-nil-t-ids
  ;; if e is an Id of a travel of L
  ;; then (assoc-equal e L) is not nil
  (implies (and (member-equal e (T-ids Trs))
                (Validfields-T Trs))
           (assoc-equal e Trs)))

(defthm computemissives-assoc-equal
  ;; if (assoc-equal e L) is not nil then we can link
  ;; assoc-equal and computemissives as follows:
  ;; (this lemma is needed to prove the next defthm)
  (implies (assoc-equal e L)
           (equal (computemissives (list (assoc-equal e L)))
                  (list (assoc-equal e (computemissives L))))))

(defthm computemissives-extract-sublst
  ;; calls of computemissives are moved into calls
  ;; of extract-sublst
  (implies (and (subsetp ids (t-ids trs))
                (validfields-t trs))
           (equal (ComputeMissives (extract-sublst trs ids))
                  (extract-sublst (ComputeMissives trs) ids)))
  :otf-flg t
  :hints (("GOAL"
           :induct (extract-sublst Trs ids)
           :do-not-induct t
           :in-theory (disable computemissives append))))


(defthm m-dest-t-dests-extract-sublst
  (implies (and (subsetp ids (t-ids trs))
                (validfields-t trs))
           (equal (m-dests (extract-sublst (computemissives Trs) ids))
                  (t-dests (extract-sublst trs ids))))
  :hints (("GOAL"
           :do-not-induct t
           :use (:instance m-dests-computemissives
                           (Trs (extract-sublst Trs ids)))
           :in-theory (disable m-dests-computemissives))))

(defthm fwd-chaining-transactionsp
  (implies (Transactionsp Trs NodeSet)
           (and (validfields-t Trs)
                (true-listp trs)
                (subsetp (t-orgs trs) nodeset)
                (subsetp (t-dests trs) nodeset)
                (no-duplicatesp-equal (t-ids trs))))
  :rule-classes :forward-chaining)

(defthm GeNoC-is-correct
  (let ((NodeSet (NodeSetGenerator Params)))
    (mv-let (results aborted)
            (GeNoC Trs NodeSet att)
            (declare (ignore aborted))
            (implies (and (Transactionsp Trs NodeSet)
                          (equal NodeSet (NodeSetGenerator Params))
                          (ValidParamsp Params))
                     (GeNoC-correctness
                      results
                      (extract-sublst Trs (R-ids results))))))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use ((:instance GeNoC_t-thm
                            (M (ComputeMissives Trs)))
                 (:instance v-ids-GeNoC_t-non-tail-comp
                            (M (computemissives trs)))
                 (:instance all-frms-equal-r-msgs-t-msgs
                            (TrLst (genoc_t-non-tail-comp
                                    (computeMissives trs)
                                    (Nodesetgenerator params) att))
                            (Trs (extract-sublst Trs
                                                 (v-ids
                                                  (genoc_t-non-tail-comp
                                                   (computeMissives trs)
                                                   (nodesetgenerator params)
                                                   att)))))
                 (:instance GC1-r-dest-m-dests
                            (TrLst (genoc_t-non-tail-comp
                                    (computeMissives trs)
                                    (nodesetgenerator params) att))
                            (M/TrLst
                             (extract-sublst (ComputeMissives Trs)
                                             (V-ids (genoc_t-non-tail-comp
                                                     (computeMissives trs)
                                                     (nodesetgenerator params)
                                                     att))))
                            (NodeSet (Nodesetgenerator params))))
           :in-theory (e/d (mv-nth)
                           (GeNoC_t-thm missivesp trlstp
                            all-frms-equal-r-msgs-t-msgs
                            v-ids-GeNoC_t-non-tail-comp
                            transactionsp GC1-r-dest-m-dests)))))
