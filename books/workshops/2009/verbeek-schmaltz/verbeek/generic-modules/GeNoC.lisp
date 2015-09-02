#|$ACL2s-Preamble$;
;; julien schmaltz
;; top level module of GeNoC
;; june 20th 2005
;; file: GeNoC.lisp
;;Amr helmy
;;24st january 2008
;;Edited 3rd march 2008 to add the round robin
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "GeNoC-scheduling")
(include-book "GeNoC-routing")
(include-book "GeNoC-departure")
(include-book "GeNoC-simulation")
(in-theory (disable mv-nth))

(defun genoc_t (m nodeset measure trlst accup time ntkstate order)
  ;; the composition of routing and scheduling is built by function genoc_t.
  ;; it takes as arguments:
  ;; - a list of missives, m
  ;; - the set of existing nodes, nodeset
  ;; - the measure provided by the scheduler
  ;; - an accumulator of arrived messages
  ;; - an accumulator of network states for simulation
  ;; - the time
  ;; - the state of the network
  ;; - an ordering
  ;; it returns:
  ;; - the arrived messages
  ;; - the en route messages
  ;; - the network state accumulator

  ;; the measure is set to the measure defined by the scheduler
  (declare (xargs :measure (acl2-count measure)))
  (if (endp m)
    ;; no more messages to send
    (mv trlst nil accup)
    ;; else
    (mv-let (delayed departing)
          ;; call R4D to determine which missives are ready for departure
          (readyfordeparture m nil nil time)
          ;; determine set of routes for all departing missives
          (let ((v (routing departing nodeset)))
            (cond ((not (legal-measure measure v nodeset ntkstate order))
                  ;; illegal measure supplied
                   (mv trlst m accup))
                  ;; check if it is possible to schedule
                  ((scheduling-assumptions v nodeset ntkstate order)
                   ;; schedule and recursivily call genoc_t
                   (mv-let (newtrlst arrived newmeasure newntkstate)
                           (scheduling v nodeset ntkstate order)
                           (genoc_t  (append newtrlst delayed)
                                     nodeset
                                     newmeasure
                                     (append arrived trlst)
                                     (append accup (list (extract-simulation newntkstate)))
                                     (+ 1 time)
                                     newntkstate
                                     (get_next_priority order))))
                  (t
                   ;; scheduler has instructed to terminate
                   (mv trlst m accup)))))))



;; correctness of genoc_t
;; ----------------------
(defun correctroutes-genoc_t (routes m-dest)
  ;; genoc_t is correct if every element ctr of the output list
  ;; is such that (a) frmv(ctr) = frmtm(m) and (b) forall r in
  ;; routesv(ctr) last(r) = desttm(m). for the m such that
  ;; idm(m) = idv(ctr).
  ;; this function checks that (b) holds.
  (if (endp routes)
      t
    (let ((r (car routes)))
      (and (equal (car (last r)) m-dest)
           (correctroutes-genoc_t (cdr routes) m-dest)))))

(defun genoc_t-correctness1 (trlst m/trlst)
  ;; we complement the correctness of genoc_t
  (if (endp trlst)
      (if (endp m/trlst)
          t
        nil)
    (let* ((tr (car trlst))
           (v-frm (frmv tr))
           (routes (routesv tr))
           (m (car m/trlst))
           (m-frm (frmm m))
           (m-dest (destm m)))
      (and (equal v-frm m-frm)
           (correctroutes-genoc_t routes m-dest)
           (genoc_t-correctness1 (cdr trlst)  (cdr m/trlst))))))

(defun genoc_t-correctness (trlst m)
  ;; before checking correctness we filter m
  ;; according to the ids of trlst
  (let ((m/trlst  (extract-sublst (tomissives m) (v-ids trlst))))
    (genoc_t-correctness1 trlst m/trlst)))


;; non tail definition of genoc_t
;; ------------------------------
(defun genoc_t-non-tail-comp (m nodeset measure time ntkstate order)
  (declare (xargs :measure (acl2-count measure)))
  ;; we define a non tail function that computes the
  ;; first output of genoc_t, i.e the completed transactions
  (if (endp m)
    nil
    (mv-let (delayed departing)
            (readyfordeparture m nil nil time)
            (let ((v (routing departing nodeset)))
              (cond ((not (legal-measure measure v nodeset ntkstate order))
                    nil)
                    ((scheduling-assumptions v nodeset ntkstate order)
                     (mv-let (newtrlst arrived newmeasure newntkstate)
                             (scheduling v nodeset ntkstate order)
                             (append (genoc_t-non-tail-comp (append newtrlst delayed)
                                                            nodeset
                                                            newmeasure
                                                            (+ time 1)
                                                            newntkstate
                                                            (get_next_priority order))
                                     arrived)))
                    (t nil))))))

;; we now prove that this function is right

(defthm true-listp-genoc_t-non-tail-comp     ;; ok
  (implies (true-listp m)
           (true-listp (genoc_t-non-tail-comp m nodeset measure  time ntkstate order)))
  :rule-classes :type-prescription)

(defthm genoc_t-non-tail-=-tail-comp      ;; ok
  (equal (mv-nth 0 (genoc_t m nodeset measure trlst accup time ntkstate order))
         (append (genoc_t-non-tail-comp m nodeset measure time ntkstate order)
                 trlst)))


;; proof of genoc_t correctness
;; ----------------------------

;; first we add a lemma that tells acl2 that
;; converting the travels that are routed and delayed
;; produced a valid list of missives
(defthm tmissivesp-mv-nth-0-scheduling-routing      ;; ok
  (let ((nodeset (nodesetgenerator params)))
    (implies (and (tmissivesp m nodeset)
                  (validparamsp params))
             (tmissivesp (mv-nth 0  (scheduling (routing m nodeset)
                                                nodeset  ntkstate
                                                order)) nodeset )))
  :hints (("goal"
           :use ((:instance  tmissivesp-mv-nth-0-scheduling
                             (trlst  (routing m (nodesetgenerator params)))))
           :in-theory (disable trlstp tmissivesp))))


;; the next three theorems are to be moved in to the file GeNoC-misc
;; the recursive call of genoc_t-non-tail-comp calls append
;; we put the append at the top.
;; to do so we add the two rules below:

(defthm v-ids-append
  ;; the ids of an append is the append of the ids
  (equal (v-ids (append a b))
         (append (v-ids a) (v-ids b))))

(defthm tm-ids-append
  ;; the ids of an append is the append of the ids
  (equal (tm-ids (append a b))
         (append (tm-ids a) (tm-ids b))))

(defthm extract-sublst-append
  ;; filtering according to an append is the append
  ;; of the filtering.
  (equal (extract-sublst m (append id1 id2))
         (append (extract-sublst m id1)
                 (extract-sublst m id2))))


;; then to split the proof is two cases, we replace the
;; append by a conjunction.
;; the rule below allows this decomposition:

(defthm correctroutess1-append
  (implies (and (equal (len a) (len c))
                (equal (len b) (len d)))
           (equal (genoc_t-correctness1 (append a b)
                                        (append c d))
                  (and (genoc_t-correctness1 a c)
                       (genoc_t-correctness1 b d)))))




;; now we need to prove some lemmas so that previous rules
;; (from genoc-misc) about extract-sublst, tomissives, etc could
;; fire.

;next thoerem is to prove that the append of the result of the
;scheduling to a a list of tmissives will result in a tmissives list

(defthm sched-rout-missivesp-append
  (implies (and (validparamsp params)
                (not-in (tm-ids x) (tm-ids y))
                (tmissivesp x (nodesetgenerator params))
                (tmissivesp y (nodesetgenerator params)))
           (tmissivesp
            (append
             (mv-nth 0
                     (scheduling
                      (routing x (nodesetgenerator params))
                      (nodesetgenerator params) ntkstate order)) y)
            (nodesetgenerator params)))
  :hints (("goal"
           :use ((:instance tmissivesp-append-tmissivesp
                            (a (mv-nth 0
                                       (scheduling
                                        (routing x
                                                 (nodesetgenerator
                                                  params))
                                                  (nodesetgenerator
                                                   params)
                                                  ntkstate order)))
                            (b y))
                 (:instance tmissivesp-newTrlst
                            (trlst (routing x (nodesetgenerator params))))
                 (:instance trlstp-routing (m x))
                 (:instance subsetp-arrived-newtrlst-ids
                            (trlst (routing x (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params)))
                 (:instance ids-routing (m x))))))

(defthm v-ids-genoc_t-non-tail-comp      ;; ok
  ;; the ids of the output of genoc_t-non-tail-comp is a
  ;; subset of those of m
  ;; for this theorem the rule ids-routing is useful
  (let ((nodeset (nodesetgenerator params)))
    (implies (and (tmissivesp m nodeset)
                  (validparamsp params))
             (let ((gnt
                    (genoc_t-non-tail-comp m nodeset measure time ntkstate order)))
               (subsetp (v-ids gnt) (tm-ids m)))))
  :hints (("goal"
           :in-theory
           (disable mv-nth tmissivesp trlstp))
          ("subgoal *1/4"
           :do-not '(eliminate-destructors generalize)
           :use ((:instance tmissivesp-append-tmissivesp
                            (nodeset (nodesetgenerator params))
                            (b (mv-nth 0 (readyfordeparture m nil nil time)))
                            (a (mv-nth 0
                                       (scheduling
                                        (routing
                                         (mv-nth
                                          1
                                          (readyfordeparture m nil nil
                                                             time))
                                         (nodesetgenerator params))
                                         (nodesetgenerator params)
                                        ntkstate
                                        order ))))
                 (:instance subsetp-arrived-newtrlst-ids
                            (trlst (routing (mv-nth 1
                                                    (readyfordeparture
                                                     m nil nil time) )
                                            (nodesetgenerator
                                             params)))
                            (nodeset (nodesetgenerator params)))
                 (:instance ids-routing (m (mv-nth 1
                                                   (readyfordeparture
                                                    m nil nil
                                                    time)))))
           :in-theory (disable mv-nth ids-routing
                               subsetp-arrived-newtrlst-ids
                               tmissivesp trlstp))
          ("subgoal *1/2"
           :in-theory (disable TM-IDS-APPEND GENOC_T-NON-TAIL-COMP TMISSIVESP)
           :use ((:instance ids-routing (m (mv-nth 1
                                                   (readyfordeparture
                                                    m nil nil time))))
                 (:instance tmissivesp-append-tmissivesp
                            (nodeset (nodesetgenerator params))
                            (b (mv-nth 0 (readyfordeparture m nil nil time)))
                            (a (mv-nth 0 (scheduling
                                          (routing
                                           (mv-nth
                                            1
                                            (readyfordeparture m nil
                                                               nil
                                                               time))
                                           (nodesetgenerator params))
                                           (nodesetgenerator params)
                                          ntkstate order))))))
          ("subgoal *1/2''" :in-theory (enable TM-IDS-APPEND GENOC_T-NON-TAIL-COMP TMISSIVESP))))


(defthm not-in-v-ids-genoc_t-non-tail-comp      ;; ok
  ;; if the ids of a list have no common element with
  ;; another ids then the output of genoc_t-non-tail-comp does
  ;; not introduce any new id
  (let ((nodeset (nodesetgenerator params)))
    (implies (and (not-in (tm-ids delayed) sched-ids)
                  (tmissivesp delayed nodeset)
                  (validparamsp params))
             (not-in (v-ids (genoc_t-non-tail-comp delayed nodeset measure
                                                   time ntkstate
                                                   order))
                     sched-ids)))
  :otf-flg t
  :hints (("goal"
           :do-not-induct t
           :in-theory (disable tmissivesp))))

(defthm v-ids-genoc_t-non-tail-comp-no-dup       ;; ok
  ;; the ids of the output of genoc_t-non-tail-comp have no dup
  (let ((nodeset (nodesetgenerator params)))
    (implies (and (tmissivesp m nodeset)
                  (validparamsp params))
             (let ((gnt (genoc_t-non-tail-comp m nodeset measure time
                                               ntkstate order)))
               (no-duplicatesp-equal (v-ids gnt)))))
  :otf-flg t
  :hints (("goal"
           :do-not '(eliminate-destructors generalize)
           :do-not-induct t
           :induct (genoc_t-non-tail-comp m (nodesetgenerator params)
                                          measure time ntkstate order)
           :in-theory (disable tmissivesp trlstp ))
          ("subgoal *1/3"
           :use ((:instance trlstp-routing
                            (m (mv-nth 1 (readyfordeparture m nil nil time))))
                 (:instance not-in->not-insched
                            (x (v-ids
                                (mv-nth
                                 1
                                 (scheduling
                                  (routing
                                   (mv-nth 1
                                           (readyfordeparture m nil
                                                              nil
                                                              time))
                                   (nodesetgenerator params))

                                  (nodesetgenerator params) ntkstate order))))
                            (y (tm-ids
                                (mv-nth 1 (readyfordeparture m nil nil time))))
                            (z(tm-ids
                               (mv-nth 0 (readyfordeparture m nil nil time)))))
                 (:instance not-in-2->not-in-append
                            (x (tm-ids
                                (mv-nth 0
                                        (scheduling
                                         (routing
                                          (mv-nth
                                           1 (readyfordeparture m nil
                                                                nil
                                                                time))
                                          (nodesetgenerator params))

                                         (nodesetgenerator params)
                                         ntkstate order))))
                            (y (tm-ids
                                (mv-nth 0 (readyfordeparture m nil nil time))))
                            (z (v-ids
                                (mv-nth
                                 1 (scheduling
                                    (routing (mv-nth
                                              1
                                              (readyfordeparture m nil
                                                                 nil
                                                                 time))
                                             (nodesetgenerator params))
                                     (nodesetgenerator params)
                                    ntkstate order)))))
                 (:instance not-in-v-ids-genoc_t-non-tail-comp
                            (delayed
                             (append
                              (mv-nth
                               0
                               (scheduling
                                (routing (mv-nth
                                          1
                                          (readyfordeparture m nil nil time))
                                         (nodesetgenerator params))

                                 (nodesetgenerator params)
                                ntkstate order))
                              (mv-nth 0
                                      (readyfordeparture m nil nil time))))

                            (measure
                             (mv-nth
                              2
                              (scheduling
                               (routing (mv-nth
                                         1
                                         (readyfordeparture m nil nil
                                                            time))
                                        (nodesetgenerator params))
                                (nodesetgenerator params)  ntkstate order)))
                            (sched-ids
                             (v-ids
                              (mv-nth
                               1
                               (scheduling
                                (routing
                                 (mv-nth 1 (readyfordeparture m nil
                                                              nil
                                                              time))
                                 (nodesetgenerator params))
                                 (nodesetgenerator params)ntkstate order))))
                            (time (+ 1 time))
                            (order (get_next_priority order))
                            (ntkstate
                             (mv-nth
                              3
                              (scheduling
                               (routing
                                (mv-nth
                                 1 (readyfordeparture m nil nil time))
                                (nodesetgenerator params))
                                (nodesetgenerator params) ntkstate order))))
                 (:instance not-in-1-0-ready-for-dept
                            (nodeset (nodesetgenerator params)))
                 (:instance subsetp-arrived-newtrlst-ids
                            (trlst (routing (mv-nth
                                             1
                                             (readyfordeparture m nil
                                                                nil
                                                                time))
                                            (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params)))
                 (:instance not-in-newtrlst-arrived
                            (trlst (routing (mv-nth
                                             1
                                             (readyfordeparture m nil
                                                                nil
                                                                time))
                                            (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params)))
                 (:instance trlstp-arrived
                            (trlst (routing (mv-nth 1
                                                    (readyfordeparture
                                                     m nil nil time))
                                            (nodesetgenerator params)))
                            (nodeset  (nodesetgenerator params))))
           :in-theory (e/d (trlstp)
                           (trlstp-arrived mv-nth trlstp
                                           not-in-v-ids-genoc_t-non-tail-comp
                                           tmissivesp)))
          ("subgoal *1/2.3'"
           :use ((:instance not-in-1-0-ready-for-dept-reverse
                            (nodeset (nodesetgenerator params)))))))

;; move to GeNoC-misc
(defthm tmissivesp-extract-sublst
  (let ((nodeset (nodesetgenerator params)))
    (implies (and (tmissivesp m nodeset)
                  (validparamsp params)
                  (true-listp ids)
                  (no-duplicatesp-equal ids)
                  (subsetp ids (tm-ids m)))
             (tmissivesp (extract-sublst m ids) nodeset)))
  :hints (("goal"
           :in-theory (disable tmissivesp))
          ("subgoal *1/1"
           :in-theory (enable tmissivesp))))
;; the following 7 theorems are intermediate lemmas to prove the
;; ultimate version
;; Tomissives-delayed-ultimate which is that too-missives newtrlst is
;; equal to tomissive to extract-sublst from the initial M based upon
;; the newtrlst's ids

(defthm tomissives-delayed/rtg
  ;; we prove that the conversion of the delayed travels
  ;; into a list of missives is equal to the filtering
  ;; of the initial list of missives m according to the ids
  ;; of the delayed travels.
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (newtrlst/rtg arrived/rtg newmeasure newntkstate)
            (scheduling (routing m nodeset)  nodeset  ntkstate order)
            (declare (ignore arrived/rtg newmeasure newntkstate))
            (implies (and (tmissivesp m nodeset)
                          (validparamsp params))
                     (equal (tomissives newtrlst/rtg)
                            (extract-sublst (tomissives m)
                                            (tm-ids newtrlst/rtg))))))
  :otf-flg t
  :hints (("goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize fertilize)
           :use ((:instance totmissives-extract-sublst
                            (l (routing m (nodesetgenerator params)))
                            (ids (tm-ids
                                  (mv-nth
                                   0 (scheduling
                                      (routing m (nodesetgenerator params))
                                       (nodesetgenerator params)
                                      ntkstate order)))))
                 (:instance newtrlst-travel-correctness
                            (trlst (routing m (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params)))
                 (:instance subsetp-arrived-newtrlst-ids
                            (trlst (routing m (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params))))
           :in-theory (disable binary-append nth-with-large-index
                               extract-sublst tm-ids
                               member-equal-tm-ids-assoc-equal
                               tomissives m-ids assoc-equal trlstp
                               missivesp totmissives-extract-sublst
                               len subsetp-arrived-newtrlst-ids))))

(defthm newtrlst-subsetp-ready-4-dept
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (newtrlst/rtg arrived/rtg newmeasure newntkstate)
            (scheduling
             (routing (mv-nth 1
                              (readyfordeparture m nil nil time))
                      nodeset)
              nodeset  ntkstate order)
            (declare (ignore arrived/rtg newmeasure newntkstate))
            (implies (and (tmissivesp m nodeset)
                          (validparamsp params))
                     (subsetp(tm-ids newtrlst/rtg)
                             (tm-ids (extract-sublst
                                      m
                                      (tm-ids
                                       (mv-nth
                                        1
                                        (readyfordeparture m
                                                           nil
                                                           nil
                                                           time)))))))))
  :hints (("goal"
           :in-theory (disable tm-orgs extract-sublst m-ids
                               idm nfix m-ids
                               mv-nth-0-scheduling-on-zero-measure
                               id-not-eq-car-member-cdr-missives
                               assoc-equal
                               subset-ready-for-departure-3
                               not-in-1-0-ready-for-dept
                               NO-DUPLICATESP
                               checkroutes-subsetp-validroute
                               true-listp-mv-nth-1-sched-2
                               subset-ready-for-departure-2
                               true-listp-last last consp-last
                               subsetp-arrived-newtrlst-ids
                               len nth tmissivesp-extract-sublst
                               tmissivesp-extract trlstp-routing
                               true-listp
                               leq-position-equal-len
                               member-equal-m-ids-assoc-equal v-ids
                               nfix )

           :use ((:instance subsetp-arrived-newtrlst-ids
                            (trlst
                             (routing (mv-nth
                                       1
                                       (readyfordeparture m nil nil
                                                          time))
                                      (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params)))
                 (:instance trlstp-routing
                            (m (mv-nth 1 (readyfordeparture m nil nil time))))
                 (:instance subset-ready-for-departure-3
                            (nodeset (nodesetgenerator params)))
                 (:instance tmissivesp-ready-4-departure-mv-1
                            (nodeset (nodesetgenerator params)))
                 (:instance subset-ready-for-departure-2
                            (nodeset (nodesetgenerator params)))
                 (:instance tmissivesp-equal-subsetp
                            (nodeset (nodesetgenerator params))
                            (x (mv-nth 1 (readyfordeparture m nil nil
                                                            time)))
                            (y m))
                 (:instance tmissivesp-ready-4-departure-mv-1
                            (nodeset (nodesetgenerator params)))))))




(defthm newtrlst-subsetp-M
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (newtrlst/rtg arrived/rtg new newntkstate)
            (scheduling (routing (mv-nth 1 (readyfordeparture m nil nil time)) nodeset)  nodeset  ntkstate order)
            (declare (ignore arrived/rtg new newntkstate))
            (implies (and (tmissivesp m nodeset)
                          (validparamsp params))
                     (subsetp (tm-ids newtrlst/rtg) (tm-ids m)))))
  :hints (("goal"
           :in-theory (disable extract-sublst
                               m-ids
                               mv-nth-0-scheduling-on-zero-measure
                               assoc-equal
                               subset-ready-for-departure-3
                               not-in-1-0-ready-for-dept
                               checkroutes-subsetp-validroute
                               true-listp-mv-nth-1-sched-2
                               len nth tmissivesp-extract-sublst
                               tmissivesp-extract
                               leq-position-equal-len
                               member-equal-m-ids-assoc-equal v-ids
                               nfix )
           :use
           ((:instance tmissivesp-ready-4-departure-mv-1
                       (nodeset (nodesetgenerator params)))
            (:instance subsetp-arrived-newtrlst-ids
                       (trlst (routing
                               (mv-nth
                                1
                                (readyfordeparture m nil nil time))
                               (nodesetgenerator params)))
                       (nodeset (nodesetgenerator params)))
            (:instance trlstp-routing
                       (m (mv-nth 1 (readyfordeparture
                                     m nil nil time))))
            (:instance subset-ready-for-departure-2
                       (nodeset (nodesetgenerator params)))))))

(defthm taking-the-to-missives-out
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (newtrlst/rtg arrived/rtg newmeasure newntkstate)
            (scheduling
             (routing
              (mv-nth
               1
               (readyfordeparture m nil nil time)) nodeset)
               nodeset  ntkstate order)
            (declare (ignore arrived/rtg newmeasure newntkstate))
            (implies (and (tmissivesp m nodeset)
                          (validparamsp params))
                     (equal
                      (extract-sublst
                       (tomissives
                        (extract-sublst
                         m
                         (tm-ids (mv-nth
                                  1
                                  (readyfordeparture m nil nil time)))))
                       (tm-ids newtrlst/rtg))
                      (tomissives
                       (extract-sublst
                        (extract-sublst
                         m
                         (tm-ids (mv-nth 1 (readyfordeparture m nil
                                                              nil
                                                              time))))
                        (tm-ids newtrlst/rtg)))))))
  :hints (("goal"
           :in-theory (disable tmissivesp tomissives-extract-sublst)
           :use
           ((:instance tomissives-extract-sublst
                       (nodeset (nodesetgenerator params))
                       (ids (tm-ids
                             (mv-nth
                              0
                              (scheduling
                               (routing
                                (mv-nth 1 (readyfordeparture m nil nil time))
                                (nodesetgenerator params))
                                 (nodesetgenerator params) ntkstate order))))
                            (l (extract-sublst
                                m (tm-ids
                                   (mv-nth
                                    1
                                    (readyfordeparture m nil nil time))))))
            (:instance subset-ready-for-departure-2
                       (nodeset (nodesetgenerator params)))
            (:instance subset-ready-for-departure-3
                       (nodeset (nodesetgenerator params)))
            (:instance tmissivesp-extract
                       (ids (tm-ids
                             (mv-nth 1 (readyfordeparture m nil nil time))))
                       (nodeset (nodesetgenerator params)))
                 (:instance tmissivesp-ready-4-departure-mv-1
                            (nodeset (nodesetgenerator params)))))
          ("subgoal 2" :in-theory (disable tmissivesp)
           :use
           ((:instance tmissivesp-ready-4-departure-mv-1
                       (nodeset (nodesetgenerator params)))
            (:instance subset-ready-for-departure-2
                       (nodeset (nodesetgenerator params)))
            (:instance subset-ready-for-departure-3
                       (nodeset (nodesetgenerator params)))
            (:instance tmissivesp-extract
                       (ids
                        (tm-ids
                         (mv-nth 1 (readyfordeparture m nil nil time))))
                            (nodeset (nodesetgenerator params)))))
          ("subgoal 3"
           :use
           ((:instance subsetp-arrived-newtrlst-ids
                       (trlst (routing
                               (mv-nth 1 (readyfordeparture m nil nil
                                                            time))
                               (nodesetgenerator params)))
                       (nodeset (nodesetgenerator params)))
            (:instance trlstp-routing
                       (m (mv-nth 1 (readyfordeparture m nil nil time))))
            (:instance ids-routing
                       (m (mv-nth 1 (readyfordeparture m nil nil time))))
            (:instance tmissivesp-ready-4-departure-mv-1
                       (nodeset (nodesetgenerator params)))))))

(defthm tomissives-delayed-intermediate-2
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (newtrlst/rtg arrived/rtg newmeasure newntkstate)
            (scheduling (routing (mv-nth 1 (readyfordeparture m nil
                                                              nil
                                                              time))
                                 nodeset)  nodeset  ntkstate order)
            (declare (ignore arrived/rtg newmeasure newntkstate))
            (implies (and (tmissivesp m nodeset)
                          (validparamsp params))
                     (equal (tomissives newtrlst/rtg)
                            (extract-sublst
                             (tomissives
                              (extract-sublst
                               m
                               (tm-ids
                                (mv-nth
                                 1 (readyfordeparture m nil nil time)))))
                             (tm-ids newtrlst/rtg))))))
  :hints (("goal"
           :in-theory (disable TOMISSIVES LEN NTH-WITH-LARGE-INDEX TM-IDS
                               nth assoc-equal MEMBER-EQUAL-TM-IDS-ASSOC-EQUAL
                               MEMBER-EQUAL-M-IDS-ASSOC-EQUAL M-IDS)
           :use ((:instance tmissivesp-equal-subsetp
                            (y m)
                            (nodeset (nodesetgenerator params))
                            (x (mv-nth 1 (readyfordeparture m nil nil time))))
                 (:instance subset-ready-for-departure-3
                            (nodeset (nodesetgenerator params)))
                 (:instance tmissivesp-ready-4-departure-mv-1
                            (nodeset (nodesetgenerator params)))))))

(defthm tomissives-delayed-ultimate
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (newtrlst/rtg arrived/rtg newmeasure newntkstate)
            (scheduling (routing (mv-nth 1 (readyfordeparture m nil
                                                              nil
                                                              time))
                                 nodeset)  nodeset  ntkstate order)
            (declare (ignore arrived/rtg newmeasure newntkstate))
            (implies (and (tmissivesp m nodeset)
                          (validparamsp params))
                     (equal (tomissives newtrlst/rtg)
                            (tomissives
                             (extract-sublst m (tm-ids newtrlst/rtg)))))))
    :hints (("goal"
             :use ((:instance subsetp-arrived-newtrlst-ids
                              (trlst
                               (routing
                                (mv-nth 1
                                        (readyfordeparture m nil nil
                                                           time))
                                (nodesetgenerator params)))
                              (nodeset (nodesetgenerator params)))
                   (:instance trlstp-routing
                              (m (mv-nth 1
                                         (readyfordeparture m nil nil time))))
                   (:instance extract-sublst-cancel-tm
                              (id1 (tm-ids
                                    (mv-nth
                                     1 (readyfordeparture m nil nil time))))
                              (id2 (tm-ids newtrlst/rtg)))
                   (:instance tmissivesp-ready-4-departure-mv-1
                              (nodeset (nodesetgenerator params)))))))

(defthm tomissives-delayed-ultimate-bis
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (newtrlst/rtg arrived/rtg newmeasure newntkstate)
            (scheduling (routing (mv-nth 1 (readyfordeparture m nil
                                                              nil
                                                              time))
                                 nodeset)  nodeset  ntkstate order)
            (declare (ignore arrived/rtg newmeasure newntkstate))
            (implies (and (tmissivesp m nodeset)
                          (validparamsp params))
                     (equal (tomissives newtrlst/rtg)
                            (extract-sublst (tomissives  m )
                                            (tm-ids newtrlst/rtg))))))
  :hints (("goal"
           :in-theory (disable subset-ready-for-departure-2
                               idm tm-curs
                               tm-orgs id-not-eq-car-member-cdr
                               leq-position-equal-len default-car
                               mv-nth-0-scheduling-on-zero-measure
                               nth-with-large-index tmissivesp
                               true-listp-mv-nth-1-sched-2
                               validfield-route m-ids nfix
                               default-cdr
                               tomissives-extract-sublst
                               id-not-eq-car-member-cdr-missives m-ids
                               member-equal-tm-ids-assoc-equal
                               len tomissives-delayed-ultimate len
                               assoc-equal member-equal-m-ids-assoc-equal)
           :use
           ((:instance subsetp-arrived-newtrlst-ids
                       (trlst
                        (routing
                         (mv-nth 1 (readyfordeparture m nil nil time))
                         (nodesetgenerator params)))
                       (nodeset (nodesetgenerator params)))
            (:instance subset-ready-for-departure-2
                       (nodeset (nodesetgenerator params)))
            (:instance trlstp-routing
                       (m (mv-nth 1 (readyfordeparture m nil nil time))))
            (:instance tomissives-extract-sublst
                       (nodeset (nodesetgenerator params))
                       (l m)
                       (ids(tm-ids
                            (mv-nth
                             0
                             (scheduling
                              (routing
                               (mv-nth
                                1 (readyfordeparture m nil nil time))
                               (nodesetgenerator params))
                               (nodesetgenerator params) ntkstate order)))))
            (:instance tmissivesp-ready-4-departure-mv-1
                       (nodeset (nodesetgenerator params)))))))

(defthm v-ids_g_nt_sigma_subsetp-v-ids-newtrlst/rtg    ;; ok
  ;; this lemma is used in the subsequent proofs
  ;; it makes a fact "explicit"
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (newtrlst arrived newmeasure newntkstate)
            (scheduling (routing m nodeset)  nodeset  ntkstate order)
            (declare (ignore arrived newntkstate))
            (implies (and (tmissivesp m nodeset)
                          (validparamsp params))
                     (subsetp
                      (v-ids
                       (genoc_t-non-tail-comp
                        (extract-sublst m (tm-ids newtrlst))
                        nodeset newmeasure time ntkstate order))
                      (tm-ids newtrlst)))))
  :otf-flg t
  :hints (("goal"
           :do-not-induct t
           :use ((:instance subsetp-arrived-newtrlst-ids
                            (trlst (routing m (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params)))
                 (:instance tmissivesp-newTrlst
                            (trlst (routing m (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params)))
                 (:instance tmissivesp-extract-sublst
                            (ids (tm-ids (mv-nth
                                          0
                                          (scheduling
                                           (routing m
                                                    (nodesetgenerator params))

                                            (nodesetgenerator
                                                params)
                                           ntkstate order)))))
                 (:instance  fwd-tmissivesp
                             (nodeset (nodesetgenerator params)))
                 ;; the following is required because in the conclusion of the
                 ;; rule there is  call to extract-sublst
                 (:instance v-ids-genoc_t-non-tail-comp
                            (m
                             (extract-sublst
                              m
                              (tm-ids
                               (mv-nth
                                0
                                (scheduling
                                 (routing m (nodesetgenerator params))
                                  (nodesetgenerator params)
                                 ntkstate order)))))
                            (measure (mv-nth
                                  2
                                  (scheduling
                                   (routing m (nodesetgenerator params))
                                    (nodesetgenerator params)
                                   ntkstate order)))))
           :in-theory (disable subsetp-arrived-newtrlst-ids
                               mv-nth-0-scheduling-on-zero-measure
                               binary-append len tmissivesp-newtrlst
                               v-ids-genoc_t-non-tail-comp tm-ids nfix
                               trlstp tmissivesp))))

;; arrived/rtg does not modify frames
;; ---------------------------------------

(defthm s/d-travel-v-frms
  (implies (and (trlstp sd-trlst nodeset)
                (s/d-travel-correctness sd-trlst trlst/sd-ids))
           (equal (v-frms sd-trlst) (v-frms trlst/sd-ids))))

(defthm arrived-v-frms-m-frms        ;; ok
  ;; we prove that the frames of the scheduled travels
  ;; are equal to the frames of the conversion of the initial list of travels
  ;; filtered according to the ids of the scheduled travels
  (mv-let (newtrlst arrived newmeasure newntkstate)
          (scheduling trlst  nodeset  ntkstate order)
          (declare (ignore newtrlst newmeasure newntkstate))
          (implies (and (trlstp trlst nodeset)
                        (validparamsp params))
                   (equal  (v-frms arrived)
                           (tm-frms
                            (totmissives
                             (extract-sublst trlst (v-ids arrived)))))))
  :hints (("goal"
           :use ((:instance tm-frms-to-v-frms
                            (x (extract-sublst
                                trlst
                                (v-ids (mv-nth
                                        1 (scheduling trlst
                                                      nodeset ntkstate
                                                      order))))))
                 (:instance s/d-travel-v-frms
                            (sd-trlst  (mv-nth 1 (scheduling trlst
                                                             nodeset
                                                             ntkstate
                                                             order)))
                            (trlst/sd-ids (extract-sublst
                                           trlst
                                           (v-ids
                                            (mv-nth
                                             1
                                             (scheduling trlst

                                                         nodeset
                                                         ntkstate order))))))

                 (:instance arrived-travels-correctness))
           :in-theory (disable trlstp s/d-travel-v-frms mv-nth))))


(defthm arrived/rtg_not_modify_frames        ;; ok
  ;; we prove the the frames of the arrived travels produced
  ;; by scheduling and routing are equal to the frames
  ;; of the initial list of missives
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (newtrlst arrived newmeasure newntkstate)
            (scheduling (routing m nodeset)  nodeset ntkstate order)
            (declare (ignore newtrlst newmeasure newntkstate))
            (implies (and (tmissivesp m nodeset)
                          (validparamsp params))
                     (equal (v-frms arrived)
                            (tm-frms
                             (extract-sublst
                              m (v-ids arrived)))))))
  :hints (("goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize )
           :use ((:instance arrived-v-frms-m-frms
                            (trlst (routing m (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params)))
                 (:instance subsetp-arrived-newtrlst-ids
                            (trlst (routing m (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params))))
           :in-theory (disable trlstp tmissivesp
                               subsetp-arrived-newtrlst-ids
                               arrived-v-frms-m-frms))
          ("subgoal 1"
           :use ((:instance totmissives-extract-sublst
                            (l (routing m (nodesetgenerator params)))
                            (ids (v-ids
                                  (mv-nth
                                   1
                                   (scheduling
                                    (routing m (nodesetgenerator params))
                                     (nodesetgenerator params)
                                    ntkstate order))))
                            (nodeset (nodesetgenerator params))))
           :in-theory (disable trlstp tmissivesp
                               subsetp-arrived-newtrlst-ids
                               arrived-v-frms-m-frms ids-routing))))


(defthm correctroutesp-vm-frms-gc1         ;; ok
  ;; the correctness of routes and equality of frames imply
  ;; the main predicate (correctness of genoc_t-non-tail-comp)
  (implies (and (correctroutesp l (extract-sublst m (v-ids l))
                                nodeset)
                (equal (v-frms l)
                       (tm-frms (extract-sublst m (v-ids l)))))
           (genoc_t-correctness1 l
                                 (tomissives (extract-sublst m (v-ids l)))))

  :hints (("Goal" :in-theory (disable len nfix assoc-equal
                                      member-equal-tm-ids-assoc-equal
                                      member-equal-m-ids-assoc-equal
                                      true-listp-member-equal))))


(defthm gc1_arrived/rtg          ;; ok
  ;; we prove the correctness of the arrived travels
  (let ((nodeset (nodesetgenerator params)))
    (implies (and (tmissivesp m nodeset)
                  (validparamsp params))
             (mv-let (newtrlst arrived newmeasure newntkstate)
                     (scheduling (routing m nodeset)  nodeset
                                 ntkstate order)
                     (declare (ignore newtrlst newmeasure newntkstate))
                     (genoc_t-correctness1
                      arrived
                      (tomissives (extract-sublst m (v-ids arrived)))))))
  :otf-flg t
  :hints (("goal"
           :do-not-induct t
           :do-not '(eliminate-destructors generalize )
           :use
           ((:instance subsetp-arrived-newtrlst-ids
                       (trlst (routing m (nodesetgenerator params)))
                       (nodeset (nodesetgenerator params)))
            (:instance totmissives-extract-sublst
                       (l (routing m (nodesetgenerator params)))
                       (ids (v-ids
                             (mv-nth
                              1
                              (scheduling
                               (routing m (nodesetgenerator params))

                               (nodesetgenerator params)  ntkstate order))))
                       (nodeset (nodesetgenerator params)))
            (:instance scheduling-preserves-route-correctness
                       (nodeset (nodesetgenerator params))
                       (trlst (routing m (nodesetgenerator params))))
            (:instance correctroutesp-vm-frms-gc1
                       (nodeset (nodesetgenerator params))
                       (l (mv-nth
                           1
                           (scheduling
                            (routing m (nodesetgenerator params))
                             (nodesetgenerator params)  ntkstate order)))))
           :in-theory (disable trlstp tmissivesp
                               correctroutesp-vm-frms-gc1 len
                               subsetp-arrived-newtrlst-ids
                               scheduling-preserves-route-correctness
                               arrived/rtg_not_modify_frames))))

;;tomissives of scheduling + tomissives of ready 0 ----> tomissives m

(defthm lemma12
  (let ((nodeset (nodesetgenerator params))
        (mv0-sched (mv-nth
                    0
                    (scheduling
                     (routing (mv-nth 1 (readyfordeparture m nil nil
                                                           time))
                              (nodesetgenerator params))
                      (nodesetgenerator params)  ntkstate  order)))
      (mv3-sched (mv-nth
                  2
                  (scheduling
                   (routing (mv-nth 1 (readyfordeparture m nil nil
                                                         time))
                            (nodesetgenerator params))
                    (nodesetgenerator params)  ntkstate order)))
      (mv4-sched (mv-nth
                  3
                  (scheduling
                   (routing (mv-nth 1 (readyfordeparture m nil nil
                                                         time))
                            (nodesetgenerator params))
                    (nodesetgenerator params)  ntkstate order)))
      (mv0-r4d        (mv-nth 0 (readyfordeparture m nil nil time)))
      (order1 (get_next_priority order)))
    (implies (and (tmissivesp m nodeset)
                  (validparamsp params))
             (equal
              (extract-sublst (append
                               (extract-sublst (tomissives m)
                                               (tm-ids mv0-sched))
                               (extract-sublst (tomissives m)
                                               (tm-ids mv0-r4d)))
                              (v-ids
                               (genoc_t-non-tail-comp
                                (append mv0-sched mv0-r4d) nodeset
                                mv3-sched
                                (+ 1 time) mv4-sched order1)))
              (extract-sublst (tomissives m)
                              (v-ids (genoc_t-non-tail-comp
                                      (append mv0-sched mv0-r4d)
                                      nodeset mv3-sched  (+ 1 time)
                                      mv4-sched
                                      order1))))))

  :hints (("goal" :use
           ((:instance v-ids-genoc_t-non-tail-comp
                       (m (append (mv-nth
                                   0
                                   (scheduling
                                    (routing
                                     (mv-nth
                                      1
                                      (readyfordeparture m nil nil
                                                         time))
                                     (nodesetgenerator params))
                                     (nodesetgenerator params)
                                    ntkstate order))
                                  (mv-nth
                                   0
                                   (readyfordeparture m nil nil time))))
                       (measure (mv-nth
                             2
                             (scheduling
                              (routing (mv-nth
                                        1 (readyfordeparture m nil nil
                                                             time))
                                       (nodesetgenerator params))
                               (nodesetgenerator params)  ntkstate order)))
                       (time (+ 1 time))
                       (order (get_next_priority order))
                       (ntkstate
                        (mv-nth
                         3
                         (scheduling
                          (routing
                           (mv-nth 1 (readyfordeparture m nil nil
                                                        time))
                           (nodesetgenerator params))
                           (nodesetgenerator params)  ntkstate order))))
            (:instance equalid-tomissives
                       (nodeset (nodesetgenerator params)))
            (:instance tm-ids-append-invert
                       (nodeset (nodesetgenerator params))
                       (a (mv-nth
                           0
                           (scheduling
                            (routing (mv-nth
                                      1
                                      (readyfordeparture m nil nil
                                                         time))
                                     (nodesetgenerator params))
                             (nodesetgenerator params)  ntkstate order)))
                       (b (mv-nth 0 (readyfordeparture m nil nil time))))
            (:instance newtrlst-travel-correctness
                       (nodeset (nodesetgenerator params))
                       (trlst (routing
                               (mv-nth 1
                                       (readyfordeparture m nil nil
                                                          time))
                               (nodesetgenerator params))))
            (:instance subsetp-arrived-newtrlst-ids
                       (trlst (routing
                               (mv-nth 1 (readyfordeparture m nil nil
                                                            time))
                               (nodesetgenerator params)))
                       (nodeset (nodesetgenerator params)))
            (:instance extract-sublst-cancel-m
                       (m (tomissives m))
                       (id1 (tm-ids (append
                                     (mv-nth
                                      0
                                      (scheduling
                                       (routing
                                        (mv-nth
                                         1
                                         (readyfordeparture m nil nil
                                                            time))
                                        (nodesetgenerator params))
                                        (nodesetgenerator params)
                                       ntkstate order))
                                     (mv-nth
                                      0
                                      (readyfordeparture m nil nil time))) ))
                       (id2 (v-ids (genoc_t-non-tail-comp
                                    (append (mv-nth
                                             0
                                             (scheduling
                                              (routing
                                               (mv-nth
                                                1
                                                (readyfordeparture m
                                                                   nil
                                                                   nil
                                                                   time))
                                               (nodesetgenerator params))
                                               (nodesetgenerator
                                                   params)
                                              ntkstate order))
                                            (mv-nth
                                             0
                                             (readyfordeparture m nil
                                                                nil
                                                                time)))
                                    (nodesetgenerator params)
                                    (mv-nth 2
                                            (scheduling
                                             (routing
                                              (mv-nth
                                               1
                                               (readyfordeparture m
                                                                  nil
                                                                  nil
                                                                  time))
                                              (nodesetgenerator params))
                                              (nodesetgenerator
                                                  params)
                                             ntkstate order))
                                    (+ 1 time)
                                    (mv-nth
                                     3
                                     (scheduling
                                      (routing
                                       (mv-nth
                                        1
                                        (readyfordeparture m nil nil
                                                           time))
                                       (nodesetgenerator params))
                                       (nodesetgenerator params)
                                      ntkstate order))
                                    (get_next_priority order )))))
            (:instance tmissivesp-ready-4-departure-mv-0
                       (nodeset (nodesetgenerator params)))
            (:instance trlstp-routing
                       (m (mv-nth 1 (readyfordeparture m nil nil time))))
          (:instance tmissivesp-append-tmissivesp
                     (a (mv-nth 0
                                (scheduling
                                 (routing
                                  (mv-nth
                                   1 (readyfordeparture m nil nil time))
                                  (nodesetgenerator params))
                                  (nodesetgenerator params)  ntkstate
                                  order)))
                     (b (mv-nth 0 (readyfordeparture m nil nil time)))
                     (nodeset (nodesetgenerator params)))
          (:instance v-ids_g_nt_sigma_subsetp-v-ids-newtrlst/rtg
                     (m (append
                         (mv-nth
                          0
                          (scheduling
                           (routing
                            (mv-nth
                             1 (readyfordeparture m nil nil time))
                            (nodesetgenerator params))
                            (nodesetgenerator params)  ntkstate
                           order))
                         (mv-nth 0 (readyfordeparture m nil nil time))) ))
          (:instance tmissivesp-ready-4-departure-mv-1
                     (nodeset (nodesetgenerator params)))
          (:instance not-in-1-0-ready-for-dept-reverse
                     (nodeset (nodesetgenerator params)))
          (:instance not-in-1-0-ready-for-dept
                     (nodeset (nodesetgenerator params)))
          (:instance tmissivesp-newTrlst
                     (trlst (routing
                             (mv-nth 1
                                     (readyfordeparture m nil nil time))
                             (nodesetgenerator params)))
                     (nodeset (nodesetgenerator params)))))))


(defthm lemma12final
  (let ((nodeset (nodesetgenerator params))
        (mv0-sched
         (mv-nth
          0
          (scheduling
           (routing
            (mv-nth
             1 (readyfordeparture m nil nil time))
            (nodesetgenerator params))
            (nodesetgenerator params)  ntkstate order)))
        (mv3-sched
         (mv-nth
          2
          (scheduling
           (routing
            (mv-nth
             1 (readyfordeparture m nil nil time))
            (nodesetgenerator params))
            (nodesetgenerator params)  ntkstate order)))
        (mv4-sched
         (mv-nth
          3
          (scheduling
           (routing
            (mv-nth
             1 (readyfordeparture m nil nil time))
            (nodesetgenerator params))
            (nodesetgenerator params) ntkstate order)))
        (mv0-r4d (mv-nth 0 (readyfordeparture m nil nil time))))
    (implies (and (tmissivesp m nodeset)
                  (validparamsp params))
             (equal
              (extract-sublst
               (append (extract-sublst (tomissives m)
                                       (tm-ids mv0-sched))
                       (tomissives mv0-r4d))
               (v-ids
                (genoc_t-non-tail-comp
                 (append mv0-sched mv0-r4d) nodeset mv3-sched
                 (+ 1 time) mv4-sched (get_next_priority order))))
              (extract-sublst
               (tomissives m)
               (v-ids
                (genoc_t-non-tail-comp
                 (append mv0-sched mv0-r4d) nodeset mv3-sched (+ 1
                                                                 time)
                 mv4-sched (get_next_priority order)))))))
    :hints (("goal"
             :in-theory (e/d () (tmissivesp
                                 checkroutes-subsetp-validroute
                                 m-ids-append-invert
                                 nil-r4d-nil-mv0 nil-r4d-nil-mv1  zp
                                ; true-listp-genoc_t-non-tail-comp
                                 tomissives
                                 member-equal-tm-ids-assoc-equal
                                 member-equal-m-ids-assoc-equal tm-ids
                                 assoc-equal m-ids))
             :use ((:instance lemma12)
                   (:instance subset-ready-for-departure-4
                              (nodeset (nodesetgenerator params)))
                 (:instance tmissivesp-ready-4-departure-mv-0
                            (nodeset (nodesetgenerator params)))
                 (:instance tmissivesp-equal-subsetp
                            (nodeset (nodesetgenerator params))
                            (y  m)
                            (x  (mv-nth 0 (readyfordeparture m nil nil time))))
                 (:instance tmissives-subset-extract-tomissives-equal
                            (nodeset (nodesetgenerator params))
                            (x m)
                            (ids (tm-ids
                                  (mv-nth
                                   0
                                   (readyfordeparture m nil nil time)))))
                 (:instance subset-ready-for-departure
                            (nodeset (nodesetgenerator params)))
                 (:instance subset-ready-for-departure-4
                            (nodeset (nodesetgenerator params)))
                 (:instance tmissivesp-ready-4-departure-mv-0
                            (nodeset (nodesetgenerator params)))))))

(defthm takingtomissivesout-equal
  (let ((nodeset (nodesetgenerator params))
        (mv1-sched (mv-nth
                    1
                    (scheduling
                     (routing
                      (mv-nth 1 (readyfordeparture m nil nil time))
                      (nodesetgenerator params))
                      (nodesetgenerator params)  ntkstate order))))
    (implies (and (tmissivesp M nodeset)
                  (validparamsp params))
             (equal
              (tomissives
               (extract-sublst (mv-nth 1 (readyfordeparture m nil nil time))
                               (v-ids mv1-sched)))
              (extract-sublst  (tomissives
                                (mv-nth 1 (readyfordeparture m nil nil time)))
                               (v-ids mv1-sched)))))

  :hints (("goal"
           :use ((:instance tmissivesp-equal-subsetp
                            (x (mv-nth 1 (readyfordeparture m nil nil time)))
                            (nodeset (nodesetgenerator params))
                            (y m))
                 (:instance ToMissives-extract-sublst
                            (L (extract-sublst
                                m
                                (tm-ids (mv-nth
                                         1
                                         (readyfordeparture m nil nil time)))))
                            (ids (v-ids
                                  (mv-nth
                                   1
                                   (scheduling
                                    (routing
                                     (mv-nth
                                      1 (readyfordeparture m nil nil time))
                                     (nodesetgenerator params))
                                     (nodesetgenerator params)
                                    ntkstate order))))
                            (nodeset (nodesetgenerator params)))
                 (:instance subsetp-arrived-newtrlst-ids
                            (trlst (routing
                                    (mv-nth
                                     1
                                     (readyfordeparture m nil nil
                                                        time))
                                    (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params)))))))



(defthm lemma121final
  (let ((nodeset (nodesetgenerator params))
        (mv1-sched (mv-nth
                    1
                    (scheduling
                     (routing
                      (mv-nth
                       1 (readyfordeparture m nil nil time))
                      (nodesetgenerator params))
                      (nodesetgenerator params)  ntkstate order))))
    (implies (and (tmissivesp M nodeset)
                  (validparamsp params))
             (equal
              (extract-sublst
               (tomissives (mv-nth 1 (readyfordeparture m nil nil time)))
               (v-ids mv1-sched))
              (tomissives (extract-sublst M (v-ids mv1-sched))))))
  :hints (("Goal"
           :in-theory (disable tmissivesp len)
           :do-not-induct t
           :use ((:instance extract-sublst-cancel-TM
                            (id1 (TM-ids
                                  (mv-nth
                                   1 (readyfordeparture m nil nil time))))
                            (id2 (v-ids
                                  (mv-nth
                                   1
                                   (scheduling
                                    (routing
                                     (mv-nth
                                      1
                                      (readyfordeparture m nil nil time))
                                     (nodesetgenerator params))
                                     (nodesetgenerator params)
                                     ntkstate order)))))
                 (:instance tmissivesp-ready-4-departure-mv-1
                            (nodeset (nodesetgenerator params)))
                 (:instance ToMissives-extract-sublst
                            (L (extract-sublst
                                m
                                (tm-ids
                                 (mv-nth 1
                                         (readyfordeparture m nil nil time)))))
                            (ids (v-ids
                                  (mv-nth
                                   1
                                   (scheduling
                                    (routing
                                     (mv-nth
                                      1 (readyfordeparture m nil nil time))
                                     (nodesetgenerator params))
                                     (nodesetgenerator params)
                                    ntkstate order))))
                            (nodeset (nodesetgenerator params)))
                 (:instance ids-routing
                            (M (mv-nth 1 (readyfordeparture m nil nil time))))
                 (:instance tmissivesp-equal-subsetp
                            (x (mv-nth 1 (readyfordeparture m nil nil time)))
                            (nodeset (nodesetgenerator params))
                            (y m))
                 (:instance subsetp-arrived-newtrlst-ids
                            (trlst (routing
                                    (mv-nth
                                     1 (readyfordeparture m nil nil
                                                          time))
                                    (nodesetgenerator params)))
                            (nodeset (nodesetgenerator params)))))))


(defthm subset-arrived-tm-ids-M
  (implies (and (tmissivesp M (nodesetgenerator params))
                (validparamsp params))
           (subsetp (V-ids (mv-nth
                            1
                            (scheduling
                             (routing (mv-nth
                                       1
                                       (readyfordeparture m nil nil time))
                                      (nodesetgenerator params))
                              (nodesetgenerator params)  ntkstate order)))
                    (Tm-ids M)))
  :hints (("Goal"
           :in-theory (disable tmissivesp)
           :use
           ((:instance subset-ready-for-departure-2
                       (nodeset (nodesetgenerator params)))
            (:instance tmissivesp-ready-4-departure-mv-1
                       (nodeset (nodesetgenerator params)))
            (:instance ids-routing
                       (M (mv-nth 1 (readyfordeparture m nil nil time))))
            (:instance subsetp-arrived-newtrlst-ids
                       (trlst (routing
                               (mv-nth
                                1
                                (readyfordeparture m nil nil time))
                               (nodesetgenerator params)))
                       (nodeset (nodesetgenerator params)))))))


(defthm lasttheorem-lemma1211
  (let ((nodeset (nodesetgenerator params))
        (mv1-sched
         (mv-nth
          1
          (scheduling
           (routing (mv-nth 1 (readyfordeparture m nil nil time))
                    (nodesetgenerator params))
            (nodesetgenerator params)  ntkstate order))))
    (implies (and (tmissivesp M nodeset)
                  (validparamsp params))
             (equal (extract-sublst (tomissives m)
                                    (v-ids mv1-sched))
                    (tomissives (extract-sublst
                                 (mv-nth 1 (readyfordeparture m nil nil time))
                                 (v-ids mv1-sched))))))
  :hints (("Goal"
           :in-theory (disable tmissivesp)
           :use ((:instance lemma121final)
                 (:instance takingtomissivesout-equal)))))
(defthm true-listp-r4d
  (implies (tmissivesp m nodeset)
           (true-listp (mv-nth 0 (readyfordeparture m nil nil time))))
  :hints (("Goal" :use (tmissivesp-ready-4-departure-mv-0)
                  :in-theory (disable tmissivesp-ready-4-departure-mv-0)))
  :rule-classes :type-prescription)

(defthm genoc_t-thm          ;; ok
  ;; now we can prove the correctness of genoc_t
  (let ((nodeset (nodesetgenerator params)))
    (implies (and (tmissivesp m nodeset) ;(goodorder order)
                  (validparamsp params))
             (mv-let (cplt abt)
                     (genoc_t m nodeset measure nil  accup time ntkstate order)
                     (declare (ignore abt))
                     (genoc_t-correctness cplt m))))
  :otf-flg t
  :hints (("goal"
           :induct (genoc_t-non-tail-comp m (nodesetgenerator params)
                                          measure time ntkstate order)
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable trlstp tmissivesp lemma121final)
           :do-not-induct t)
          ("subgoal *1/2"
           :in-theory (disable tmissivesp mv-nth
                               extract-sublst-cancel-m
                       lemma121final trlstp tmissivesp
                       lemma12)
           :use
           ((:instance gc1_arrived/rtg
                       (m (mv-nth 1 (readyfordeparture m nil nil time))))
            (:instance lasttheorem-lemma1211)
            (:instance v-ids-genoc_t-non-tail-comp
                       (m (append (mv-nth
                                   0
                                   (scheduling
                                    (routing
                                     (mv-nth
                                      1
                                      (readyfordeparture m nil nil
                                                         time))
                                     (nodesetgenerator params))
                                     (nodesetgenerator params)
                                    ntkstate order))
                                  (mv-nth
                                   0 (readyfordeparture m nil nil time))))
                       (measure (mv-nth
                             2
                             (scheduling
                              (routing
                               (mv-nth
                                1
                                (readyfordeparture m nil nil time))
                               (nodesetgenerator params))
                               (nodesetgenerator params)
                              ntkstate order)))
                       (time (+ 1 time))
                       (ntkstate (mv-nth
                                  3
                                  (scheduling
                                   (routing
                                    (mv-nth
                                     1
                                     (readyfordeparture m nil nil
                                                        time))
                                    (nodesetgenerator params))
                                    (nodesetgenerator params)
                                   ntkstate order)))
                       (order (get_next_priority order)))
            (:instance gc1_arrived/rtg
                       (m  (mv-nth 1 (readyfordeparture m nil nil time))))))
          ("subgoal *1/2.2"
           :use
           ((:instance v-ids-genoc_t-non-tail-comp
                       (m (append
                           (mv-nth
                            0
                            (scheduling
                             (routing
                              (mv-nth
                               1 (readyfordeparture m nil nil time))
                              (nodesetgenerator params))
                              (nodesetgenerator params)  ntkstate
                             order))
                           (mv-nth 0 (readyfordeparture m nil nil time))))
                       (measure (mv-nth
                             2
                             (scheduling
                              (routing
                               (mv-nth 1 (readyfordeparture m nil nil
                                                            time))
                               (nodesetgenerator params))
                               (nodesetgenerator params)  ntkstate
                              order)))
                       (time (+ 1 time))
                       (ntkstate (mv-nth
                                  3
                                  (scheduling
                                   (routing
                                    (mv-nth
                                     1 (readyfordeparture m nil nil
                                                          time))
                                    (nodesetgenerator params))
                                    (nodesetgenerator params)
                                   ntkstate order)))
                       (order (get_next_priority order)))))
          ("Subgoal *1/3.1"
           :in-theory (disable tmissivesp mv-nth
                               extract-sublst-cancel-m
                               lasttheorem-lemma1211 lemma12)
           :use
           ((:instance tmissivesp-ready-4-departure-mv-1
                       (nodeset (nodesetgenerator Params)))
            (:instance gc1_arrived/rtg
                       (M (mv-nth 1 (readyfordeparture m nil nil time))))))
          ("Subgoal *1/3.1'"
           :in-theory (disable tmissivesp mv-nth
                               extract-sublst-cancel-m
                               lemma121final lemma12))))#|ACL2s-ToDo-Line|#



;;------------------------------------------------------------
;;      definition and validation of genoc
;;------------------------------------------------------------

;; we load the generic definitions of the interfaces
(include-book "interfaces-computes")

;(include-book "GeNoC-interfaces")

;; ComputetTMissives
;; --------------
;(defun computeTMissives (transactions)
  ;; apply the function p2psend to build a list of tmissives
  ;; from a list of transactions
;(if (endp transactions)
;     nil
;    (let* ((trans (car transactions))
;          (id (idt trans))
;           (org (orgt trans))
;          (msg (msgt trans))
;           (dest (destt trans))
;           (flit (flitt trans))
;           (time (timet trans)))
;      (cons (list id org org (p2psend msg) dest flit time)
;            (computetmissives (cdr transactions))))))


;; ComputeResults
;; -------------
;(defun computeresults (trlst)
  ;; apply the function p2precv to build a list of results
  ;; from a list of travels
;  (if (endp trlst)
;      nil
;    (let* ((tr (car trlst))
;           (id (idv tr))
;           (r (car (routesv tr)))
;           (dest (car (last r)))
;           (frm (frmv tr))
;           (flit (flitv tr)))
;      (cons (list id dest (p2precv frm) flit)
;            (computeresults (cdr trlst))))))


;; genoc
;; -----

(defun genoc (trs params params2 order)
  ;; main function
  (if (ValidStateParamsp params params2)
    (mv-let (responses aborted simu)
            (genoc_t (computetmissives trs)
                     (NodesetGenerator params)
                     (initial-measure (routing (computetmissives trs) (NodesetGenerator params))
                                      (NodesetGenerator params)
                                      (generate-initial-ntkstate trs (stategenerator params params2))
                                      order)
                     nil
                     nil
                     '0
                     (generate-initial-ntkstate trs (stategenerator params params2))
                     order)
            (declare(ignore simu))
            (mv (computeresults responses) aborted))
    (mv nil nil)))

;; genoc correctness
;; -----------------
(defun genoc-correctness (results trs/ids)
  ;; trs/ids is the initial list of transactions filtered according
  ;; to the ids of the list of results.
  ;; we check that the messages and the destinations of these two lists
  ;; are equal.
  (and (equal (r-msgs results)
              (t-msgs trs/ids))
       (equal (r-dests results)
              (t-dests trs/ids))))

(defun all-frms-equal-to-p2psend (trlst trs)
  ;; check that every frame of trlst is equal to the application
  ;; of p2psend to the corresponding message in the list of
  ;; transactions trs
  (if (endp trlst)
      (if (endp trs)
          t
        nil)
    (let* ((tr (car trlst))
           (trans (car trs))
           (tr-frm (frmv tr))
           (t-msg (msgt trans)))
      (and (equal tr-frm (p2psend2 t-msg))
           (all-frms-equal-to-p2psend (cdr trlst) (cdr trs))))))

(defthm gc1-=>-all-frms-equal-to-p2psend      ;; ok
  (implies (genoc_t-correctness1 trlst (tomissives (computetmissives trs)))
           (all-frms-equal-to-p2psend trlst trs))
  :hints (("Goal"
           :in-theory (disable last true-listp leq-position-equal-len
                                nfix len))))

(defthm all-frms-equal-r-msgs-t-msgs
  ;; if frames have been computed by p2psend then
  ;; computeresults applies p2precv. we get thus the initial msg.
  (implies (and (all-frms-equal-to-p2psend trlst trs)
                (validfields-trlst trlst nodeset))
           (equal (r-msgs (computeresults trlst))
                  (t-msgs trs)))
  :hints (("Goal"
           :in-theory (disable last true-listp leq-position-equal-len
                               nfix len))))

(defthm gc1-r-dest-tm-dests       ;; ok
  (implies (and (genoc_t-correctness1 trlst m/trlst)
                (validfields-trlst trlst nodeset)
                (missivesp m/trlst nodeset))
           (equal (r-dests (computeresults trlst))
                  (m-dests m/trlst))))


(in-theory (disable mv-nth))

(defthm validfields-trlst-genoc_nt       ;; ok
  ;; to use the lemma all-frms-equal-to-p2psend we need to establish
  ;; that genoc_nt contains travels with validfields
  ;; and that it contains no duplicated ids
  (let ((nodeset (nodesetgenerator params)))
    (implies (and (tmissivesp m nodeset)
                  (validparamsp params))
             (validfields-trlst
              (genoc_t-non-tail-comp m nodeset measure time ntkstate
                                     order)
              nodeset)))
  :otf-flg t
  :hints (("goal"
           :do-not-induct t
           :induct (genoc_t-non-tail-comp m (nodesetgenerator params)
                                          measure  time ntkstate order))
          ("subgoal *1/3"
           :use
           ((:instance tmissivesp-newTrlst
                       (trlst (routing
                               (mv-nth 1 (readyfordeparture m nil nil time))
                               (nodesetgenerator params)))
                       (nodeset (nodesetgenerator params)))
            (:instance trlstp-arrived
                       (trlst (routing
                               (mv-nth 1 (readyfordeparture m nil nil time))
                               (nodesetgenerator params)))
                       (nodeset (nodesetgenerator params)))
            (:instance tmissivesp-mv-nth-0-scheduling
                       (trlst (routing
                               (mv-nth 1 (readyfordeparture m nil nil time))
                               (nodesetgenerator params)))))
           :in-theory (disable tmissivesp-newTrlst trlstp-arrived
                               tmissivesp-mv-nth-0-scheduling))))


(defthm tm-orgs-computetmissives      ;; ok
  (equal (tm-orgs (computetmissives trs))
         (t-orgs trs)))

(defthm tm-dests-computetmissives      ;; ok
  (equal (tm-dests (computetmissives trs))
         (t-dests trs)))



(defthm tm-ids-computestmissives       ;; ok
  ;; lemma for the next defthm
  (equal (tm-ids (computetmissives trs))
         (t-ids trs)))


(defthm tmissivesp-computetmissives     ;; ok
  (implies (transactionsp trs nodeset)
           (tmissivesp (computetmissives trs) nodeset)))



(defthm Extract-computemissives-tmissivesp-instance
  (implies (and (transactionsp trs (nodesetgenerator params))
                (validparamsp params))
           (tmissivesp
            (extract-sublst (computetmissives trs)
                            (v-ids
                             (genoc_t-non-tail-comp (computetmissives trs)
                                                    (nodesetgenerator params)
                                                    measure time ntkstate order)))
            (nodesetgenerator params)))
  :hints (("Goal"
           :use
           ((:instance v-ids-genoc_t-non-tail-comp
                       (m (computetmissives trs)))
            (:instance tmissivesp-computetmissives
                       (nodeset (nodesetgenerator params)))
            (:instance subset-arrived-tm-ids-M
                       (M (computetmissives trs)))
            (:instance v-ids-genoc_t-non-tail-comp-no-dup
                       (M (computetmissives trs)))))))


(defthm computetmissives-assoc-equal       ;; ok
  ;; if (assoc-equal e l) is not nil then we can link
  ;; assoc-equal and computetmissives as follows:
  ;; (this lemma is needed to prove the next defthm)
  (implies (assoc-equal e l)
           (equal (computetmissives (list (assoc-equal e l)))
                  (list (assoc-equal e (computetmissives l))))))


(defthm computetmissives-append       ;; ok
  (equal (computetmissives (append a b))
         (append (computetmissives a)
                 (computetmissives b))))


(defthm member-equal-assoc-equal-not-nil-t-ids
  ;; if e is an id of a travel of l
  ;; then (assoc-equal e l) is not nil
  (implies (and (member-equal e (t-ids trs))
                (validfields-t trs))
           (assoc-equal e trs)))

(defthm computetmissives-extract-sublst      ;; ok
  ;; calls of computetmissives are moved into calls
  ;; of extract-sublst
  (implies (and (subsetp ids (t-ids trs))
                (validfields-t trs))
           (equal (computetmissives (extract-sublst trs ids))
                  (extract-sublst (computetmissives trs) ids)))
  :otf-flg t
  :hints (("goal"
           :induct (extract-sublst trs ids)
           :do-not-induct t
           :in-theory (disable computetmissives append))))


(defthm computemissives-Extract-tmissivesp-instance
  (implies (and (transactionsp trs (nodesetgenerator params))
                (validparamsp params))
           (tmissivesp
            (computetmissives
             (extract-sublst trs
                             (v-ids
                              (genoc_t-non-tail-comp (computetmissives trs)
                                                     (nodesetgenerator params)
                                                     measure  time
                                                     ntkstate
                                                     order))))
            (nodesetgenerator params)))

  :hints (("Goal"
           :use
           ((:instance v-ids-genoc_t-non-tail-comp
                       (m (computetmissives trs)))
            (:instance Extract-computemissives-tmissivesp-instance)
            (:instance subset-arrived-tm-ids-M
                       (M (computetmissives trs)))
            (:instance v-ids-genoc_t-non-tail-comp-no-dup
                       (M (computetmissives trs)))
            (:instance computetmissives-extract-sublst
                       (ids (v-ids
                             (genoc_t-non-tail-comp (computetmissives trs)
                                                    (nodesetgenerator params)
                                                    measure  time ntkstate
                                                    order))))))))



(in-theory (disable fwd-chaining-transactionsp))

(defthm gc1-gnc-trs
  (implies (and (transactionsp trs (nodesetgenerator params))
                (validparamsp params))
           (genoc_t-correctness1
            (genoc_t-non-tail-comp
             (computetmissives trs)
             (nodesetgenerator params) measure  '0 ntkstate order)
            (tomissives (computetmissives
                         (extract-sublst
                          trs
                          (v-ids
                           (genoc_t-non-tail-comp
                            (computetmissives trs) (nodesetgenerator params)
                            measure '0 ntkstate order)))))))
  :hints (("Goal" :use ((:instance v-ids-genoc_t-non-tail-comp
                                   (time '0)
                                   (m (computetmissives trs)))
                        (:instance tomissives-extract-sublst
                                   (l (computetmissives trs))
                                   (ids (v-ids
                                         (genoc_t-non-tail-comp
                                          (computetmissives trs)
                                          (nodesetgenerator params)
                                          measure
                                          '0 ntkstate order)))
                                   (nodeset (nodesetgenerator params)))
                        (:instance genoc_t-thm
                                   (time '0)
                                   (m (computetmissives trs)))))))


(defthm gc1-=>-all-frms-equal-to-p2psend-instance       ;; ok
  (implies (and (transactionsp trs (nodesetgenerator params))
                (validparamsp params))
           (all-frms-equal-to-p2psend
            (genoc_t-non-tail-comp (computetmissives trs)
                                   (nodesetgenerator params)
                                   measure '0 ntkstate order)
            (extract-sublst trs
                            (v-ids
                             (genoc_t-non-tail-comp
                              (computetmissives trs) (nodesetgenerator params)
                              measure  '0 ntkstate order))))))

(defthm gc1-gnc-trs-inv
  (implies (and (transactionsp Trs (nodesetgenerator params))
                (validparamsp params))
           (genoc_t-correctness1
            (genoc_t-non-tail-comp (computetmissives
                                    trs)(nodesetgenerator params) measure
                                    '0 ntkstate order)
            (tomissives
             (extract-sublst (computetmissives trs)
                             (v-ids
                              (genoc_t-non-tail-comp
                               (computetmissives trs)
                               (nodesetgenerator params)
                               measure  '0 ntkstate order))))))
  :hints (("Goal"
           :in-theory (disable transactionsp)
           :use
           ((:instance v-ids-genoc_t-non-tail-comp
                       (time '0)
                       (m (computetmissives trs)))
            (:instance subset-arrived-tm-ids-M
                       (time '0)
                       (M (computetmissives trs)))
            (:instance v-ids-genoc_t-non-tail-comp-no-dup
                       (time '0)
                       (M (computetmissives trs)))
            (:instance tmissivesp-computetmissives
                       (nodeset (nodesetgenerator params)))
            (:instance computetmissives-extract-sublst
                       (ids (v-ids (genoc_t-non-tail-comp
                                    (computetmissives trs)
                                    (nodesetgenerator params)
                                    measure  '0 ntkstate order))))
            (:instance gc1-gnc-trs)))))


(defthm all-frms-equal-r-msgs-t-msgs-instance
  ;; if frames have been computed by p2psend then
  ;; computeresults applies p2precv. we get thus the initial msg.
  (implies (and (transactionsp trs (nodesetgenerator params))
                (validparamsp params))
           (equal (r-msgs (computeresults
                           (genoc_t-non-tail-comp
                            (computetmissives trs)(nodesetgenerator
                                                   params)
                            measure  '0 ntkstate order)))
                  (t-msgs (extract-sublst
                           trs
                           (v-ids
                            (genoc_t-non-tail-comp
                             (computetmissives trs) (nodesetgenerator params)
                             measure  '0 ntkstate order))))))
  :hints (("Goal"
           :use
           ((:instance validfields-trlst-genoc_nt
                       (time '0)
                       (m (computetmissives trs)))
            (:instance all-frms-equal-r-msgs-t-msgs
                       (nodeset (nodesetgenerator params))
                       (trlst (genoc_t-non-tail-comp
                               (computetmissives trs)
                               (nodesetgenerator params) measure '0
                               ntkstate order))
                       (trs (extract-sublst
                             trs
                             (v-ids (genoc_t-non-tail-comp
                                     (computetmissives trs)
                                     (nodesetgenerator params)
                                     measure  '0 ntkstate order)))))))))

(defthm r-ids-computeresults
  (equal (r-ids (computeresults x))
         (v-ids x)))

(defthm all-frms-equal-r-msgs-t-msgs-instance-use
  ;; if frames have been computed by p2psend then
  ;; computeresults applies p2precv. we get thus the initial msg.
  (implies (and (transactionsp trs (nodesetgenerator params))
                (validparamsp params))
           (equal (r-msgs
                   (computeresults
                    (genoc_t-non-tail-comp (computetmissives trs)
                                           (nodesetgenerator params)
                                           measure '0 ntkstate order)))
                  (t-msgs (extract-sublst
                           trs
                           (r-ids(computeresults
                                  (genoc_t-non-tail-comp
                                   (computetmissives trs)
                                   (nodesetgenerator params)
                                   measure '0 ntkstate order))))))))


(defthm gc1-r-dest-tm-dests-inst      ;; ok
  (implies (and (and (transactionsp trs (nodesetgenerator params))
                     (validparamsp params)))
           (equal (r-dests
                   (computeresults
                    (genoc_t-non-tail-comp (computetmissives trs)
                                           (nodesetgenerator params)
                                           measure  '0 ntkstate order)))
                  (m-dests (tomissives
                            (extract-sublst (computetmissives trs)
                                            (v-ids
                                             (genoc_t-non-tail-comp
                                              (computetmissives trs)
                                              (nodesetgenerator params)
                                              measure  '0 ntkstate order)))))))
  :hints (("Goal"  :in-theory (disable len nfix nth)
           :use
           ((:instance gc1-gnc-trs)
            (:instance gc1-r-dest-tm-dests)
            (:instance validfields-trlst-genoc_nt
                       (time '0)
                       (m (computetmissives trs)))
            (:instance to-missives-missivesp
                       (m (extract-sublst
                           (computetmissives trs)
                           (v-ids
                            (genoc_t-non-tail-comp
                             (computetmissives trs)
                             (nodesetgenerator params)measure
                             '0 ntkstate order))))
                       (nodeset (nodesetgenerator params) ) )
            (:instance tmissivesp-computetmissives
                       (nodeset (nodesetgenerator params)))
            (:instance v-ids-genoc_t-non-tail-comp
                       (time '0)
                       (m (computetmissives trs)))
            (:instance subset-arrived-tm-ids-M
                       (time '0)
                       (M (computetmissives trs)))
            (:instance v-ids-genoc_t-non-tail-comp-no-dup
                       (time '0)
                       (M (computetmissives trs)))
            (:instance computetmissives-extract-sublst
                       (ids (v-ids
                             (genoc_t-non-tail-comp
                              (computetmissives trs)
                              (nodesetgenerator params)
                              measure  '0 ntkstate order))))
            (:instance tm-ids-computestmissives )
            (:instance gc1-r-dest-tm-dests
                       (nodeset (nodesetgenerator params))
                       (trlst (genoc_t-non-tail-comp
                               (computetmissives trs)
                               (nodesetgenerator params)
                               measure '0 ntkstate order))
                       (m/trlst (tomissives
                                 (extract-sublst
                                  (computetmissives trs)
                                  (v-ids (genoc_t-non-tail-comp
                                          (computetmissives trs)
                                          (nodesetgenerator params)
                                          measure '0 ntkstate order))))))))))

(defthm gc1-r-dest-tm-dests-inst-use      ;; ok
  (implies (and (and (transactionsp trs (nodesetgenerator params))
                     (validparamsp params)))
           (equal (r-dests
                   (computeresults
                    (genoc_t-non-tail-comp
                     (computetmissives trs)
                     (nodesetgenerator params) measure  '0 ntkstate order)))
                  (m-dests
                   (tomissives
                    (extract-sublst
                     (computetmissives trs)
                     (r-ids (computeresults
                             (genoc_t-non-tail-comp
                              (computetmissives trs)
                              (nodesetgenerator params)
                              measure  '0 ntkstate order)))))))))

(defthm m-dest-t-dests-extract-sublst      ;; ok
  (implies (and (subsetp ids (t-ids trs))
                (validfields-t trs))
           (equal (tm-dests (extract-sublst (computetmissives trs) ids))
                  (t-dests (extract-sublst trs ids))))
  :hints (("goal"
           :do-not-induct t
           :use (:instance tm-dests-computetmissives
                           (trs (extract-sublst trs ids)))
           :in-theory (disable tm-dests-computetmissives))))



(defthm tm-dests-compute-missives-extract-sublst-use
  (implies (and (subsetp ids (t-ids trs))
                (transactionsp trs nodeset))
           (equal (t-dests (extract-sublst trs ids))
                  (tm-dests  (extract-sublst  (computetmissives trs) ids))))
  :rule-classes nil)

(defthm  m-dests-tm-dests
  (equal (m-dests (tomissives x))
         (tm-dests x)))

(defthm m-dests-to-missives-compute-missives-extract-sublst-use
  (implies (and (subsetp ids (t-ids trs))
                (transactionsp trs nodeset))
           (equal (t-dests (extract-sublst trs ids))
                  (m-dests  (tomissives (extract-sublst
                                         (computetmissives trs)
                                         ids)))))
  :rule-classes nil)

(defthm m-dests-to-missives-compute-missives-extract-sublst-use-instance
  (implies (and (transactionsp trs (nodesetgenerator params))
                (validparamsp params))
           (equal (t-dests
                   (extract-sublst
                    trs
                    (r-ids
                     (computeresults
                      (genoc_t-non-tail-comp (computetmissives trs)
                                             (nodesetgenerator params)
                                             measure  '0 ntkstate order)))))
                  (m-dests
                   (tomissives (extract-sublst
                                (computetmissives trs)
                                (r-ids
                                 (computeresults
                                  (genoc_t-non-tail-comp
                                   (computetmissives trs)
                                   (nodesetgenerator params)
                                   measure  '0 ntkstate order))))))))
  :hints (("Goal"
           :use
           ((:instance m-dests-to-missives-compute-missives-extract-sublst-use
                       (nodeset (nodesetgenerator params))
                       (ids (r-ids
                             (computeresults
                              (genoc_t-non-tail-comp (computetmissives trs)
                                                     (nodesetgenerator params)
                                                     measure '0 ntkstate order)))))
            (:instance tmissivesp-computetmissives
                       (nodeset (nodesetgenerator params)))
            (:instance v-ids-genoc_t-non-tail-comp
                       (time '0)
                       (m (computetmissives trs)))))))

(defthm equality-to-test
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (results aborted)
            (genoc trs params params2 order)
            (declare (ignore aborted))
            (implies (and (transactionsp trs nodeset)
                          (validstateparamsp params params2))
                     (equal
                      (computeresults
                       (genoc_t-non-tail-comp (computetmissives trs)
                                              (nodesetgenerator
                                               params)
                                              (initial-measure (routing (computetmissives trs) (NodesetGenerator params))
                                                               (NodesetGenerator params)
                                                               (generate-initial-ntkstate trs (stategenerator params params2))
                                                               order)
                                              '0
                                              (generate-initial-ntkstate trs (stategenerator params params2))
                                              order))
                      results))))

  :hints (("Goal"
        :use
        (:instance
         m-dests-to-missives-compute-missives-extract-sublst-use-instance
         (ntkstate (stategenerator params params2))))))


(defthm genoc-is-correct            ;; ok
  (let ((nodeset (nodesetgenerator params)))
    (mv-let (results aborted)
            (genoc trs params params2 order)
            (declare (ignore aborted))
            (implies (and (transactionsp trs nodeset)
                          (validstateparamsp params params2))
                     (genoc-correctness
                      results
                      (extract-sublst trs (r-ids results))))))
  :otf-flg t
  :hints (("goal" :do-not-induct t
           :in-theory (disable equality-to-test len nfix  nth)
           :use
           ((:instance all-frms-equal-r-msgs-t-msgs-instance-use )
            (:instance  equality-to-test )
            (:instance
             m-dests-to-missives-compute-missives-extract-sublst-use-instance
             (ntkstate (generate-initial-ntkstate trs (stategenerator params params2)))
             (measure (initial-measure (routing (computetmissives trs) (NodesetGenerator params))
                                      (NodesetGenerator params)
                                      (generate-initial-ntkstate trs (stategenerator params params2))
                                      order)))))))