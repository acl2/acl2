;;-------------------------------------------------------------------------
;;-------------------------------------------------------------------------
;;
;;
;; Functional Specification and Validation of the Octagon Network on
;;              Chip using the ACL2 Theorem Prover
;;
;;
;;                          Proof Script
;;
;;
;;                         Julien Schmaltz
;;                     Joseph Fourier University
;;               46, av. Felix Viallet 38031 Grenoble Cedex
;;                             FRANCE
;;                      Julien.Schmaltz@imag.fr
;;
;;-------------------------------------------------------------------------
;;-------------------------------------------------------------------------

;; File: octagon_book.lisp
;; Final Book containing the validation of the Octagon.

(in-package "ACL2")

;; we import the definition of the function node which is imported by
;; this book
(include-book "collect_msg_book")

;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------
;;
;;                             OCTAGON
;;
;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------

(defun ComputeResponses (tl Glob_Mem ms cr_lst)
  ;; computes the responses of the requests of tl by calling function
  ;; node with the right inputs.
  ;; at the end cr_lst contains the responses and their route to go
  ;; back to the origin node
  ;; returns also the new memory
  (if (endp tl)
      (mv (rev cr_lst) Glob_Mem)
    (let* ((request (caar tl)) ;; tl = ( ( (r/w addr dat) k n1 .. f) ..)
           (route (cdar tl))
           ;; we extract every element of the request
           (nw_r/w (car request))
           (nw_addr (cadr request))
           (nw_dat (caddr request)))
      (mv-let (dnt1 dnt2 stat r_dat dnt3 Glob_Mem1)
              (node 'no_op ;; no local operations
                    0 0 ;; loc dat are not considered in the computation
                    Glob_Mem
                    0 0 ;; nw_stat nw_r_dat = incoming response, irrelevant here
                    nw_r/w nw_addr nw_dat ;; incoming request
                    0 1 ;; IncomingResponse = 0,  IncomingRequest = 1
                    (car (last route)) ;; node_nb = last step of the route
                    ms)
              (declare (ignore dnt1 dnt2 dnt3))
              (ComputeResponses
               (cdr tl)
               Glob_Mem1
               ms
               (acons ;; the response is inserted in tl
                     (list stat r_dat)
                     (rev route) ;; we reverse the route
                     cr_lst)))))
)

;; now we define non_tail recursive definitions for every output

(defun ComputeResponses_non_tail_cr_lst (tl Glob_Mem ms)
  ;; non_tail function that computes cr_lst
  (if (endp tl)
      nil
    (let* ((request (caar tl)) ;; tl = ( ( (r/w addr dat) k n1 .. f) ..)
           (route (cdar tl))
           ;; we extract every element of the request
           (nw_r/w (car request))
           (nw_addr (cadr request))
           (nw_dat (caddr request)))
      (mv-let (dnt1 dnt2 stat r_dat dnt3 Glob_Mem1)
              (node 'no_op ;; no local operations
                    0 0 ;; loc dat are not considered in the computation
                    Glob_Mem
                    0 0 ;; nw_stat nw_r_dat = incoming response, irrelevant here
                    nw_r/w nw_addr nw_dat ;; incoming request
                    0 1 ;; IncomingResponse = 0,  IncomingRequest = 1
                    (car (last route)) ;; node_nb = first step of the route
                    ms)
              (declare (ignore dnt1 dnt2 dnt3))
              (acons ;; the response is inserted in tl
                     (list stat r_dat)
                     (rev route) ;; we reverse the route
                     (ComputeResponses_non_tail_cr_lst
                      (cdr tl) Glob_Mem1 ms)))))


)

(defthm ComputeResponses_=_non_tail_cr_lst
  ;; we prove a rule that will rewrite the tail definition into the
  ;; non tail one
  (equal (car
          (ComputeResponses tl Glob_Mem ms cr_lst))
         (append (rev cr_lst)
                 (ComputeResponses_non_tail_cr_lst tl Glob_Mem ms))))

(defun ComputeResponses_glob_mem (tl Glob_Mem ms)
  ;; non_tail function that computes cr_lst
  (if (endp tl)
      Glob_Mem
    (let* ((request (caar tl)) ;; tl = ( ( (r/w addr dat) k n1 .. f) ..)
           (route (cdar tl))
           ;; we extract every element of the request
           (nw_r/w (car request))
           (nw_addr (cadr request))
           (nw_dat (caddr request)))
      (mv-let (dnt1 dnt2 stat r_dat dnt3 Glob_Mem1)
              (node 'no_op ;; no local operations
                    0 0 ;; loc dat are not considered in the computation
                    Glob_Mem
                    0 0 ;; nw_stat nw_r_dat = incoming response, irrelevant here
                    nw_r/w nw_addr nw_dat ;; incoming request
                    0 1 ;; IncomingResponse = 0,  IncomingRequest = 1
                    (car (last route)) ;; node_nb = first step of the route
                    ms)
              (declare (ignore dnt1 dnt2 dnt3 stat r_dat))
              (ComputeResponses_glob_mem (cdr tl) Glob_Mem1 ms))))
)

(defthm computeResponses_=_glob_mem
  ;; rule to rewrite the second output of function ComputeResponses
  (equal (mv-nth 1 (computeResponses tl Glob_mem ms cr_lst))
         (ComputeResponses_glob_Mem tl Glob_Mem ms)))

(in-theory (disable ComputeResponses))

(defthm consp_x_=>_consp_rev_x
  (implies (consp x)
           (consp (rev x)))
  :rule-classes :type-prescription)


(defthm all_intp_last
  (implies (and (all_intp l)
                (consp l))
           (integerp (car (last l))))
  :rule-classes :forward-chaining)

(defthm all_pos_intp_last
  (implies (all_pos_intp l)
           (<= 0 (car (last l))))
  :rule-classes :forward-chaining)


(defthm all_inf_routep_last
  (implies (and (all_inf_np l n)
                (consp l))
           (< (car (last l)) n))
  :rule-classes :forward-chaining)


(defthm mem_node_ok_non_loc_op
  ;; to prove the memory correct we prove the folllowing lemma on node:
  ;; if there is no incomingRequest and if the location of the order
  ;; is not owned by the local memory then the global memory is not changed
  (implies (and (equal IncomingRequest 0)
                (< loc (* ms node_nb))
                (<= ms loc))
           (equal (mv-nth 5
                          (node op loc dat Glob_Mem
                                nw_stat nw_r_dat nw_r/w nw_addr nw_dat
                                IncomingResponse IncomingRequest
                                node_nb ms))
                  Glob_Mem))
  :hints (("GOAL"
           :in-theory (enable node))))


(defthm all_ok_status_read_computeResponses
  ;; we prove that in case of good read requests the returned status is OK
  (implies (and (all_r/w_1 req_lst) ; read requests
                ;; every address of the request is own by the destination
                ;; node
                (all_ok_nw_req_p req_lst ms)
                (all_pos_intp_route_lstp req_lst)
                (all_int_routep req_lst)
                (all_consp_route req_lst)
                (all_inf_routep req_lst (floor (len Glob_Mem) ms))
                (all_addrp req_lst)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (all_ok_statusp
            (car
             (ComputeResponses req_lst Glob_Mem ms nil))))
  :otf-flg t
  :hints (("GOAL"
           :induct (ComputeResponses_non_tail_cr_lst
                    req_lst Glob_Mem ms)
           :do-not-induct t
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)
           ))
)


(defthm all_ok_status_write_computeResponses
  ;; we prove that in case of good write request the returned status is OK
  (implies (and (all_r/w_0 req_lst) ; write requests
                ;; every address of the request is own by the destination
                ;; node
                (all_ok_nw_req_p req_lst ms)
                (all_pos_intp_route_lstp req_lst)
                (all_int_routep req_lst)
                (all_consp_route req_lst)
                (all_inf_routep req_lst (floor (len Glob_Mem) ms))
                (all_addrp req_lst)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (all_ok_statusp
            (car
             (ComputeResponses req_lst Glob_Mem ms nil))))
  :otf-flg t
  :hints (("GOAL"
           :induct (ComputeResponses_non_tail_cr_lst
                    req_lst Glob_Mem ms)
           :do-not-induct t
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)
           ))
)



(defun all_read_dat_okp (req_lst res Glob_Mem ms)
  ;; predicate that defines the correctness of the returned data
  ;; in case of read requests
  (if (endp res)
      t
    (if (endp req_lst)
        nil
      (and (equal (nth 1 (caar res))
                  (nth (local_addr (nth 1 (caar req_lst)) ms)
                       (get_local_Mem Glob_Mem (last_route req_lst)
                                      ms)))
           (all_read_dat_okp (cdr req_lst) (cdr res)
                             Glob_Mem ms)))))


(defthm all_ok_data_read_ComputeResponses
  ;; in case of good read requests the returned data is equal to the
  ;; data in the initial memory
  (implies (and (all_r/w_1 req_lst) ; read requests
                ;; every address of the request is own by the destination
                ;; node
                (all_ok_nw_req_p req_lst ms)
                (all_pos_intp_route_lstp req_lst)
                (all_int_routep req_lst)
                (all_consp_route req_lst)
                (all_inf_routep req_lst (floor (len Glob_Mem) ms))
                (all_addrp req_lst)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (all_read_dat_okp req_lst
                             (car
                              (ComputeResponses req_lst Glob_Mem ms
                                                nil))
                             Glob_Mem MS))
  :hints (("GOAL"
           :induct (ComputeResponses_non_tail_cr_lst
                    req_lst Glob_Mem ms)
           :do-not-induct t
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)
           ))
)

(defthm all_ok_dat_write_ComputeResponses
  ;; in case of good write requests the returned data is correct
  (implies (and (all_r/w_0 req_lst) ; write requests
                ;; every address of the request is own by the destination
                ;; node
                (all_ok_nw_req_p req_lst ms)
                (all_pos_intp_route_lstp req_lst)
                (all_int_routep req_lst)
                (all_consp_route req_lst)
                (all_inf_routep req_lst (floor (len Glob_Mem) ms))
                (all_addrp req_lst)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (all_ok_dat_writep req_lst
                              (car
                               (ComputeResponses req_lst Glob_Mem
                                                 ms nil))))
  :hints (("GOAL"
           :induct (ComputeResponses_non_tail_cr_lst
                    req_lst Glob_Mem ms)
           :do-not-induct t
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)
           )))


(defthm mem_ok_read_ComputeResponses
  ;; in case of good read requests the global (hence the local) memory
  ;; is unchanged
  (implies (and (all_r/w_1 req_lst) ; read requests
                ;; every address of the request is own by the destination
                ;; node
                (all_ok_nw_req_p req_lst ms)
                (all_pos_intp_route_lstp req_lst)
                (all_int_routep req_lst)
                (all_consp_route req_lst)
                (all_inf_routep req_lst (floor (len Glob_Mem) ms))
                (all_addrp req_lst)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (equal (mv-nth 1 (ComputeResponses req_lst Glob_Mem ms nil))
                  Glob_Mem))
)

(defun all_ok_mem_writep (req_lst mem ms)
  ;; in case of good write requests, the location is changed as a call
  ;; to put-nth
  (if (endp req_lst)
      mem
     (all_ok_mem_writep (cdr req_lst)
                        (put-nth (global_addr (nth 1 (caar req_lst))
                                              (last_route req_lst)
                                              ms)
                                 (nth 2 (caar req_lst))
                                 mem)
                        ms)))

(defthm mem_ok_write_ComputeResponses
  ;; in case of good read requests the global (hence the local) memory
  ;; is unchanged
  (implies (and (all_r/w_0 req_lst) ; write requests
                ;; every address of the request is own by the destination
                ;; node
                (all_ok_nw_req_p req_lst ms)
                (all_pos_intp_route_lstp req_lst)
                (all_int_routep req_lst)
                (all_consp_route req_lst)
                (all_inf_routep req_lst (floor (len Glob_Mem) ms))
                (all_addrp req_lst)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (equal (mv-nth 1 (ComputeResponses req_lst Glob_Mem ms nil))
                  (all_ok_mem_writep req_lst Glob_Mem ms)))
)


;; Now, we consider function ComputeResponses correct


;; But we prove lemmas to show that hypotheses of previous theorems
;; are preserved by computeRes. This in order to be able to use the
;; correctness of Octagon

(defthm not_member_equal_rev
  (implies (not (member-equal x L))
           (not (member-equal x (rev L)))))

(defthm no-duplicatesp-rev
  (implies (no-duplicatesp x)
           (no-duplicatesp (rev x)))
  :hints (("Subgoal *1/4"
           :use (:instance not_member_equal_rev
                           (x (car x))
                           (L (cdr x)))
           :in-theory (disable not_member_equal_rev)))
)

(defthm all_no_duplicatesp_computeResponses
  (implies (all_no_duplicatesp tl)
           (all_no_duplicatesp
            (car (computeResponses tl Glob_Mem ms nil))))
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;   :hints (("GOAL"
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL
;                                MEMBER->MEMBER-EQUAL)))
  )

(defthm all_pos_intp_rev
  (implies (all_pos_intp x)
           (all_pos_intp (rev x))))

(defthm all_pos_intp_computeResponses
  (implies (all_pos_intp_route_lstp tl)
           (all_pos_intp_route_lstp
            (car (computeResponses tl Glob_Mem ms nil)))))

(defthm all_true-listp_computeResponses
  (implies (all_true-listp tl)
           (all_true-listp
            (car (computeResponses tl Glob_Mem ms nil)))))

(defthm tlp_computeResponses
  (implies (tlp tl)
           (tlp (car (computeResponses tl Glob_Mem ms nil)))))

(defthm all_int_rev
  (implies (all_intp l)
           (all_intp (rev l))))

(defthm all_int_routep_computeResponse
  (implies (all_int_routep tl)
           (all_int_routep (car
                            (computeResponses tl Glob_mem ms nil)))))

(defthm all_inf_np_rev
  (implies (all_inf_np l N)
           (all_inf_np (rev l) N)))

(defthm all_inf_routep_computeResponses
  (implies (all_inf_routep tl N)
           (all_inf_routep (car
                            (computeResponses tl Glob_mem ms nil))
                            N)))


(local
 (defthm availableMovep_append
   (implies (and (availableMovep l N)
                 (equal (car (last L))
                        (+ X (* -2 N)))
                 (integerp X))
            (availableMovep (append L (list x)) N)))
)

(local
 (defthm car_l_last_rev_l
   (equal (car (last (rev l)))
          (car l)))
)

(local
 (defthm availableMovep_append_2
   (implies (and (availableMovep l N)
                 (equal (car (last l))
                        (+ X (* 2 N)))
                 (integerp X))
            (availableMovep (append L (list x)) N)))
)

(local
 (defthm availableMovep_append_3
   (implies (and (availableMovep l N)
                 (equal (car (last l))
                        (+ 1 X))
                 (integerp X))
            (availableMovep (append L (list x)) N)))
)

(local
 (DEFTHM AVAILABLEMOVEP_APPEND_4
   (IMPLIES (AND (AVAILABLEMOVEP L N)
                 (EQUAL (CAR (LAST L)) (+ -1 X))
                 (INTEGERP X))
            (AVAILABLEMOVEP (APPEND L (LIST X)) N)))
)

(local
 (defthm availableMovep_append_5
   (implies (and (availableMovep l N)
                 (equal (car (last l)) 0)
                 (equal X (+ -1 (* 4 N))))
            (availableMovep (append L (list x)) N))
   :hints (("GOAL"
            :in-theory (disable prefer-positive-addends-<
                                prefer-positive-addends-equal))))
)

(local
 (defthm availableMovep_append_6
   (implies (and (availableMovep l N)
                 (equal (car (last l)) (+ -1 (* 4 N)))
                 (equal X 0))
            (availableMovep (append L (list x)) N))
   :hints (("GOAL"
            :in-theory (disable prefer-positive-addends-<
                                prefer-positive-addends-equal))))
)

(defthm available_rev
  (implies (and (availableMovep L N)
                (all_intp L))
           (availableMovep (rev L) N))
  :hints (("GOAL"
           :in-theory (disable prefer-positive-addends-<
                               prefer-positive-addends-equal
                               SIMPLIFY-SUMS-EQUAL))))

(defthm all_availablemovep_routep_computeResponses
  (implies (and (all_availablemovep_routep tl N)
                (all_int_routep tl))
           (all_availablemovep_routep
            (car
             (computeResponses tl Glob_mem ms nil))
            N)))


(defun ComputeRes (tl Glob_Mem ms res_lst)
  ;; computes the results of the responses in tl by calling function
  ;; node with the right inputs.
  ;; rs_lst contains the list of the result at the end of the computation
  ;; rs_lst = ( (i stat_i dat_i) .... )
  ;; this function also returns the new value of the memory
  (if (endp tl)
      (mv (rev res_lst) Glob_Mem)
    (let* ((response (caar tl))
           (route (cdar tl))
           (node_nb (car (last route))) ;; destination node
           (nw_stat (car response))
           (nw_r_dat (cadr response)))
      (mv-let (stat r_dat dnt1 dnt2 dnt3 Glob_Mem1)
              (node 'no_op 0 0 Glob_Mem
                    nw_stat nw_r_dat ;; incoming response
                    0 0 0
                    1 0 ;; IncomingResponse = 1, IncomingRequest = 0
                    node_nb ms)
              (declare (ignore dnt1 dnt2 dnt3))
              (ComputeRes (cdr tl) Glob_Mem1 ms
                          (acons ;; the key is the node number
                           node_nb
                     ;; the value is the result
                           (list stat r_dat)
                           res_lst)))))
)

(defun ComputeRes_non_tail_res_lst (tl Glob_Mem ms)
  ;; non-tail recursive definition of ComputeRes
  (if (endp tl)
      nil
    (let* ((response (caar tl))
           (route (cdar tl))
           (node_nb (car (last route)))
           (nw_stat (car response))
           (nw_r_dat (cadr response)))
      (mv-let (stat r_dat dnt1 dnt2 dnt3 Glob_Mem1)
              (node 'no_op 0 0 Glob_Mem
                    nw_stat nw_r_dat ;; incoming response
                    0 0 0
                    1 0 ;; IncomingResponse = 1, IncomingRequest = 0
                    node_nb ms)
              (declare (ignore dnt1 dnt2 dnt3))
              (acons ;; the key is the node number
                     node_nb
                     ;; the value is the result
                     (list stat r_dat)
                     (ComputeRes_non_tail_res_lst (cdr tl) Glob_Mem1 ms)))))
)

(defthm ComputeRes_=_non_tail_res_lst
  ;; rule to rewrite the tail recursive function to the non-tail one
  (equal (car
          (ComputeRes tl Glob_Mem ms res_lst))
         (append (rev res_lst)
                 (ComputeRes_non_tail_res_lst tl Glob_Mem ms))))

(defun ComputeRes_glob_mem (tl Glob_Mem ms)
  ;; function that computes the second output of ComputeRes
  (if (endp tl)
      Glob_Mem
    (let* ((response (caar tl))
           (route (cdar tl))
           (node_nb (car (last route)))
           (nw_stat (car response))
           (nw_r_dat (cadr response)))
      (mv-let (stat r_dat dnt1 dnt2 dnt3 Glob_Mem1)
              (node 'no_op 0 0 Glob_Mem
                    nw_stat nw_r_dat ;; incoming response
                    0 0 0
                    1 0 ;; IncomingResponse = 1, IncomingRequest = 0
                    node_nb ms)
              (declare (ignore dnt1 dnt2 dnt3 stat r_dat))
              (ComputeRes_glob_mem (cdr tl) Glob_Mem1 ms))))
)

(defthm ComputeRes_=_glob_mem
  ;; rule to rewrite the complex function to the simple one
  (equal (mv-nth 1 (ComputeRes tl Glob_Mem ms res_lst))
         (ComputeRes_glob_mem tl Glob_Mem ms)))

(in-theory (disable ComputeRes))


;; Verification of Function ComputeRes

(defthm ComputeRes_correctness_stat
  (all_stat_okp resp_lst
                (car
                 (ComputeRes resp_lst Glob_Mem ms nil)))
  :hints (("GOAL"
           :in-theory (enable node)))
)

(defthm all_ok_statusp_=>_all_ok_resultp
  (implies (all_ok_statusp resp_lst)
           (all_ok_resultp
            (car (computeRes resp_lst Glob_Mem ms nil))))
  :hints (("GOAL"
           :in-theory (enable node))))

(defthm ComputeRes_correctness_dat
  (all_dat_okp resp_lst
               (car
                (ComputeRes resp_lst Glob_Mem ms nil)))
  :hints (("GOAL"
           :in-theory (enable node)))
)

(defthm ComputeRes_correctness_mem
  ;; the memory is not changed by ComputeRes
  (equal (mv-nth 1
                 (ComputeRes resp_lst Glob_Mem ms nil))
         Glob_Mem)
  :hints (("GOAL"
           :in-theory (enable node)))
)

;; now, we consider function ComputeRes correct

(include-book "make_travel_list_book")

(include-book "scheduler_book")

(include-book "trip_thms")

(defun Octagon (op_lst N ms Glob_Mem)
  ;; model of the complete network, i.e. nodes connected to Octagon
  ;; runs the Network once and returns loc_done nw_done and the memory
  (mv-let (loc_done nw_op Glob_Mem1)
          ;; first we collect the messages and execute the local
          ;; operations
          ;; we also get the non local requests
          (collect_msg op_lst nil nil Glob_MEM ms)
          ;; then we compute the travel list
          (let* ((tl (make_travel_list nw_op nil ms N))
                 ;; we extract the set of non-overlapping communications
                 (novlp (scheduler tl nil nil))
                 ;; we move every request to their destination
                 (tl_at_dest (trip novlp N)))
            (mv-let (cr_lst Glob_Mem2)
                    ;; we compute the response of every request
                    (ComputeResponses tl_at_dest Glob_Mem1 ms nil)
                    ;; we move the responses back to their source node
                    (let ((tl_back (trip cr_lst N)))
                      ;; we compute the final result
                      (mv-let (nw_done Glob_Mem3)
                              (ComputeRes tl_back Glob_Mem2 ms nil)
                              (mv loc_done nw_done Glob_Mem3))))))
)


(in-theory (disable ;(:REWRITE COLLECT_=_NW_OP_NON_TAIL)
                    ;(:REWRITE COLLECT_MSG_=_COLLECT_MEM)
                    (:REWRITE COMPUTERESPONSES_=_GLOB_MEM)
                    (:REWRITE COMPUTERESPONSES_=_NON_TAIL_CR_LST)
                    (:REWRITE COMPUTERES_=_NON_TAIL_RES_LST)
                   ; (:REWRITE COMPUTERES_CORRECTNESS_MEM)
                    (:REWRITE MAKE_TRAVEL_=_NON_TAIL)
                    (:REWRITE SCHEDULER_TAIL_=_NON_TAIL)
                    (:REWRITE COMPUTERES_=_GLOB_MEM)))


(defthm all_ok_status_read_Octagon
  ;; in case of good read orders, all the results of the non-overlapping
  ;; communications are OK
  ;; we only consider non local communications
  (implies (and (all_read_op_lstp op_lst)
                (all_non_loc_op_lstp op_lst ms)
                (all_node_nb_validp op_lst (* 4 N))
                (all_address_validp op_lst (* 4 N) ms)
                (equal (len Glob_Mem) (* (* 4 N) ms))
                (integerp N) (< 0 N)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (all_ok_resultp
            (mv-nth 1 (Octagon op_lst N ms Glob_Mem))))
  :otf-flg t
  :hints (("GOAL"
           ;; we know the proof will use the previous theorems and will
           ;; not require any induction
           :do-not-induct t
           :use ((:instance all_ok_status_read_computeresponses
                            (req_lst
                              (scheduler
                               (MAKE_TRAVEL_LIST
                                (MV-NTH 1
                                        (COLLECT_MSG OP_LST NIL NIL
                                                     Glob_Mem ms))
                                NIL ms N)
                               NIL NIL))
                            (Glob_Mem
                             (MV-NTH 2
                                     (COLLECT_MSG OP_LST NIL NIL
                                                  Glob_Mem ms))))))))

(defthm all_ok_status_write_Octagon
  ;; in case of good read orders, all the results of the non-overlapping
  ;; communications are OK
  ;; we only consider non local communications
  (implies (and (all_write_op_lstp op_lst)
                (all_non_loc_op_lstp op_lst ms)
                (all_node_nb_validp op_lst (* 4 N))
                (all_address_validp op_lst (* 4 N) ms)
                (equal (len Glob_Mem) (* (* 4 N) ms))
                (integerp N) (< 0 N)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (all_ok_resultp
            (mv-nth 1 (Octagon op_lst N ms Glob_Mem))))
  :otf-flg t
  :hints (("GOAL"
           ;; we know the proof will use the previous theorems and will
           ;; not require any induction
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :use ((:instance all_ok_status_write_computeresponses
                            (req_lst
                              (scheduler
                               (MAKE_TRAVEL_LIST
                                (MV-NTH 1
                                        (COLLECT_MSG OP_LST NIL NIL
                                                     Glob_Mem ms))
                                N\IL ms N)
                               NIL NIL))
                            (Glob_Mem
                             (MV-NTH 2
                                     (COLLECT_MSG OP_LST NIL NIL
                                                  Glob_Mem ms))))))))

(defthm mem_ok_read_Octagon
  ;; we prove that in case of read transfers the memory is not
  ;; changed
  (implies (and (all_read_op_lstp op_lst)
                (all_non_loc_op_lstp op_lst ms)
                (all_node_nb_validp op_lst (* 4 N))
                (all_address_validp op_lst (* 4 N) ms)
                (equal (len Glob_Mem) (* (* 4 N) ms))
                (integerp N) (< 0 N)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (equal (mv-nth 2
                          (Octagon op_lst N ms Glob_Mem))
                  Glob_Mem))
  :otf-flg t
  :hints (("GOAL"
           ;; we know the proof will use the previous theorems and will
           ;; not require any induction
           :do-not-induct t
           :do-not '(eliminate-destructors generalize)
           :use (:instance
                 (:theorem
                  (implies (and (integerp a) (integerp b)
                                (< 0 a) (< 0 b)
                                (equal (len l) (* a b)))
                           (equal (floor (len l) a)
                                  b)))
                 (a ms) (b (* 4 N)) (l Glob_Mem)))))

(defun all_ok_dat_writep_Octagon (op_lst res_lst)
  ;; op_lst = ( (i op_i loc_i dat_i) ...)
  ;; res_lst = ( (i st dat) ... )
  (if (endp res_lst)
      t
    (if (endp op_lst)
        nil
      (let* ((order (cdar op_lst))
             (result (cdar res_lst))
             (dat_ord (nth 2 order))
             (dat_res (nth 1 result)))
        (and (equal dat_res dat_ord)
             (all_ok_dat_writep_Octagon (cdr op_lst) (cdr res_lst))))))
)


(defthm not_consp_op_lst_collect_msg
  (implies (not (consp op_lst))
           (not (consp
                 (mv-nth 1 (collect_msg op_lst nil nil Glob_Mem ms)))))
  :hints (("GOAL"
           :in-theory (enable collect_msg))))

(defthm not_consp_nw_op_make_travel_list
  (implies (not (consp nw_op))
           (not (consp
                 (make_travel_list nw_op nil ms N))))
  :hints (("GOAL"
           :in-theory (enable make_travel_list))))


(defthm not_consp_tl_not_consp_scheduler
  (implies (not (consp tl))
           (not (consp (scheduler tl nil nil))))
  :hints (("GOAL"
           :in-theory (enable scheduler))))

(defthm not_consp_car_computeresponses
  (implies (not (consp tl))
           (not (consp (car (computeResponses tl Glob_Mem ms nil)))))
  :hints (("GOAL"
           :in-theory (enable computeResponses))))

(defthm not_consp_car_computeres
  (implies (not (consp res_lst))
           (not (consp (car (computeRes res_lst glob_mem ms nil)))))
  :hints (("GOAL"
           :in-theory (enable computeRes))))

(set-non-linearp t)

(defthm all_ok_dat_write_Octagon
  (implies (and (all_write_op_lstp op_lst)
                (all_non_loc_op_lstp op_lst ms)
                (all_node_nb_validp op_lst (* 4 N))
                (all_address_validp op_lst (* 4 N) ms)
                (equal (len Glob_Mem) (* (* 4 N) ms))
                (integerp N) (< 0 N)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (all_dat_okp
            (car (computeresponses
                  (scheduler (make_travel_list
                              (mv-nth 1
                                      (collect_msg op_lst nil nil
                                                   Glob_Mem ms))
                              NIL ms N)
                             nil nil)
                  Glob_Mem ms nil))
            (mv-nth 1 (Octagon op_lst N MS Glob_Mem))))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use (;(:instance all_ok_dat_write_ComputeResponses
                 ;           (req_lst (scheduler
                 ;                     (make_travel_list
                 ;                      (mv-nth 1 (collect_msg op_lst nil nil
                 ;                                             Glob_Mem ms))
                 ;                      nil ms N)
                 ;                     nil nil)))
                 (:instance COMPUTERES_CORRECTNESS_DAT
                            (resp_lst
                             (CAR
                              (COMPUTERESPONSES
                               (SCHEDULER
                                (MAKE_TRAVEL_LIST (MV-NTH 1
                                                          (COLLECT_MSG OP_LST NIL NIL GLOB_MEM MS))
                                                  NIL MS N)
                                NIL NIL)
                               GLOB_MEM MS NIL)))
                            (Glob_Mem
                             (MV-NTH
                              1
                              (COMPUTERESPONSES
                               (SCHEDULER
                                (MAKE_TRAVEL_LIST (MV-NTH 1
                                                          (COLLECT_MSG OP_LST NIL NIL GLOB_MEM MS))
                                                  NIL MS N)
                                NIL NIL)
                               GLOB_MEM MS NIL)))))
           :in-theory (disable ;all_ok_dat_write_computeresponses
                               COMPUTERES_CORRECTNESS_DAT))))


(defthm all_ok_dat_read_Octagon
  (implies (and (all_read_op_lstp op_lst)
                (all_non_loc_op_lstp op_lst ms)
                (all_node_nb_validp op_lst (* 4 N))
                (all_address_validp op_lst (* 4 N) ms)
                (equal (len Glob_Mem) (* (* 4 N) ms))
                (integerp N) (< 0 N)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (all_dat_okp
            (car (computeresponses
                  (scheduler (make_travel_list
                              (mv-nth 1
                                      (collect_msg op_lst nil nil
                                                   Glob_Mem ms))
                              NIL ms N)
                             nil nil)
                  Glob_Mem ms nil))
            (mv-nth 1 (Octagon op_lst N MS Glob_Mem))))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :use ((:instance COMPUTERES_CORRECTNESS_DAT
                            (resp_lst
                             (CAR
                              (COMPUTERESPONSES
                               (SCHEDULER
                                (MAKE_TRAVEL_LIST (MV-NTH 1
                                                          (COLLECT_MSG OP_LST NIL NIL GLOB_MEM MS))
                                                  NIL MS N)
                                NIL NIL)
                               GLOB_MEM MS NIL)))
                            (Glob_Mem
                             (MV-NTH
                              1
                              (COMPUTERESPONSES
                               (SCHEDULER
                                (MAKE_TRAVEL_LIST (MV-NTH 1
                                                          (COLLECT_MSG OP_LST NIL NIL GLOB_MEM MS))
                                                  NIL MS N)
                                NIL NIL)
                               GLOB_MEM MS NIL)))))
           :in-theory (disable ;all_ok_dat_write_computeresponses
                               COMPUTERES_CORRECTNESS_DAT))))


(defthm all_write_mem_octagon
  (implies (and (all_write_op_lstp op_lst)
                (all_non_loc_op_lstp op_lst ms)
                (all_node_nb_validp op_lst (* 4 N))
                (all_address_validp op_lst (* 4 N) ms)
                (equal (len Glob_Mem) (* (* 4 N) ms))
                (integerp N) (< 0 N)
                (true-listp Glob_Mem)
                (NODE_MEM_SIZEp ms))
           (equal (mv-nth 2 (Octagon op_lst N MS Glob_Mem))
                  (all_ok_mem_writep
                   (scheduler
                    (make_travel_list
                     (mv-nth 1 (collect_msg op_lst nil nil
                                            Glob_Mem ms))
                     NIL ms N)
                    nil nil)
                   Glob_Mem ms)))
  :hints (("GOAL"
           :do-not-induct t
           :use ((:instance mem_ok_write_ComputeResponses
                            (req_lst
                             (scheduler
                              (make_travel_list
                               (mv-nth 1 (collect_msg op_lst nil nil
                                                      Glob_Mem ms))
                               NIL ms N)
                              nil nil))))
           :in-theory (disable mem_ok_write_ComputeResponses))))

(set-non-linearp nil)