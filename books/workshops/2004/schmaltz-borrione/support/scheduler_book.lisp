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

;; File: scheduler_book.lisp
;; Definition and validation of the function Scheduler

(in-package "ACL2")

(include-book "intersect")

(defun scheduler (tl non_ovlp_r prev)
  ;; extracts non overlapping communications of tl
  (if (endp tl)
      (rev non_ovlp_r)
    (let ((route_i (cdr (car tl))))
      (if (no_intersectp route_i prev)
          (scheduler (cdr tl)
                               (cons (car tl) non_ovlp_r)
                               (append route_i prev))
        (scheduler (cdr tl) non_ovlp_r prev)))))

(defun scheduler_non_tail (tl prev)
  (if (endp tl)
      nil
    (let ((route_i (cdr (car tl))))
      (if (no_intersectp route_i prev)
          (cons (car tl)
                (scheduler_non_tail (cdr tl)
                                              (append route_i prev)))
        (scheduler_non_tail (cdr tl) prev)))))

(defthm scheduler_tail_=_non_tail
  (equal (scheduler tl non_ovlp_r prev)
         (append
          (rev non_ovlp_r)
          (scheduler_non_tail tl prev))))

(in-theory (disable scheduler))

(defthm scheduler_and_prev_and_intersectp
  ;; if scheduler satisfies all_no_intersectp_routep then
  ;; the previous nodes have no intersection with grab_nodes
  ;; of scheduler
  (implies (all_no_intersectp_routep
            (scheduler tl nil prev))
           (no_intersectp prev
                          (grab_nodes
                           (scheduler tl nil prev)))))

(defthm all_no_intersectp_scheduler_non_tail
  ;; the following theorem proves that a route is unique but two routes may have
  ;; nodes in common
  (all_no_intersectp_routep (scheduler tl nil prev))
  :hints (("Subgoal *1/2"
           :use (:instance scheduler_and_prev_and_intersectp
                           (tl (cdr tl))
                           (prev (append (cdar tl) prev)))
           :in-theory (disable scheduler_and_prev_and_intersectp
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (commented out two rules just below).]
                               ;; NO-DUPLICATESP->NO-DUPLICATESP-EQUAL
                               ;; MEMBER->MEMBER-EQUAL
                               ))))

(defthm no_dupli_tl_=>_no_dupli_scheduler
  (implies (all_no_duplicatesp tl)
           (all_no_duplicatesp
            (scheduler tl nil prev))))

(defthm all_no_duplicatesp_scheduler
  ;; MAIN THEOREM ON SCHEDULER
  ;; if tl contains routes with no duplicate, then grab_nodes
  ;; of scheduler contains no duplicate
  (implies (all_no_duplicatesp tl)
           (no-duplicatesp (grab_nodes (scheduler tl nil prev))))
  :hints (("GOAL"
           :in-theory (disable
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (commented out rule just below).]
                       ;; NO-DUPLICATESP->NO-DUPLICATESP-EQUAL
                       scheduler_TAIL_=_NON_TAIL))))


(defthm all_no_duplicatesp_preserved_scheduler
  (implies (all_no_duplicatesp tl)
           (all_no_duplicatesp (scheduler tl nil prev))))

(defthm tlp_scheduler
  ;; we prove that scheduler perserves the tlp property
  (implies (tlp tl)
           (tlp (scheduler tl nil prev))))

(defthm all_r/w_1_scheduler
  ;; we prove that if every r/w signal is 1 in tl then it is still 1
  ;; after applying the scheduler function
  (implies (all_r/w_1 tl)
           (all_r/w_1 (scheduler tl nil prev))))

(defthm all_r/w_0_scheduler
  ;; we prove that if every r/w signal is 0 in tl then it is still 0
  ;; after applying the scheduler function
  (implies (all_r/w_0 tl)
           (all_r/w_0 (scheduler tl nil prev))))

(defthm all_addrp_scheduler
  ;; the scheduler preserves the validity of addresses
  (implies (all_addrp tl)
           (all_addrp
            (scheduler tl nil prev))))

(defthm all_pos_intp_route_lst
  (implies (all_pos_intp_route_lstp tl)
           (all_pos_intp_route_lstp
            (scheduler tl nil prev))))

(defthm all_true-listp_scheduler
  (implies (all_true-listp tl)
           (all_true-listp
            (scheduler tl nil prev))))

(defthm all_int_routep_scheduler
  (implies (all_int_routep tl)
           (all_int_routep
            (scheduler tl nil prev))))

(defthm all_consp_scheduler
  (implies (all_consp_route tl)
           (all_consp_route
            (scheduler tl nil prev))))
(defthm all_inf_routep_det_non_overlap_set
  (implies (all_inf_routep tl N)
           (all_inf_routep
            (scheduler tl nil prev) N)))

(defthm all_ok_nw_req_scheduler
  (implies (all_ok_nw_req_p tl ms)
           (all_ok_nw_req_p (scheduler tl nil prev) ms)))


(defthm all_availableMovep_scheduler
  (implies (all_availableMovep_routep tl N)
           (all_availableMovep_routep (scheduler tl nil prev) N))
)
