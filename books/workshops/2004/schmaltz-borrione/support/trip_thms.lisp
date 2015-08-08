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

;; File: trip_thms.lisp
;; Book containing the main definitions and theorems on the Trip function

(in-package "ACL2")

;; we import lemmas to help for the proofs
(include-book "local_trip_book")

;; in order to use the lemmas we disable the corresponding functions
(in-theory (disable first_travel_step nth_travel_step))


(defun do_travel1 (msg route N)
  ;; function that calls the trip step functions until the route contains only
  ;; one node number
  (if (< (len route) 2)
      msg
    (if (equal (len route) 2) ;; we are done and we do the last step,
                              ;; which is identical to the first step
        (first_travel_step msg route N)
      ;; either we do the nth step
      (let ((route_triple (firstn 3 route)))
        (do_travel1 (nth_travel_step msg route_triple N)
                    (cdr route)
                    N)))))

(local
 (defthm do_travel_1_equal_msg_len_route_<=_2
   (implies (and (no-duplicatesp route)
                 (all_pos_intp route)
                 (all_intp route)
                 (true-listp route)
                 (availableMovep route N)
                 (all_inf_np route (* 4 N))
                 (integerp N) (< 0 N)
                 (<= (len route) 2))
            (equal (do_travel1 msg route N)
                   msg)))
)

(local
 (defthm do_travel_1_equal_msg_=_3
   (implies (and (no-duplicatesp route)
                 (true-listp route)
                 (integerp N) (< 0 N)
                 (all_pos_intp route)
                 (all_intp route)
                 (availableMovep route N)
                 (all_inf_np route (* 4 N))
                 (equal (len route) 3))
            (equal (do_travel1 msg route N)
                   msg))
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;    :hints (("GOAL"
;             :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)))
   )
)

(defthm no-duplicatesp_firstn_member
  (implies (no-duplicatesp l)
           (not (member-equal (car l)
                              (firstn (+ -1 n) (cdr l))))))

(defthm no-duplicatesp_firstn
  (implies (no-duplicatesp l)
           (no-duplicatesp (firstn n L))))

(defthm all_intp_firstn
  (implies (all_intp L)
           (all_intp (firstn n L))))

(defthm availableMovep_firstn
  (implies (availableMovep route N)
           (availableMovep (firstn i route) N)))

(defthm all_pos_intp_firstn
  (implies (all_pos_intp L)
           (all_pos_intp (firstn n L))))

(defthm all_inf_np_firstn
  (implies (all_inf_np L Bound)
           (all_inf_np (firstn n L) Bound)))

(defthm available_cdr
  (implies (availableMovep L N)
           (availableMovep (cdr L) N))
  :rule-classes :forward-chaining)

(local
 (defthm do_travel1_equal_msg_>_3
   (implies (and (no-duplicatesp route)
                 (availableMovep route N)
                 (true-listp route)
                 (integerp N) (< 0 N)
                 (all_pos_intp route)
                 (all_intp route)
                 (all_inf_np route (* 4 N))
                 (< 3 (len route)))
            (equal (do_travel1 msg route N)
                   msg))
   :otf-flg t
   :hints (("GOAL"
            :induct (do_travel1 msg route N)
            :do-not-induct t
            :in-theory (disable
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (commented out two rules just below).]
                        ;; NO-DUPLICATESP->NO-DUPLICATESP-EQUAL
                        ;; MEMBER->MEMBER-EQUAL
                        availableMovep
                        firstn))))
)


(defthm do_travel_1_equal_msg
  ;; we prove that doing iterative steps does not modify the message
  ;; if the route is made of valid moves
  (implies (and (no-duplicatesp route)
                (all_pos_intp route)
                (all_intp route)
                (all_inf_np route (* 4 N))
                (availableMovep route N)
                (integerp N) (< 0 N)
                (true-listp route))
           (equal (do_travel1 msg route N)
                  msg))
  :hints (("GOAL"
           :cases ((equal (len route) 3)
                   (<= (len route) 2)
                   (< 3 (len route))))))

(local
 (defthm do_travel_1_not_equal_msg_len_route_<=_2
   (implies (and (no-duplicatesp route)
                 (all_pos_intp route)
                 (all_intp route)
                 (true-listp route)
                 (not (availableMovep route N))
                 (all_inf_np route (* 4 N))
                 (integerp N) (< 0 N)
                 (<= (len route) 2))
            (not (do_travel1 msg route N))))
)

(local
 (defthm nth_travel_nil
   (implies (and (no-duplicatesp route)
                 (integerp N) (< 0 N)
                 (all_intp route) (true-listp route)
                 (all_pos_intp route) (all_inf_np route (* 4 N))
                 (equal (len route) 3))
            (not (nth_travel_step nil route N)))
   :hints (("GOAL"
            :cases ((availableMovep route N)
                    (not (availableMovep route n))))))
)

(local
 (defthm first_travel_nil
   (implies (and (no-duplicatesp route)
                 (integerp N) (< 0 N)
                 (all_intp route) (true-listp route)
                 (all_pos_intp route) (all_inf_np route (* 4 N))
                 (equal (len route) 2))
            (not (first_travel_step nil route N)))
   :hints (("GOAL"
            :cases ((availableMovep route N)
                    (not (availableMovep route n))))))
)

(local
 (defthm do_travel1_nil
   (implies (and (no-duplicatesp route)
                 (true-listp route)
                 (integerp N) (< 0 N)
                 (all_pos_intp route)
                 (all_intp route)
                 (equal (len route) 3)
                 (not (availableMovep route N))
                 (all_inf_np route (* 4 N)))
            (not (do_travel1 nil route N))))
)

(local
 (defthm do_travel_1_not_equal_msg_=_3
   (implies (and (no-duplicatesp route)
                 (true-listp route)
                 (integerp N) (< 0 N)
                 (all_pos_intp route)
                 (all_intp route)
                 (not (availableMovep route N))
                 (all_inf_np route (* 4 N))
                 (equal (len route) 3))
            (not (do_travel1 msg route N)))
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;    :hints (("GOAL"
;             :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)))
   )
)

(local
 (defthm not_available_movep_firstn3
   (implies (and (availableMovep (cdr route) N)
                 (not (availableMovep route N)))
           (not (availableMovep (firstn 3 route) N))))
)

(local
 (defthm do_travel1_not_equal_msg_>_3
   (implies (and (no-duplicatesp route)
                 (not (availableMovep route N))
                 (true-listp route)
                 (integerp N) (< 0 N)
                 (all_pos_intp route)
                 (all_intp route)
                 (all_inf_np route (* 4 N))
                 (< 3 (len route)))
            (not (do_travel1 msg route N)))
   :otf-flg t
   :hints (("GOAL"
            :induct (do_travel1 msg route N)
            :do-not-induct t
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (commented out two rules just below).]
            :in-theory (disable
                        ;; NO-DUPLICATESP->NO-DUPLICATESP-EQUAL
                        ;; MEMBER->MEMBER-EQUAL
                        availableMovep
                        firstn))
           ("Subgoal *1/3"
            :cases ((availableMovep (cdr route) n)
                    (not (availableMovep (cdr route) n))))))
)


(defthm do_travel_1_not_equal_msg
  ;; we prove that we lose the message if there is at least one
  ;; invalid move in the route
  (implies (and (no-duplicatesp route)
                (all_pos_intp route)
                (all_intp route)
                (all_inf_np route (* 4 N))
                (not (availableMovep route N))
                (integerp N) (< 0 N)
                (true-listp route))
           (not (do_travel1 msg route N)))
  :hints (("GOAL"
           :cases ((equal (len route) 3)
                   (<= (len route) 2)
                   (< 3 (len route))))))


(defun do_travel (msg route N)
  ;; top function for doing the trip steps
  (if (<= 2 (len route))
      (do_travel1 (first_travel_step msg (firstn 2 route) N)
                  route
                  N)
    msg))

;;;;;;;;;;;;;;;; MAIN DEFINITION OF TRIP ;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun trip (tl N)
  ;; exectute the travel of every element of the travel list tl
  ;; Note: the route of the first element of tl is (cdr (car tl))
  ;;       the request is (caar tl)
  (if (endp tl)
      nil
    (acons (do_travel (caar tl)      ;; request
                      (cdr (car tl)) ;; route
                      N)
           (cdr (car tl))
           (trip (cdr tl) N))))

(defthm correctness_of_Trip
  ;; we prove that if the route contains only valid moves
  ;; then the message is not modified
  (implies (and (all_no_duplicatesp tl)
                (all_pos_intp_route_lstp tl)
                (all_int_routep tl)
                (all_inf_routep tl (* 4 N))
                (all_availableMovep_routep tl N)
                (all_true-listp tl)
                (integerp N) (< 0 N)
                (tlp tl))
           (equal (trip tl N)
                  tl))
  :hints (("GOAL"
           :expand ((all_no_duplicatesp tl)
                    (all_pos_intp_route_lstp tl)
                    (all_int_routep tl)
                    (all_inf_routep tl (* 4 N))
                    (all_true-listp tl)
                    (all_availableMovep_routep tl N))
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)
           )))


(defun all_not_available_routep (tl N)
  ;; predicate that recognizes a travel list in which every route is not
  ;; made of only valid moves
  (if (endp tl)
      t
    (let* ((req_route (car tl))
           (route (cdr req_route)))
    (and (not (availableMovep route N))
         (all_not_available_routep (cdr tl) N)))))

(defun all_nil_msg (tl)
  ;; recognizes a travel list in which every message is nil
  (if (endp tl)
      t
    (and (not (caar tl))
         (all_nil_msg (cdr tl)))))

(defthm correctness_of_Trip_not
  ;; if every route are not made of valid moves then we lose the message
  (implies (and (all_no_duplicatesp tl)
                (all_pos_intp_route_lstp tl)
                (all_int_routep tl)
                (all_inf_routep tl (* 4 N))
                (all_not_available_routep tl N)
                (all_true-listp tl)
                (integerp N) (< 0 N)
                (all_true-listp tl)
                (tlp tl))
           (all_nil_msg (trip tl N)))
  :hints (("GOAL"
           :expand ((all_no_duplicatesp tl)
                    (all_pos_intp_route_lstp tl)
                    (all_int_routep tl)
                    (all_inf_routep tl (* 4 N))
                    (all_true-listp tl)
                    (all_not_available_routep tl N))
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;            :in-theory (disable NO-DUPLICATESP->NO-DUPLICATESP-EQUAL)
           )))
