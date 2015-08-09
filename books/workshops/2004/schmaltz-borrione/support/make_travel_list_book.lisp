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

;; File: make_travel_list_book.lisp
;; Definition and validation of the function that associates a route to a request

(in-package "ACL2")


;; we import the constrained function "myroute"
(include-book "routing_main")

(defmacro dest_node_nb (addr ms)
  ;; this macro expands to the value of the destination node
  `(floor ,addr ,ms))

(defun compute_myroute (loc node_nb ms N)
  ;; computes the mymyroute from node_nb to the node possessing the data
  ;; at address loc
  ;; N represents the number of nodes in a quarter
  (myroute node_nb (dest_node_nb loc ms) N))


(defun make_travel_list (nw_op travels_list ms N)
  ;; then we compute the myroute for each message on the NoC and put all then a
  ;; "travel list"
  (if (endp nw_op)
      (rev travels_list)
    (let* ((msg (car nw_op))
           (node_i (car msg))
           (msg_i (cdr msg))
           (loc_i (nth 1 msg_i))
           (myroute_i (compute_myroute loc_i node_i ms N)))
      (make_travel_list (cdr nw_op)
                        (acons msg_i myroute_i travels_list)
                        ms N))))


(defun make_travel_list_non_tail (nw_op ms N)
  ;; we define a non tail recursive definition
  (if (endp nw_op)
      nil
    (let* ((msg (car nw_op))
           (node_i (car msg))
           (msg_i (cdr msg))
           (loc_i (nth 1 msg_i))
           (myroute_i (compute_myroute loc_i node_i ms N)))
      (acons msg_i myroute_i
             (make_travel_list_non_tail (cdr nw_op)
                                        ms N)))))

(defthm make_travel_=_non_tail
  ;; and we add a rewrite rule to use the non tail recursive function
  (equal (make_travel_list
          nw_op travels_list ms N)
         (append (rev travels_list)
                 (make_travel_list_non_tail
                  nw_op ms N))))

;; we disable the tail definition
(in-theory (disable make_travel_list))


(local
(include-book "../../../../arithmetic-3/bind-free/top"))

(set-non-linearp t)

(local
 (include-book "../../../../arithmetic-3/floor-mod/floor-mod"))

;; now we prove that the properties on a myroute are preserved during the
;; construction of the travel list

(defthm all_inf_make_travel
  (implies (and (integerp N) (< 0 N)
                (NODE_MEM_SIZEp ms)
                (all_node_nb_validp nw_op (* 4 N))
                ; every address is a non neg int
                (all_address_validp nw_op (* 4 N) ms)
                )
           (all_inf_routep (make_travel_list nw_op nil
                                             ms N)
                           (* 4 N)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :induct
           (make_travel_list_non_tail nw_op ms N)))
)


(defthm all_int_routep_make_travel
  (implies (and (integerp N) (< 0 N)
                (NODE_MEM_SIZEp ms)
                (all_node_nb_validp nw_op (* 4 N))
                ; every address is a non neg int
                (all_address_validp nw_op (* 4 N) ms))
           (all_int_routep (make_travel_list nw_op nil
                                             ms N)))
  :hints (("GOAL"
           :do-not-induct t
           :induct
           (make_travel_list_non_tail nw_op ms N))))

(defthm all_pos_int_route_make_travel
  (implies (and (integerp N) (< 0 N)
                (NODE_MEM_SIZEp ms)
                (all_node_nb_validp nw_op (* 4 N))
                ; every address is a non neg int
                (all_address_validp nw_op (* 4 N) ms))
           (all_pos_intp_route_lstp
            (make_travel_list nw_op nil
                              ms N)))
  :hints (("GOAL"
           :do-not-induct t
           :induct
           (make_travel_list_non_tail nw_op ms N))))


(defthm all_valid_next_node_make_travel
  (implies (and (integerp N) (< 0 N)
                (NODE_MEM_SIZEp ms)
                (all_node_nb_validp nw_op (* 4 N))
                ; every address is a non neg int
                (all_address_validp nw_op (* 4 N) ms))
           (all_availableMovep_routep
            (make_travel_list nw_op nil
                              ms N)
            N))
  :hints (("GOAL"
           :do-not-induct t
           :induct
           (make_travel_list_non_tail nw_op ms N))))


(defthm all_no_duplicatesp_make_travel
  (implies (and (integerp N) (< 0 N)
                (NODE_MEM_SIZEp ms)
                (all_node_nb_validp nw_op (* 4 N))
                ; every address is a non neg int
                (all_address_validp nw_op (* 4 N) ms))
           (all_no_duplicatesp
            (make_travel_list nw_op nil
                              ms N)))
    :hints (("GOAL"
           :do-not-induct t
           :induct
           (make_travel_list_non_tail nw_op ms N))))

(defthm all_consp_route_make_travel
  (implies (and (integerp N) (< 0 N)
                (NODE_MEM_SIZEp ms)
                (all_node_nb_validp nw_op (* 4 N))
                ; every address is a non neg int
                (all_address_validp nw_op (* 4 N) ms))
           (all_consp_route
            (make_travel_list nw_op nil
                              ms N)))
    :hints (("GOAL"
           :do-not-induct t
           :induct
           (make_travel_list_non_tail nw_op ms N))))

(defthm all_true_listp_make_travel
  (implies (and (integerp N) (< 0 N)
                (NODE_MEM_SIZEp ms)
                (all_node_nb_validp nw_op (* 4 N))
                ; every address is a non neg int
                (all_address_validp nw_op (* 4 N) ms))
           (all_true-listp
            (make_travel_list nw_op nil
                              ms N)))
    :hints (("GOAL"
           :do-not-induct t
           :induct
           (make_travel_list_non_tail nw_op ms N))))

(set-non-linearp nil)

;; we need to prove that make_travel_list produces a tlp
(defthm tlp_make_travel_list1
  (tlp (make_travel_list nw_op nil ms N))
  :hints (("GOAL"
           :induct (make_travel_list_non_tail nw_op ms n)
           :do-not-induct t)))

(defthm all_r/w_1_collect_implies_all_r/w_1_make_travel
  ;; we prove that if every r/w signal in collect are 1, then
  ;; they are still 1 in the travel list, but their position has changed
  (implies  (all_r/w_1_collect nw_op)
            (all_r/w_1
             (make_travel_list nw_op nil ms N)))
)

(defthm all_r/w_0_collect_implies_all_r/w_0_make_travel
  ;; we prove that if every r/w signal in collect are 0, then
  ;; they are still 0 in the travel list, but their position has changed
  (implies (all_r/w_0_collect nw_op)
           (all_r/w_0
            (make_travel_list nw_op nil ms N))))


(defthm all_address_validp_implies_all_addrp
  ;; we prove that if every location is valid in a nw_op list
  ;; then every address in the travel list is also valid
  (implies (all_address_validp nw_op (* 4 N) ms)
           (all_addrp
            (make_travel_list nw_op nil ms N))))

(set-non-linearp t)

(defthm all_ok_nw_req_p_make_travel_lst
  (implies (and (integerp N) (< 0 N)
                (all_address_validp nw_op (* 4 n) ms)
                (NODE_MEM_SIZEp ms)
                (all_node_nb_validp nw_op (* 4 N)))
           (all_ok_nw_req_p
            (make_travel_list nw_op nil ms N)
            ms)))

(set-non-linearp nil)
