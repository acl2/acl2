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

;; File: collect_msg_book.lisp
;; Definition of the function collect_msg and some rules to work with

(in-package "ACL2")

;; we import some predicates and macros
(include-book "predicatesNCie")

;; we import the definition and theorems about the function Node
(include-book "node")

(defun collect_msg (op_lst loc_done nw_op Glob_Mem ms)
  ;; Collect_msg takes as input a list of operationa
  ;; op-lst contains all the operation that must be performed in every node
  ;; ( (0 op-0 loc-0 dat-0)
  ;;   (1 op-1 loc-1 dat-1)
  ;;   (3 op-3 loc-3 dat-3)
  ;;   ...)
  ;; loc-done will contain all the results of local communications
  ;; nw-op will contain all the messages that are sent on the NoC.
  ;; If there is an emitted message on the network then the msg output of
  ;; the node is not 'NO_MSG_R/W 'NO_MSG_ADDR 'NO_MSG_DATA
  (if (endp op_lst)
      (mv (rev loc_done) (rev nw_op) Glob_Mem)
    (let* ((msg (car op_lst))
           (node_i (car msg))
           (op_i (nth 1 msg))
           (loc_i (nth 2 msg))
           (dat_i (nth 3 msg)))
      (mv-let (st dat nw_r/w nw_addr nw_data node_Glob_Mem)
              (node op_i loc_i dat_i Glob_Mem
                    nil nil nil nil nil 0 0 ;; nothing comes from the nw
                    node_i ms) ;; i the current node number
              (if (equal nw_r/w 'NO_MSG_r/w) ;; no msg on the nw
          ;; we put the result in loc_done
                  (collect_msg (cdr op_lst)
                               (acons node_i
                                      (list st dat)
                                      loc_done)
                               nw_op node_Glob_Mem ms)
                ;; else we put the nw operation in nw_op
                (collect_msg (cdr op_lst) loc_done
                             (acons node_i (list nw_r/w nw_addr nw_data)
                                    nw_op)
                             node_Glob_Mem ms))))))

(defun loc_done (op_lst loc_done Glob_Mem ms)
  ;; this function computes the same result as the first output of the
  ;; above function, i.e. the list loc_done
  (if (endp op_lst)
      (rev loc_done)
    (let* ((msg (car op_lst))
           (node_i (car msg))
           (op_i (nth 1 msg))
           (loc_i (nth 2 msg))
           (dat_i (nth 3 msg)))
      (mv-let (st dat nw_r/w nw_addr nw_data node_Glob_Mem)
              (node op_i loc_i dat_i Glob_Mem
                    nil nil nil nil nil 0 0 ; nothing comes from the nw
                    node_i ms) ; i the current node number
              (declare (ignore nw_r/w nw_addr nw_data))
              (loc_done (cdr op_lst)
                        (acons node_i (list st dat) loc_done)
                        node_Glob_Mem ms)))))

(defun loc_done_non_tail (op_lst Glob_Mem ms)
  ;; to simplify the proof we define a non-tail recursive definition
  ;; of the tail recursive function
  (if (endp op_lst)
      nil
    (let* ((msg (car op_lst))
           (node_i (car msg))
           (op_i (nth 1 msg))
           (loc_i (nth 2 msg))
           (dat_i (nth 3 msg)))
      (mv-let (st dat nw_r/w nw_addr nw_data node_Glob_Mem)
              (node op_i loc_i dat_i Glob_Mem
                    nil nil nil nil nil 0 0 ; nothing comes from the nw
                    node_i ms) ; i the current node number
              (declare (ignore nw_r/w nw_addr nw_data))
              (acons node_i (list st dat)
                     (loc_done_non_tail (cdr op_lst)
                                        node_Glob_Mem ms))))))

(local
 (defthm loc_done_=_not_tail
   ;; we prove a rule to rewrite the tail definition to the tail definition
   (equal (loc_done op_lst loc_done Glob_Mem ms)
          (append (rev loc_done)
                  (loc_done_non_tail op_lst Glob_Mem ms))))
)

;; We prove that under some conditions the central if test of collect_msg is
;; always true and in each of these cases the first element of collect_msg
;; is equal to loc_done

;; now we prove that the if condition "governing" local transfers is
;; always true for local transfers

(local
 (defthm if_always_true_no_op
   ;; every operation is a no_op
   (implies (and (all_loc_op_lstp op_lst ms)
                 (consp op_lst)
                 (equal op (nth 1 (car op_lst)))
                 (equal loc (nth 2 (car op_lst)))
                 (equal dat (nth 3 (car op_lst)))
                 (all_no_op_lstp op_lst))
            (equal (mv-nth 2
                           (node op  ;; (nth 1 (car op_lst))
                                 loc ;; (nth 2 (car op_lst))
                                 dat ;; (nth 3 (car op_lst))
                                 Glob_Mem
                                 nil nil nil nil nil 0 0
                                 (caar op_lst) ms))
                   'NO_MSG_r/w))
   :hints (("GOAL"
            :in-theory (enable node))))
)

(local
 (defthm if_always_true_read
   ;; every operation is a read
   (implies (and (all_loc_op_lstp op_lst ms)
                 (consp op_lst)
                 (equal op (nth 1 (car op_lst)))
                 (equal loc (nth 2 (car op_lst)))
                 (equal dat (nth 3 (car op_lst)))
                 (all_read_op_lstp op_lst))
            (equal (mv-nth 2
                           (node op  ;; (nth 1 (car op_lst))
                                 loc ;; (nth 2 (car op_lst))
                                 dat ;; (nth 3 (car op_lst))
                                 Glob_Mem
                                 nil nil nil nil nil 0 0
                                 (caar op_lst) ms))
                   'NO_MSG_r/w))
   :hints (("GOAL"
            :in-theory (enable node))))
)

(local
 (defthm if_always_true_write
   ;; every operation is a write
   (implies (and (all_loc_op_lstp op_lst ms)
                 (consp op_lst)
                 (equal op (nth 1 (car op_lst)))
                 (equal loc (nth 2 (car op_lst)))
                 (equal dat (nth 3 (car op_lst)))
                 (all_write_op_lstp op_lst))
            (equal (mv-nth 2
                           (node op  ;; (nth 1 (car op_lst))
                                 loc ;; (nth 2 (car op_lst))
                                 dat ;; (nth 3 (car op_lst))
                                 Glob_Mem
                                 nil nil nil nil nil 0 0
                                 (caar op_lst) ms))
                   'NO_MSG_r/w))
   :hints (("GOAL"
            :in-theory (enable node))))
)

(local
 (defthm collect_=_loc_done
   (implies (and (all_loc_op_lstp op_lst ms)
                 (valid_op_lst op_lst))
            (equal (mv-nth 0
                           (collect_msg op_lst loc_done nw_op Glob_Mem ms))
                   (loc_done op_lst loc_done Glob_Mem ms))))
 )

(defun nw_op_non_tail (op_lst Glob_Mem ms)
  ;; computes the nw_op output of collect_msg but the definition if not
  ;; tail recursive
  (if (endp op_lst)
      nil
    (let* ((msg (car op_lst))
           (node_i (car msg))
           (op_i (nth 1 msg))
           (loc_i (nth 2 msg))
           (dat_i (nth 3 msg)))
      (mv-let (st dat nw_r/w nw_addr nw_dat node_Glob_Mem)
              (node op_i loc_i dat_i Glob_Mem
                    nil nil nil nil nil 0 0 ; nothing comes from the nw
                    node_i ms) ; i the current node number
              (declare (ignore st dat))
              (acons node_i (list nw_r/w nw_addr nw_dat)
                     (nw_op_non_tail (cdr op_lst) node_Glob_Mem ms))))))

;; now we prove that the condition governing local transfers is false

(local
 (defthm if_always_true_no_op_even_if_non_local
   ;; every operation is a no_op
   (implies (and (all_non_loc_op_lstp op_lst ms)
                 (all_no_op_lstp op_lst)
                 (equal op (nth 1 (car op_lst)))
                 (equal loc (nth 2 (car op_lst)))
                 (equal addr (nth 3 (car op_lst)))
                 (consp op_lst))
            (equal (mv-nth 2
                        (node op   ;; (nth 1 (car op_lst))
                              loc  ;; (nth 2 (car op_lst))
                              addr ;; (nth 3 (car op_lst))
                              Glob_Mem
                              nil nil nil nil nil 0 0
                              (caar op_lst) ms))
                   'NO_MSG_r/w))
   :hints (("GOAL"
            :in-theory (enable node))))
)

(local
 (defthm if_always_false_read
   ;; every operation is a read
   (implies (and (all_non_loc_op_lstp op_lst ms)
                 (all_read_op_lstp op_lst)
                 (equal op (nth 1 (car op_lst)))
                 (equal loc (nth 2 (car op_lst)))
                 (equal addr (nth 3 (car op_lst)))
                 (consp op_lst))
            (not (equal (mv-nth 2
                             (node op   ;; (nth 1 (car op_lst))
                                   loc  ;; (nth 2 (car op_lst))
                                   addr ;; (nth 3 (car op_lst))
                                   Glob_Mem
                                   nil nil nil nil nil 0 0
                                   (caar op_lst) ms))
                        'NO_MSG_r/w)))
   :hints (("GOAL"
            :in-theory (enable node))))
)

(local
 (defthm if_always_false_write
   ;; every operation is a write
   (implies (and (all_non_loc_op_lstp op_lst ms)
                 (all_write_op_lstp op_lst)
                 (equal op (nth 1 (car op_lst)))
                 (equal loc (nth 2 (car op_lst)))
                 (equal addr (nth 3 (car op_lst)))
                 (consp op_lst))
            (not (equal (mv-nth 2
                             (node op   ;; (nth 1 (car op_lst))
                                   loc  ;; (nth 2 (car op_lst))
                                   addr ;; (nth 3 (car op_lst))
                                   Glob_Mem
                                   nil nil nil nil nil 0 0
                                   (caar op_lst) ms))
                        'NO_MSG_r/w)))
   :hints (("GOAL"
            :in-theory (enable node))))
)

(local
 (defthm collect_=_nw_op_non_tail
   (implies (and (all_non_loc_op_lstp op_lst ms)
                 (all_read_or_write op_lst))
            (equal (mv-nth 1
                           (collect_msg op_lst loc_done nw_op Glob_Mem ms))
                   (append (rev nw_op)
                           (nw_op_non_tail op_lst Glob_Mem ms))))
   :hints (("Subgoal *1/2"
            :cases ((all_read_op_lstp op_lst)
                    (all_write_op_lstp op_lst)))))
)

(defun collect_mem (op_lst Glob_Mem ms)
  ;; we finally define a function for the last output of collect_msg:
  ;; the memory
  (if (endp op_lst)
      Glob_Mem
    (let* ((msg (car op_lst))
           (node_i (car msg))
           (op_i (nth 1 msg))
           (loc_i (nth 2 msg))
           (dat_i (nth 3 msg)))
      (mv-let (st dat nw_r/w nw_addr nw_data node_Glob_Mem)
              (node op_i loc_i dat_i Glob_Mem nil nil nil nil nil 0 0
                    node_i ms)
              (declare (ignore st dat nw_r/w nw_addr nw_data))
              (collect_mem (cdr op_lst) node_Glob_Mem ms)))))

(local
 (defthm collect_msg_=_collect_mem
   ;; we prove a rewrite rule to rewrite the last output of collect_msg
   ;; to the above function
   (equal (mv-nth 2
                  (collect_msg op_lst loc_done nw_op Glob_Mem ms))
          (collect_mem op_lst Glob_Mem ms))
   :hints (("GOAL"
            :in-theory (enable collect_msg))))
)

;; now all these functions will be reduced to their non tail form,
;; we disable them and will the use the rules.

(in-theory (disable collect_msg))

;; now we can prove lemmas that we want to import

(defthm memory_read_lemma
  (implies (equal op 'read)
           (equal (mv-nth 2 (memory op loc dat memo))
                  memo))
  :hints (("GOAL"
           :in-theory (enable memory))))

(defthm read_node_mem
  (implies (and (NODE_MEM_SIZEp ms)
                (integerp node_nb) (<= 0 node_nb)
                (true-listp Glob_Mem)
                (< node_nb (floor (len Glob_Mem) ms))
                (equal op 'read))
           (equal (mv-nth 5 (node op loc dat Glob_mem nw_stat nw_r_dat
                                  nw_r/w nw_addr nw_dat IncomingResponse
                                  IncomingRequest Node_nb ms))
                  Glob_Mem))
  :hints (("GOAL"
           :in-theory (enable node))))

(set-non-linearp t)

(defthm mv-nth-2-collect-read
  (implies (and (NODE_MEM_SIZEp ms)
                (all_node_nb_validp op_lst N)
                (integerp N) (< 0 N)
                (equal (len Glob_Mem) (* N ms))
                (true-listp Glob_Mem)
                (all_non_loc_op_lstp op_lst ms)
                (all_read_op_lstp op_lst))
           (equal (mv-nth 2 (collect_msg op_lst nil nil Glob_Mem ms))
                  Glob_Mem))
)

(defthm write_node_non_loc
  (implies (and (NODE_MEM_SIZEp ms)
                (integerp node_nb) (<= 0 node_nb)
                (true-listp Glob_Mem) (< node_nb (floor (len Glob_Mem) ms))
                (equal op 'write)
                (or (<= (+ MS (* MS node_nb)) loc)
                    (< loc (* ms node_nb))))
           (equal (mv-nth 5 (node op loc dat Glob_mem nw_stat nw_r_dat
                                  nw_r/w nw_addr nw_dat IncomingResponse
                                  IncomingRequest Node_nb ms))
                  Glob_Mem))
  :hints (("GOAL"
           :in-theory (enable node))))

(defthm mv-nth-2-collect-write
  (implies (and (NODE_MEM_SIZEp ms)
                (all_node_nb_validp op_lst N)
                (integerp N) (< 0 N)
                (equal (len Glob_Mem) (* N ms))
                (true-listp Glob_Mem)
                (all_non_loc_op_lstp op_lst ms)
                (all_write_op_lstp op_lst))
           (equal (mv-nth 2 (collect_msg op_lst nil nil Glob_Mem ms))
                  Glob_Mem))
)


(set-non-linearp nil)

(defthm all_read_implies_all_r/w_1
  ;; we prove that if every order of op_lst are READ then
  ;; every r/w signal in the nw_op list are 1
  (implies (and (all_non_loc_op_lstp op_lst ms)
                (all_read_op_lstp op_lst))
           (all_r/w_1_collect
            (mv-nth 1
                    (collect_msg op_lst nil nil Glob_Mem ms))))
  :hints (("GOAL"
           :in-theory (enable node)))
)

(defthm all_write_implies_all_r/w_0
  ;; we prove that if every order of op_lst are WRITE then
  ;; every r/w signal in the nw_op list are 0
  (implies (and (all_non_loc_op_lstp op_lst ms)
                (all_write_op_lstp op_lst))
           (all_r/w_0_collect
            (mv-nth 1
                    (collect_msg op_lst nil nil Glob_Mem ms))))
  :hints (("GOAL"
           :in-theory (enable node))))


(defthm all_address_validp_nw_op
  ;; we prove that if every address is valid in op_lst, if
  ;; every order is non local and if every order is a read
  ;; then the address is still valid in collect
  (implies (and (all_address_validp op_lst N ms)
                (all_non_loc_op_lstp op_lst ms)
                (all_read_op_lstp op_lst))
           (all_address_validp
            (mv-nth 1
                    (collect_msg op_lst nil nil Glob_Mem ms))
            N ms))
  :hints (("GOAL"
           :in-theory (enable node))))

(defthm all_address_validp_nw_op_write
  ;; we prove that if every address is valid in op_lst, if
  ;; every order is non local and if every order is a write
  ;; then the address is still valid in collect
  (implies (and (all_address_validp op_lst N ms)
                (all_non_loc_op_lstp op_lst ms)
                (all_write_op_lstp op_lst))
           (all_address_validp
            (mv-nth 1
                    (collect_msg op_lst nil nil Glob_Mem ms))
            N ms))
  :hints (("GOAL"
           :in-theory (enable node))))

(defthm all_node_nb_validp_nw_op
  ;; if every node number is valid in op_lst, then collect_msg
  ;; preserves this property for read orders
  (implies (and (all_node_nb_validp op_lst N)
                (all_non_loc_op_lstp op_lst ms)
                (all_read_op_lstp op_lst))
           (all_node_nb_validp
            (mv-nth 1
                    (collect_msg op_lst nil nil Glob_Mem ms))
            N))
  :hints (("GOAL"
           :in-theory (enable node))))

(defthm all_node_nb_validp_nw_op_write
  ;; if every node number is valid in op_lst, then collect_msg
  ;; preserves this property for write orders
  (implies (and (all_node_nb_validp op_lst N)
                (all_non_loc_op_lstp op_lst ms)
                (all_write_op_lstp op_lst))
           (all_node_nb_validp
            (mv-nth 1
                    (collect_msg op_lst nil nil Glob_Mem ms))
            N))
  :hints (("GOAL"
           :in-theory (enable node))))

(defthm true-listp_collect
  ;; we need for further theorems to prove that collect_msg returns
  ;; a true-listp
  (implies (and (true-listp Glob_Mem)
                (all_non_loc_op_lstp op_lst ms))
           (true-listp
            (mv-nth 2
                    (collect_msg op_lst loc_done nw_op Glob_Mem ms))))
  :hints (("GOAL"
           :induct (collect_mem op_lst Glob_Mem ms)
           :do-not-induct t
           :in-theory (enable node))))

(defthm len_mv_nth_2_collect_write
  (implies (and (NODE_MEM_SIZEp ms)
                (all_node_nb_validp op_lst N)
                (integerp N) (< 0 N)
                (equal (len Glob_Mem) (* N ms))
                (true-listp Glob_Mem)
                (all_non_loc_op_lstp op_lst ms)
                (all_write_op_lstp op_lst))
           (equal (len
                   (mv-nth 2
                           (collect_msg op_lst loc_done
                                        nw_op Glob_Mem ms)))
                  (len Glob_Mem)))
  :otf-flg t
  :hints (("GOAL"
           :induct (collect_mem op_lst Glob_Mem ms)
           :do-not-induct t)
;           :in-theory (enable collect_msg))
          ("Subgoal *1/2"
           :use (:instance len_new_memory
                           (op 'write) (loc (nth 2 (car op_lst)))
                           (dat (nth 3 (car op_lst)))
                           (nw_stat nil) (nw_r_dat nil) (nw_dat nil)
                           (nw_r/w nil) (nw_addr nil) (IncomingResponse 0)
                           (NUM_NODE N)
                           (IncomingRequest 0)
                           (node_nb (caar op_lst)))
           :in-theory (disable len_new_memory))))
