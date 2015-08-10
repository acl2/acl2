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

;; File: node.lisp
;; Memory Structure and Validation
;; Definition of Interfaces and Transfers
;; Proof of the Node System

(in-package "ACL2")

;; we import some definitions and predicates
(include-book "predicatesNCie")

;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------
;;
;;                         MEMORY MODEL
;;
;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------


;; The memory is represented as a list. We import useful books on lists

(include-book "../../../../data-structures/list-defuns")

(include-book "../../../../data-structures/list-defthms")

;;-----------------------------------------------------------------------
;;                    DEFINITION OF THE ADDRESS MAPPING
;;-----------------------------------------------------------------------

(defun addr_map (x y ms)
  (if (equal y (mod x ms))
      t
    nil))

;;-----------------------------------------------------------------------
;;                   FUNCTIONAL MEMORY MODEL
;;-----------------------------------------------------------------------

;;                         LOCAL MEMORY

;; Definition of the basic operations:

;; A read is simply a call to "nth"
(defun mem_read (addr memo)
  (mv (nth addr memo) memo))

;; A write is simply a call to "update-nth":
(defun mem_write (addr memo item)
  (mv item (put-nth addr item memo)))

;; We define the memory unit of a node
(defun MEMORY (op addr item memo)
  (if (< addr (len memo)) ;; then we are OK and can do op
      (if (equal op 'read)
          (mv-let (dat mem)
                  (mem_read addr memo)
                  (mv 'OK dat mem))
        (if (equal op 'write)
            (mv-let (dat mem)
                    (mem_write addr memo item)
                    (mv 'OK dat mem))
          (mv 'INV_OP 'INV_DATA memo))) ;; the output is only one list
    (mv 'INV_ADDR 'INV_DATA memo)))

;;                 VALIDATION OF THE MEMORY FUNCTION

;; a type prescription on true-listp
(defthm true-listp_new_mem
  (implies (true-listp mem)
           (true-listp
            (mv-nth 2
             (memory op addr item mem))))
  :rule-classes :type-prescription)

;; now I prove what is the length of the modified mem
(defthm len_memory
  (equal (len
          (mv-nth 2
           (memory op addr item mem)))
         (len mem)))

;; If the address is greater than the len of the memory then
(defthm addr_out_of_bounds_stat
  (implies (<= (len mem) addr)
           (equal (car
                   (memory op addr item mem))
                  'INV_ADDR)))

(defthm addr_out_of_bounds_dat
  (implies (<= (len mem) addr)
           (equal (mv-nth 1
                   (memory op addr item mem))
                  'INV_DATA)))

(defthm addr_out_of_bounds_mem
  (implies (<= (len mem) addr)
           (equal (mv-nth 2
                   (memory op addr item mem))
                  mem)))

(defthm stat_read_control
  (implies (and (equal op 'read) ; read operation
                (< addr (len mem))) ; on a valid address
           (equal (car
                   (memory op addr item mem))
                  'OK)))

(defthm dat_read_control
  (implies (and (equal op 'read) ; read operation
                (< addr (len mem))) ; on a valid address
           (equal (mv-nth 1
                   (memory op addr item mem))
                  (nth addr mem))))

;; this theorem proves that the memory is not modified by read operations
(defthm mem_read_control
  (implies (and (equal op 'read) ; read operation
                (< addr (len mem))) ; on a valid address
           (equal (mv-nth 2
                   (memory op addr item mem))
                  mem)))

;; Now we add rule to reduce write operations

(defthm stat_write_control
  (implies (and (equal op 'write) ; write operation
                (< addr (len mem))) ; on a valid address
           (equal (car    ; here If I use an accessor the rule is not used
                   (memory op addr item mem))
                  'OK)))

(defthm dat_write_control
  (implies (and (equal op 'write) ; write operation
                (< addr (len mem))) ; on a valid address
           (equal (mv-nth 1
                   (memory op addr item mem))
                  item)))

;; this theorem proves that the memory location to be written is written with
;; the right item
(defthm mem_write_control
  (implies (and (equal op 'write) ; write operation
                (< addr (len mem))) ; on a valid address
           (equal (mv-nth 2
                   (memory op addr item mem))
                  (put-nth addr item mem))))

;(defmacro addrp (x)
;  `(and (integerp ,x)
;        (<= 0 ,x)))

;; the next theorem proves that the other location are not modified!
(defthm mem_write_control_not_written
  (implies (and (equal op 'write)
                (< addr1 (len mem))
                (< addr2 (len mem))
                (addrp addr1) (addrp addr2)
                (not (equal addr1 addr2)))
           (equal (nth addr1
                       (mv-nth 2
                        (memory op addr2 item mem)))
                  (nth addr1 mem))))

;; now we disable the memory function and only the rules will be used
(in-theory (disable memory))


;;                       GLOBAL MEMORY

;; The global memory is represented as the ordered concatenation of all
;; local memory units.

;; We define a function that extracts the memory unit of a

(defun get_local_mem (Glob_Mem node_nb ms)
  (firstn ms (nthcdr (* node_nb ms) Glob_Mem)))

;; we prove that the length of the local memory is equal to the
;; parameter ms

;; we load books on arithmetics

(include-book "../../../../arithmetic-3/bind-free/top")

(set-non-linearp t)

(include-book "../../../../arithmetic-3/floor-mod/floor-mod")

;; for "historical reasons" we keep two versions of some lemmas

(defthm len_get_local_mem
  (implies (and (NODE_MEM_SIZEp ms)
                (integerp node_nb) (<= 0 node_nb)
                (< node_nb (floor (len Glob_Mem) ms)))
           (equal (len (get_local_mem Glob_Mem node_nb ms))
                  ms)))

(set-non-linearp nil)

(defthm len_get_local_mem2
  (implies (and (NODE_MEM_SIZEp ms)
                (integerp node_nb) (<= 0 node_nb)
                (equal (len Glob_Mem) (* ms NUM_NODE))
                (< node_nb NUM_NODE) (integerp NUM_NODE) (< 0 NUM_NODE))
           (equal (len (get_local_mem Glob_Mem node_nb ms))
                  ms)))

;; we define a function that updates a local memory
(defun update_local_mem (Glob_Mem memo node_nb ms)
    (append (firstn (* node_nb ms) Glob_Mem)
            (append memo
                    (nthcdr (* (+ 1 node_nb) ms) Glob_Mem))))

;; and we prove an important property on it:
;; if a memory is updated by its actual memory, then update does not
;; change this memory

(defthm append_firstn_cdr_lemma
  (implies (and (true-listp L)
                (integerp a) (integerp n)
                (<= 0 a) (<= 0 n))
           (equal (append (firstn a (nthcdr n L))
                          (nthcdr (+ a n) L))
                  (nthcdr n L)))
  :otf-flg t
  :hints (("GOAL"
           :induct (nthcdr n L)
           :do-not-induct t
           :in-theory (disable prefer-positive-addends-equal
                               prefer-positive-addends-<)
           :do-not '(eliminate-destructors generalize fertilize))))



(defthm update_and_get_local_ok
  (implies (and (equal memo (get_local_mem Glob_Mem node_nb ms))
                (integerp node_nb) (<= 0 node_nb)
                (true-listp Glob_Mem)
                (< node_nb (floor (len Glob_Mem) ms))
                (NODE_MEM_SIZEp ms))
           (equal (update_local_mem Glob_Mem memo node_nb ms)
                  Glob_Mem))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize fertilize)
           :do-not-induct t)))

;; we prove a property on the length of an updated memory

(set-non-linearp t)

(defthm len_update_local_mem
  (implies (and (true-listp Glob_Mem) (NODE_MEM_SIZEp ms)
                (equal (len memo) ms)
                (< node_nb (floor (len Glob_Mem) ms))
                (integerp node_nb) (<= 0 node_nb))
           (equal (len (update_local_mem Glob_Mem memo node_nb ms))
                  (len Glob_Mem)))
  :hints (("GOAL"
           :in-theory (enable update_local_mem))))

(set-non-linearp nil)


(defthm len_update_local_mem2
  (implies (and (true-listp Glob_Mem) (NODE_MEM_SIZEp ms)
                (equal (len memo) ms)
                (equal (len Glob_Mem) (* ms NUM_NODE))
                (integerp NUM_NODE) (< 0 NUM_NODE)
                (< node_nb NUM_NODE)
                (integerp node_nb) (<= 0 node_nb))
           (equal (len (update_local_mem Glob_Mem memo node_nb ms))
                  (len Glob_Mem))))

;; we prove that it returns a true-listp

(defthm true-listp_update_local_mem
  (implies (and (true-listp Glob_Mem) (NODE_MEM_SIZEp ms)
                (integerp node_nb) (<= 0 node_nb))
           (true-listp (update_local_mem Glob_Mem memo node_nb ms)))
  :hints (("GOAL"
           :in-theory (enable update_local_mem)))
  :rule-classes :type-prescription)

;; then we disable these functions

(in-theory (disable update_local_mem get_local_mem))


;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------
;;
;;                         ADDRESS DECODER
;;
;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------


;; the decoder is the following component

;;               -------------
;;              |             |
;;     -------->|   Decoer    |-------->
;;      loc     |      n      |  l/nl
;;               -------------

;; n is the number of the node the decoder is part of
;; ms is the size of each memory unit
;; loc is an input address

(defun decoder (loc ms node_nb)
  (if (and (< loc (* (1+ node_nb) ms)) ;; less than the first address of next
      ;; node
           (<= (* node_nb ms) loc)) ;; greater than or equal to the first
  ;; address of the current node.
      1 ; l/nl=1 for local transfers
    0)) ; l/nl=0 for non local transfers


;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------
;;
;;                         DEFINITION OF INTERFACES
;;
;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------



;;------------------------------------------------------------------------
;;                            MASTER INTERFACE
;;------------------------------------------------------------------------

;; the protocol is very simple, and a master can only
;; do some read or write operation at a given address
;; as the work done for buses, I model the interface
;; by two functions
;;
;; a master interface is the following component
;;
;;                --------------
;;               |              |
;;               |              |
;;   ----------->|   MI_req     |----------->
;;   op, loc, dat|              | r/w, addr, data
;;               |              |
;;   <-----------|   MI_res     |<----------
;;   stat r-dat  |              | stat r-dat
;;               |              |
;;                --------------


(defun MI_req (op loc dat)
  (if (equal op 'read) ; if read then r/w = 1
      (mv 1 loc dat)
    (mv 0 loc dat) ; else write, r/w = 0
))

;; ACL2 proves CONSP and TRUE-LISTP of this function

(defun MI_res (stat r_dat)
  (mv stat r_dat))

;; ACL2 proves CONSP and TRUE-LISTP of this function

;;------------------------------------------------------------------------
;;                           Slave Interfaces
;;------------------------------------------------------------------------


;; the protocol is very simple, a slave just
;; transmits a read or a write command to a memory
;; as the work done for buses, I model the interface
;; by two functions
;;
;; a slave interface is the following component
;;
;;                  --------------
;;                 |              |
;;                 |              |
;;     ----------->|   SI_ord     |----------->
;;  r/w, addr, data|              | op, loc, dat
;;                 |              |
;;     <-----------|   SI_resp    |<----------
;;     stat r-dat  |              | stat r-dat
;;                 |              |
;;                  --------------

;(defmacro local_addr (addr ms)
;  `(mod ,addr ,ms))

(defun SI_ord (r/w addr data dec_sl ms)
  (if (equal dec_sl 1)
      (if (equal r/w 1)
          (mv 'read (local_addr addr ms) data)
        (mv 'write (local_addr addr ms) data))
    (mv 'IDLE 'NO_LOC 'NO_DATA)))

(defun SI_resp (stat r-dat dec_sl)
  (if (equal dec_sl 1)
      (mv stat r-dat)
    (mv 'IDLE 'NO_DATA)))


;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------
;;
;;                 FUNCTIONAL DEFINITION OF TRANSFERS
;;
;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------



;;------------------------------------------------------------------------
;;                    LOCAL TRANSFERS via a BUS
;;------------------------------------------------------------------------


;; here we define the functional representation of "local" transferts
;; that will take place using a bus.

;; we define a bus a the identity functiom

(defun Bus (x)
  x)

;; Transmission of Orders

(defun trans_ord (op loc dat dec_sl ms)
  (mv-let (r/w addr dat)
          (MI_req op loc dat)
          (let ((msg (bus (list r/w addr dat))))
            (let ((r/w (car msg))
                  (addr (cadr msg))
                  (dat (caddr msg)))
              (SI_ord r/w addr dat dec_sl ms)))))

;; Transmission of a Result

(defun trans_res (stat r_dat dec_sl)
  (mv-let (status r_dat)
          (SI_resp stat r_dat dec_sl)
          (let ((msg (bus (list status r_dat))))
            (let ((status (car msg))
                  (r_dat (cadr msg)))
              (MI_res status r_dat)))))


;; now we can prove Theorem 1, in case of transfers via our simple bus function

(defthm Theorem1_for_bus
  (mv-let (nop nloc ndat)
          (trans_ord op loc dat 1 ms)
          (implies (or (equal op 'read)
                       (equal op 'write))
                   (and (equal nop op)
                        (equal ndat dat)
                        (addr_map loc nloc ms)))))

;; we can also prove Theorem 2

(defthm Theorem2_for_bus
  (mv-let (nstatus nr_dat)
          (trans_res status r_dat 1)
          (and (equal nstatus status)
               (equal nr_dat r_dat))))

;; now we can define a transfer (like Definition 3)

(defun Bus_transfer (op loc dat Glob_Mem sl_select node_nb ms)
  (mv-let (op loc dat)
          (trans_ord op loc dat sl_select ms)
          (mv-let (stat dat memo)
                  (Memory op loc dat
                          (get_local_mem Glob_Mem node_nb ms))
                  (mv-let (st d)
                          (trans_res stat dat sl_select)
                          (mv st d
                              (update_local_mem Glob_Mem memo
                                                node_nb ms))))))


;;------------------------------------------------------------------------
;;                              NETWORK TRANSFERS
;;------------------------------------------------------------------------


(defun nw_transfer (r/w addr data Glob_Mem sl_select node_nb ms)
  (mv-let (op loc dat)
          (si_ord r/w addr data sl_select ms)
          (mv-let (stat dat memo)
                  (memory op loc dat
                                  (get_local_mem Glob_Mem node_nb ms))
                  (mv-let (st d)
                          (si_resp stat dat sl_select)
                          (mv st d
                              (update_local_mem Glob_Mem memo
                                                node_nb ms))))))



;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------
;;
;;                 FUNCTIONAL DEFINITION OF A NODE SYSEM
;;
;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------

;; a node is the following component:

;;                  ---------------
;;                 |               |
;;                 |               |
;;     ----------->|               |
;;    op, loc, dat |     NODE      |
;;                 |               |
;;     <-----------|               |
;;    stat r-dat   |               |
;;                 |               |
;;                 |               |
;;                 |               |
;;                  ---------------
;;                    |        /|\
;;                    |         |
;;                    |         |
;;                    | nw-msg  |
;;                   \|/        |
;;
;;                    (to the network)


;; and it is represented by the following function:
;; nw-msg is a message that comes from the network
;; ms is the size of the memory = (len memo)

;; If the transfer can be done locally, then node calls "Bus_transfer"
;; else it emits a message (= r/w addr data) and grabs a reply if there is a
;; valid answer. When a message is coming, it is either a response or
;; a request.
;; The flags IncomingResponse IncomingRequest solve that.

;; what are the outputs of this component?
;;     - a result (stat r-dat)
;;     - a network message which is either a request or a response
;;     - global memory

(defun node (op loc dat Glob_Mem
                nw_stat nw_r_dat ;; stat and dat coming from the network
                nw_r/w nw_addr nw_dat ;; msg coming from the network
                IncomingResponse IncomingRequest ;; commands coming from the scheduler
                node_nb ;; node number
                ms ;; size of local memory
                )
  (if (equal op 'NO_OP) ;; node master is doing nothing
      ;; if there is a command from the scheduler, we do it
      (if (equal IncomingRequest 1)
          (let ((dec (decoder ;;;;(local_addr nw_addr ms) ENORME!!!!
                      nw_addr ms node_nb)))
            (mv-let (st dat memo)
                    (nw_transfer nw_r/w nw_addr nw_dat Glob_Mem
                                 dec node_nb ms)
                    (mv 'NO_OP 'NO_DATA ;; to the master
                        st dat 'NO_MSG_DATA ;; res sent to th nw
                        memo))) ;; new memory
        ;; that was for incoming msg, now we treat the case of incoming reply
        (if (equal IncomingResponse 1)
            (mv-let (stat r_dat)
                    (MI_res nw_stat nw_r_dat)
                    (mv stat r_dat ;; rep sent to the master
                        'NO_MSG_R/W 'NO_MSG_ADDR 'NO_MSG_DATA ;; nothing sent to the nw
                        Glob_Mem)) ;; the memory is not changed
          (mv 'NO_OP 'NO_DATA 'NO_MSG_R/W
              'NO_MSG_ADDR 'NO_MSG_DATA Glob_Mem)))
    ;; else the node master is doing a write or read operation
    (let ((dec (decoder loc ms node_nb)))
      (if (equal dec 1) ;; local transfer
          (mv-let (st dat memo)
                  (bus_transfer op loc dat Glob_Mem
                                  dec node_nb ms)
                  (mv st dat ;; to the node master
                      'NO_MSG_R/W 'NO_MSG_ADDR 'NO_MSG_DATA ;; to the nw
                      memo))
              ;; else the node sends a msg to the nw
        (mv-let (r/w addr data)
                (mi_req op loc dat)
                (mv 'NO_OP 'NO_DATA ;; nothing to the master
                    r/w addr data ;; msg sent to the nw
                    Glob_Mem))))))


;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------
;;
;;                   VALIDATION OF THE NODE SYSTEM
;;
;;-----------------------------------------------------------------------
;;-----------------------------------------------------------------------

;; to simplify the next proofs, we prove some theorems to validate
;; the node system

;; most of these lemmas are proven in less than 1 second by ACL2,
;; but when the rules derived from them are useful and rewrite
;; terms in simpler ones.

;; for good write or read operations, the returned status is OK

(defthm nw_stat_node_=_OK_no_op_write
  (implies (and (equal IncomingRequest 1) (equal op 'NO_OP)
                (equal nw_r/w 0) ;; nw write
                (integerp node_nb) (<= 0 node_nb)
                ;; a node_nb is less than the maximum number of nodes
                ;; Note: (len Glob_Mem) = (* ms Num_Node)
                ;; the next hypothesis states the same thing
                ;; but avoid free variables
                (< node_nb (floor (len Glob_Mem) ms))
                ;; nw_addr is a valid address for the node_nb
                (<= (* node_nb ms) nw_addr)
                (< nw_addr (* (1+ node_nb) ms))
                (addrp nw_addr) (NODE_MEM_SIZEp ms))
           (equal (mv-nth 2
                          (node op loc dat Glob_Mem
                                nw_stat nw_r_dat nw_r/w nw_addr nw_dat
                                IncomingResponse IncomingRequest node_nb ms))
                  'OK)))

(defthm nw_stat_node_=_OK_no_op_read
  (implies (and (equal IncomingRequest 1) (equal op 'NO_OP)
                (equal nw_r/w 1) ;; nw read
                (integerp node_nb) (<= 0 node_nb)
                ;; a node_nb is less than the maximum number of nodes
                ;; Note: (len Glob_Mem) = (* ms Num_Node)
                ;; the next hypothesis states the same thing
                ;; but avoid free variables
                (< node_nb (floor (len Glob_Mem) ms))
                ;; nw_addr is a valid address for the node_nb
                (<= (* node_nb ms) nw_addr)
                (< nw_addr (* (1+ node_nb) ms))
                (addrp nw_addr) (NODE_MEM_SIZEp ms))
           (equal (mv-nth 2
                          (node op loc dat Glob_Mem
                                nw_stat nw_r_dat nw_r/w nw_addr nw_dat
                                IncomingResponse IncomingRequest node_nb ms))
                  'OK)))

;; for good operations the returned data is OK

(defthm nw_data_node_ok_write
  (implies (and (equal IncomingRequest 1) (equal op 'NO_OP)
                (equal nw_r/w 0) ;; nw write
                (integerp node_nb) (<= 0 node_nb)
                ;; a node_nb is less than the maximum number of nodes
                ;; Note: (len Glob_Mem) = (* ms Num_Node)
                ;; the next hypothesis states the same thing
                ;; but avoid free variables
                (< node_nb (floor (len Glob_Mem) ms))
                ;; nw_addr is a valid address for the node_nb
                (<= (* node_nb ms) nw_addr)
                (< nw_addr (* (1+ node_nb) ms))
                (addrp nw_addr) (NODE_MEM_SIZEp ms))
           (equal (mv-nth 3
                          (node op loc dat Glob_Mem
                                nw_stat nw_r_dat nw_r/w nw_addr nw_dat
                                IncomingResponse IncomingRequest node_nb ms))
                  nw_dat)))

(defthm nw_data_node_ok_read
  (implies (and (equal IncomingRequest 1) (equal op 'NO_OP)
                (equal nw_r/w 1) ;; nw read
                (integerp node_nb) (<= 0 node_nb)
                ;; a node_nb is less than the maximum number of nodes
                ;; Note: (len Glob_Mem) = (* ms Num_Node)
                ;; the next hypothesis states the same thing
                ;; but avoid free variables
                (< node_nb (floor (len Glob_Mem) ms))
                ;; nw_addr is a valid address for the node_nb
                (<= (* node_nb ms) nw_addr)
                (< nw_addr (* (1+ node_nb) ms))
                (addrp nw_addr) (NODE_MEM_SIZEp ms))
           (equal (mv-nth 3
                          (node op loc dat Glob_Mem
                                nw_stat nw_r_dat nw_r/w nw_addr nw_dat
                                IncomingResponse IncomingRequest node_nb ms))
                  (nth (local_addr nw_addr ms)
                       (get_local_mem Glob_Mem node_nb ms)))))

(defthm nw_mem_node_ok_read
  (implies (and (equal IncomingRequest 1) (equal op 'NO_OP)
                (true-listp Glob_Mem) (equal nw_r/w 1) ;; nw read
                (integerp node_nb) (<= 0 node_nb)
                ;; a node_nb is less than the maximum number of nodes
                ;; Note: (len Glob_Mem) = (* ms Num_Node)
                ;; the next hypothesis states the same thing
                ;; but avoid free variables
                (< node_nb (floor (len Glob_Mem) ms))
                ;; nw_addr is a valid address for the node_nb
                (<= (* node_nb ms) nw_addr)
                (< nw_addr (* (1+ node_nb) ms))
                (addrp nw_addr) (NODE_MEM_SIZEp ms))
           (equal (mv-nth 5
                          (node op loc dat Glob_Mem
                                nw_stat nw_r_dat nw_r/w nw_addr nw_dat
                                IncomingResponse IncomingRequest node_nb ms))
                  Glob_Mem)))

(defthm update_get_and_put_nth_lemma
  (implies (and (true-listp L)
                (integerp b) (integerp c)
                (<= 0 b) (<= 0 c) (< b c))
           (equal (append (firstn c (put-nth b v L))
                          (nthcdr c L))
                  (put-nth b V L))))

(defthm update_get_and_put_nth
  (implies (and (true-listp L)
                (integerp a) (integerp b) (integerp c)
                (<= 0 a) (<= 0 b) (<= 0 c) (< b c))
           (equal (append (firstn a L)
                          (put-nth b v (firstn c (nthcdr a L)))
                          (nthcdr (+ a c) L))
                  (put-nth (+ a b) v L)))
  :otf-flg t
  :hints (("GOAL"
           :induct (PUT-NTH B V (FIRSTN C (NTHCDR A L)))
           :do-not-induct t
           :in-theory (disable prefer-positive-addends-equal
                               prefer-positive-addends-<)
           :do-not '(eliminate-destructors generalize fertilize))))

(defthm update_get_and_put
  (implies (and (true-listp Glob_Mem)
                (equal memo
                       (put-nth b v
                                (get_local_mem Glob_Mem node_nb ms)))
                (integerp node_nb) (<= 0 node_nb)
                (integerp b) (<= 0 b)
                (< b ms)
                (NODE_MEM_SIZEp ms))
           (equal (update_local_mem Glob_Mem memo node_nb ms)
                  (put-nth (+ (* node_nb ms) b)
                           v GLOB_MEM)))
  :hints (("GOAL"
           :do-not-induct t
           :use (:instance update_get_and_put_nth
                           (a (* ms NODE_NB))
                           (c ms)
                           (L GLOB_MEM))
           :in-theory (e/d (update_local_mem get_local_mem)
                           (PUT-NTH-FIRSTN PUT-NTH-NTHCDR
                            update_get_and_put_nth)))))

;(defmacro global_addr (addr node_nb ms)
;  `(+ (local_addr ,addr ,ms) (* ,ms ,node_nb)))

(defthm nw_mem_node_ok_write
  (implies (and (equal IncomingRequest 1) (equal op 'NO_OP)
                (equal nw_r/w 0) ;; nw write
                (true-listp Glob_Mem)
                (integerp node_nb) (<= 0 node_nb)
                ;; a node_nb is less than the maximum number of nodes
                ;; Note: (len Glob_Mem) = (* ms Num_Node)
                ;; the next hypothesis states the same thing
                ;; but avoid free variables
                (< node_nb (floor (len Glob_Mem) ms))
                ;; nw_addr is a valid address for the node_nb
                (<= (* node_nb ms) nw_addr)
                (< nw_addr (* (1+ node_nb) ms))
                (addrp nw_addr) (NODE_MEM_SIZEp ms))
           (equal (mv-nth 5
                          (node op loc dat Glob_Mem
                                nw_stat nw_r_dat nw_r/w nw_addr nw_dat
                                IncomingResponse IncomingRequest node_nb ms))
                  (put-nth (global_addr nw_addr node_nb ms)
                           nw_dat Glob_Mem)))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize fertilize)
           :use (:instance update_get_and_put
                           (b (mod nw_addr ms))
                           (memo
                            (put-nth (mod nw_addr ms)
                                     nw_dat
                                     (get_local_mem Glob_Mem node_nb ms)))
                           (v nw_dat))
           ;; use hint require because of free variables
           :in-theory (disable update_get_and_put)
           :do-not-induct t)))

(set-non-linearp t)

(defthm len_new_memory
  (implies (and (NODE_MEM_SIZEp ms)
                (integerp node_nb) (<= 0 node_nb)
                (integerp NUM_NODE) (< 0 NUM_NODE)
                (< node_nb NUM_NODE)
                (equal (len Glob_Mem) (* ms NUM_NODE))
                (true-listp Glob_Mem))
           (equal (len (mv-nth 5
                               (node op loc dat Glob_Mem
                                     nw_stat nw_r_dat nw_r/w nw_addr nw_dat
                                     IncomingResponse IncomingRequest node_nb ms)))
                  (len Glob_Mem)))
  :hints (("GOAL"
           :use ((:instance len_update_local_mem2
                            (NUM_NODE NUM_NODE)
                            (memo
                             (MV-NTH 2
                                     (MEMORY 'READ
                                             (MOD LOC ms)
                                             DAT
                                             (GET_LOCAL_MEM
                                              GLOB_MEM NODE_NB
                                              ms)))))
                 (:instance len_update_local_mem2
                            (NUM_NODE NUM_NODE)
                            (memo
                             (MV-NTH 2
                                     (MEMORY 'WRITE
                                             (MOD LOC ms)
                                             DAT
                                             (GET_LOCAL_MEM
                                              GLOB_MEM NODE_NB
                                              ms)))))
                 (:instance len_update_local_mem2
                            (NUM_NODE NUM_NODE)
                            (memo
                             (MV-NTH 2
                                     (MEMORY 'IDLE
                                             'NO_LOC
                                             'NO_DATA
                                             (GET_LOCAL_MEM
                                              GLOB_MEM NODE_NB
                                              ms)))))
                 (:instance len_update_local_mem2
                            (NUM_NODE NUM_NODE)
                            (memo
                             (GET_LOCAL_MEM GLOB_MEM NODE_NB ms)))
                 (:instance len_update_local_mem2
                            (NUM_NODE NUM_NODE)
                            (memo
                             (PUT-NTH (MOD NW_ADDR ms)
                                      NW_DAT
                                      (GET_LOCAL_MEM GLOB_MEM NODE_NB
                                                     ms)))))
           :in-theory (disable len_update_local_mem2))))

(set-non-linearp nil)

(defthm true-listp_new_memory
  (implies (and (NODE_MEM_SIZEp ms)
                (integerp node_nb) (<= 0 node_nb)
                (true-listp Glob_Mem))
           (true-listp (mv-nth 5
                               (node op loc dat Glob_Mem
                                     nw_stat nw_r_dat nw_r/w nw_addr nw_dat
                                     IncomingResponse IncomingRequest node_nb ms))))
  :rule-classes :type-prescription)

;; now we can disable function node

(in-theory (disable node))

;;Summary
;;Form:  (CERTIFY-BOOK "node" ...)
;;Rules: NIL
;;lWarnings:  Guards, Subsume and Non-rec
;;Time:  12.31 seconds (prove: 7.54, print: 0.11, other: 4.66)
;; "/home/julien/work/ProofReplayOctagonFMCAD04/node.lisp"
