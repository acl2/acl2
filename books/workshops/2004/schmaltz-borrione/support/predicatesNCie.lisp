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

;; File: predicatesNCie.lisp
;; Definitions of predicates and helper functions

(in-package "ACL2")

(defmacro addrp (x)
  ;; an address is a non negative integer
  `(and (integerp ,x)
        (<= 0 ,x)))

(defmacro local_addr (addr ms)
  ;; expands to the value of the local address corresponding to addr
  `(mod ,addr ,ms))

(defmacro global_addr (addr node_nb ms)
  ;; expands to the value of the global address corresponding to addr and the
  ;; node number
  `(+ (local_addr ,addr ,ms) (* ,ms ,node_nb)))


(defun rev (l)
  ;; a simple function that reverses a list
  (if (endp l)
      nil
    (append (rev (cdr l)) (list (car l)))))

(defthm true-listp-rev
  ;; we prove that rev returns a true-list
  (true-listp (rev x))
  :rule-classes :type-prescription)

(defun all_loc_op_lstp (op_lst ms)
  ;; defines a list of operations which are all local
  ;; op_lst has the form ( (node_nb op loc dat) .....)
  ;; so loc is the (nth 2 (car op_lst)) ...
  ;; a transfer is local if
  ;; (and (< loc (* ms (1+ node_nb)))
  ;;      (<= (* node_nb ms) loc))
  (if (endp op_lst)
      t
    (let ((loc (nth 2 (car op_lst)))
          (node_nb (caar op_lst)))
      (and (and (< loc (* ms (1+ node_nb)))
                (<= (* ms node_nb) loc))
           (all_loc_op_lstp (cdr op_lst) ms))))
)

(defun all_no_op_lstp (op_lst)
  ;; recognizes a list no_op operations
  (if (endp op_lst)
      t
    (and (equal (nth 1 (car op_lst)) 'NO_OP)
         (all_no_op_lstp (cdr op_lst)))))

(defun all_read_op_lstp (op_lst)
  ;; recognizes a list of read operations
  (if (endp op_lst)
      t
    (and (equal (nth 1 (car op_lst)) 'READ)
         (all_read_op_lstp (cdr op_lst)))))

(defun all_write_op_lstp (op_lst)
  ;; recognizes a list of write operations
  (if (endp op_lst)
      t
    (and (equal (nth 1 (car op_lst)) 'WRITE)
         (all_write_op_lstp (cdr op_lst)))))


(defmacro valid_op_lst (op_lst)
  ;; recognizes a valid operations: read, write or no_op
  `(or (all_no_op_lstp ,op_lst)
       (all_read_op_lstp ,op_lst)
       (all_write_op_lstp ,op_lst)))

(defun all_non_loc_op_lstp (op_lst ms)
  ;; defines a list of operations which are all non local
  ;; op_lst has the form ( (node_nb op loc dat) .....)
  ;; so loc is the (nth 2 (car op_lst)) ...
  ;; a transfer is non local if
  ;; (and (not (< loc (* ms (1+ node_nb))))
  ;;      (not (<= (* node_nb ms) loc)))
  ;; is not true
  (if (endp op_lst)
      t
    (let ((loc (nth 2 (car op_lst)))
          (node_nb (caar op_lst)))
      (and (or (not (< loc (* ms (1+ node_nb))))
               (not (<= (* ms node_nb) loc)))
           (all_non_loc_op_lstp (cdr op_lst) ms))))
)

(defmacro all_read_or_write (op_lst)
  ;; recognizes read or write operations
  `(or (all_read_op_lstp ,op_lst)
       (all_write_op_lstp ,op_lst)))


(defun all_inf_np (l n)
  ;; recognizes a list in which every element is less than n
  (if (endp l)
      t
    (and (< (car l) n)
         (all_inf_np (cdr l) n))))

(defun all_intp (x)
  ;; recognizes a list in which every element is an integer
  (if (endp x)
      t
    (and (integerp (car x))
         (all_intp (cdr x)))))

(defun all_pos_intp (x)
  ;; recognizes a list in which every element is positive or equal to 0
  (if (endp x)
      t
    (and (<= 0 (car x))
         (all_pos_intp (cdr x)))))

(defun AvailableMovep (route n)
  ;; recognizes a route made of available moves
  (if (endp (cdr route))
      t
    (and (if (equal (nth 1 route)
                    (+ 1 (car route)))
             ;; clockwise
             t
           (if (equal (nth 1 route)
                      (+ -1 (car route)))
               ;; counterclockwise
               t
             (if (equal (nth 1 route)
                        (+ (* 2 N) (car route)))
                 ;; across positive
                 t
               (if (equal (nth 1 route)
                          (+ (* -2 N) (car route)))
                   ;; across negative
                   t
                 (if (equal (nth 1 route) 0)
                     ;; special cases around 0
                     (if (equal (car route) (+ -1 (* 4 N)))
                         ;; we come from (+ -1 (* 4 N))
                         t
                       nil)
                   (if (equal (nth 1 route) (+ -1 (* 4 N)))
                       ;; we go to (+ -1 (* 4 N))
                       (if (equal (car route) 0)
                           t
                         nil)
                     nil))))))
         (AvailableMovep (cdr route) n))))


(defun all_inf_routep (lst n)
  ;; defines a predicate that recognizes a travel list where every route
  ;; has the property "all_inf_np"
  (if (endp lst)
      t
    (and (all_inf_np (cdr (car lst)) n)
         (all_inf_routep (cdr lst) n))))

(defun all_node_nb_validp (nw_op bound)
  ;; defines a predicate that recognizes a nw_op list where every
  ;; node number is < bound
  (if (endp nw_op)
      t
    (and (and (integerp (caar nw_op)) ;; get the node number
              (<= 0 (caar nw_op)) (< (caar nw_op) bound))
         (all_node_nb_validp (cdr nw_op) bound))))

(defun all_address_validp (nw_op N ms)
  ;; defines a predicate that recognizes a nw_op list where every
  ;; address is a valid address
  (if (endp nw_op)
      t
    (and (and (integerp (nth 1 (cdar nw_op))) ; get the address
              (<= 0 (nth 1 (cdar nw_op)))
              (< (nth 1 (cdar nw_op)) (* ms N)))
         (all_address_validp (cdr nw_op) N ms))))

(defun all_r/w_0_collect (x)
  ;; recognizes a list x in which every operation (r/w signal) is 0 (read)
  (if (endp x)
      t
    (and (equal (car (cdr (car x))) 0) ; r/w signal
         (all_r/w_0_collect (cdr x)))))

(defun all_r/w_1_collect (x)
  ;; recognizes a list x in which every operation (r/w signal) is 1 (write)
  (if (endp x)
      t
    (and (equal (car (cdr (car x))) 1) ; r/w signal
         (all_r/w_1_collect (cdr x)))))


(defun all_r/w_1 (x)
  ;; we define a predicate for list of read operations (r/w = 1)
  (if (endp x)
      t
    (and (equal (caaar x) 1)
         (all_r/w_1 (cdr x)))))

(defun all_r/w_0 (x)
  ;; we define a predicate for list of write operations (r/w = 0)
  (if (endp x)
      t
    (and (equal (caaar x) 0)
         (all_r/w_0 (cdr x)))))


(defmacro NODE_MEM_SIZEp (x)
  ;; macro that defines the type of the size of a memory
  `(and (integerp ,x)
        (< 0 ,x)))

(defun all_int_routep (lst)
  ;; recognizes a list where every route is a list of integers
  (if (endp lst)
      t
    (and (all_intp (cdr (car lst)))
         (all_int_routep (cdr lst)))))

(defun all_pos_intp_route_lstp (x)
  ;; recognizes a list of lists of positive integers
  (if (endp x)
      t
    (and (all_pos_intp (cdr (car x)))
         (all_pos_intp_route_lstp (cdr x)))))


(defun all_availableMovep_routep (tl n)
  ;; recognizes a list where every route has the property
  ;; "AvailableMovep"
  ;; tl is a travel list and (cdr (car tl)) returns the route
  (if (endp tl)
      t
    (and (AvailableMovep (cdr (car tl)) n)
         (all_availableMovep_routep (cdr tl) n))))

(defun all_no_duplicatesp (l)
  ;; recognizes a travel list in which every route contains no duplicate
  (if (endp l)
      t
    (and (no-duplicatesp (cdr (car l)))
         (all_no_duplicatesp (cdr l)))))

(defun all_consp_route (tl)
  ;; recognizes a travel list in which every route is a consp
  (if (endp tl)
      t
    (and (consp (cdr (car tl)))
         (all_consp_route (cdr tl)))))

(defun all_true-listp (tl)
  ;; recognizes a travel list in which every route is a true-list
  (if (endp tl)
      t
    (and (true-listp (cdr (car tl)))
         (all_true-listp (cdr tl)))))

(defun tlp (tl)
  ;; recognizes a travel list
  (if (endp tl)
      (null tl)
    (and (consp (car tl))
         (tlp (cdr tl)))))

(defun all_ok_resultp (res_lst)
  ;; res_lst = ( (i st dat) ... )
  (if (endp res_lst)
      t
    (and (equal (cadar res_lst) 'OK)
         (all_ok_resultp (cdr res_lst)))))

(defun all_dat_okp (resp_lst res)
  ;; res is ok if every data of resp_lst is equal to the data of res
  ;; resp_lst = ( ((st dat) route) ... )
  ;; res      = ( (i st dat) ...)
  (if (endp resp_lst)
      t
    (if (endp res)
        nil
      (and (equal (cadaar resp_lst) ;; data field of resp_lst
                  (caddar res))      ;; data field of res
           (all_dat_okp (cdr resp_lst) (cdr res)))))
)

(defun all_stat_okp (resp_lst res)
  ;; res is OK if every status in it is equal to the status in resp_lst
  ;; resp_lst = ( ((st dat) route) ... )
  ;; res      = ( (i st dat) ...)
  (if (endp resp_lst)
      t
    (if (endp res)
        nil
      (and (equal (caaar resp_lst) ;; st field of resp_lst
                  (cadar res)) ;; st field of res
           (all_stat_okp (cdr resp_lst) (cdr res)))))
)


(defun all_ok_dat_writep (req_lst res)
  ;; for write requests, the returned data is the data sent in the request
  (if (endp res)
      t
    (if (endp req_lst)
        nil
      (and (equal (nth 1 (caar res)) ;; data field of the result
                  (nth 2 (caar req_lst)))
           (all_ok_dat_writep (cdr req_lst) (cdr res))))))

(defmacro last_route (l)
  ;; gets the last element of a route
  `(car (last (cdr (car ,l)))))


(defun all_ok_nw_req_p (req_lst ms)
  ;; req_lst = ( ( (r/w addr dat) route) ...)
  ;; this predicate assures that every request is routed to
  ;; a node number which contains the address of the request
  (if (endp req_lst)
      t
    (let ((addr (nth 1 (caar req_lst))) ;; get the address field
          (node_nb (car (last (cdar req_lst)))));; get the last of the route
      (and (and (<= (* node_nb ms) addr)
                (< addr (* ms (1+ node_nb))))
           (all_ok_nw_req_p (cdr req_lst) ms))))
)

(defun all_existing_addrp (tl N ms)
  ;; we define a predicate that recognizes a list of operations in which every
  ;; address is less than the len of the global memory, i.e. that the address
  ;; exists in the network
  (if (endp tl)
      t
    (and (< (nth 1 (caar tl)) (* N ms))
         (all_existing_addrp (cdr tl) N ms))))

(defun all_ok_statusp (x)
  ;; now we define a predicate that recognizes a list where all the status are
  ;; OK
  (if (endp x)
      t
    (and (equal (caaar x) 'OK)
         (all_ok_statusp (cdr x)))))

(defun all_addrp (no_over_lst)
  ;; all the address of all the operations satisfy addrp(x)
  (if (endp no_over_lst)
      t
    (and (addrp (nth 1 (caar no_over_lst)))
         (all_addrp (cdr no_over_lst)))))

