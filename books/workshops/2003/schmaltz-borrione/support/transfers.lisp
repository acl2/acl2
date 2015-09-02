;------------------------------------------------------------------------
;
; File : transfers.lisp
; Author : Julien Schmaltz
; July 2003
; TIMA-VDS
; Grenoble, France
;
;------------------------------------------------------------------------


(in-package "ACL2")

(include-book "decoder")
(include-book "arbiter")


;-----------------------------------------------------------------------
;
;            Modeling the two interfaces
;
;----------------------------------------------------------------------

(defun slave_interface (HSEL HWRITE HADDR HWDATA SD MEM_SIZE)
  (if (equal HSEL 1)
      (list (list (if (equal HWRITE 1)
                      'read
                      'write)
                  (mod HADDR MEM_SIZE) HWDATA)
            (list SD))

      nil))

(defun O-slave (x)
  (nth 0 (nth 0 x)))

(defun L-slave (x)
  (nth 1 (nth 0 x)))

(defun D-slave (x)
  (nth 2 (nth 0 x)))

(defun HRDATA (x)
  (nth 0 (nth 1 x)))

(defun master_interface (O L D HRDATA HGRANT)
  (if (equal HGRANT 1)
      (list (list (if (equal O 'Read)
                      1
                      0)
                  L
                  D)
            (list HRDATA))
      nil))

(defun HWRITE (x)
  (nth 0 (nth 0 x)))

(defun HADDR (x)
  (nth 1 (nth 0 x)))

(defun HWDATA (x)
  (nth 2 (nth 0 x)))

(defun D-master (x)
  (nth 0 (nth 1 x)))

;-----------------------------------------------------------------------
;
;            Modeling transfers
;
;----------------------------------------------------------------------

; a transfer from a master to a slave is the result of the slave interface
; function applied on the result of the master interface function

(defun trans_M_to_S (O L D N Card_S P Last_Granted MREQ Slave_Number
                     SD MEM_SIZE)
  (slave_interface
   (nth Slave_Number
        (decoder MEM_SIZE Card_S
                 (HADDR
		  (Master_interface O L D SD
				    (nth (master_num MREQ N Last_Granted)
					 (arbiter N P MREQ Last_Granted))))))
   (HWRITE
    (Master_interface O L D SD
		      (nth (master_num MREQ N Last_Granted)
			   (arbiter N P MREQ Last_Granted))))
   (HADDR
    (Master_interface O L D SD
		      (nth (master_num MREQ N Last_Granted)
			   (arbiter N P MREQ Last_Granted))))
   (HWDATA
    (Master_interface O L D SD
		      (nth (master_num MREQ N Last_Granted)
			   (arbiter N P MREQ Last_Granted))))
   SD MEM_SIZE))

; the function returns a true-list


; a transfer from a slave to a master is the result of the master interface
; function applied on the result of the slave interface function

(defun trans_S_to_M (O L D SD MEM_SIZE Card_S MREQ N P
                     HWRITE HADDR HWDATA Slave_Number Last_granted)
  (master_interface O L D
                    (HRDATA
                     (slave_interface
                      (nth Slave_Number
                           (decoder MEM_SIZE Card_S L))
                      HWRITE
                      HADDR
                      HWDATA
                      SD
                      MEM_SIZE))
                    (nth (master_num MREQ N Last_Granted)
                         (arbiter N P MREQ Last_Granted))))
; returns a true-list



; validation of transmission of the address and the data
; from the master to the slave

(defthm trans_M_to_S_thm
  (implies (and
            ; P is the number of priority level(s)
            (integerp P) (equal P (len MREQ))
            ; N is the length of each level
            (equal (len (car MREQ)) N)
            ; at least one master
            (integerp N) (< 0 N)
            ; each level has the same length
            (uniform_listp MREQ)
            ; the last owner has a valid number
            (integerp Last_Granted) (<= 0 Last_Granted)
            (< (+ 1 Last_granted) N)
            ; at least one request
            (not (no_requestp_matrix MREQ))
            (consp MREQ) (consp (cdr MREQ))
            ; each level is a line of bits
            (list_of_1_and_0 (nth (stage_P MREQ) MREQ))
            ; at least one slave unit
            (integerp Card_S) (< 0 Card_S)
            ; L is a valid address
            (integerp L) (<= 0 L) (< L (* Card_S MEM_SIZE))
            ; the size of the slave memory is at least one
            (integerp MEM_SIZE) (< 0 MEM_SIZE)
            ; the slave is active
            (equal Slave_Number (floor L MEM_SIZE))
            )
           (and (equal (L-slave
                        (trans_M_to_S O L D N Card_S P Last_Granted MREQ
                             Slave_Number 'undef MEM_SIZE))
                       (mod L MEM_SIZE))
                (equal (D-slave
                        (trans_M_to_S O L D N Card_S P Last_Granted MREQ
                                      Slave_Number 'undef MEM_SIZE))
                       D)))
  :hints (("GOAL" ;:use (:instance decoder_nth_1 (ADDR L))
                  :in-theory (disable ;decoder_nth_1
                              floor floor-mod-elim nth))))

; Prove 5.05

; Validation of the read transmission

(defthm trans_M_to_S_read
  (implies  (and
            ; P is the number of priority level(s)
            (integerp P) (equal P (len MREQ))
            ; N is the length of each level
            (equal (len (car MREQ)) N)
            ; at least one master
            (integerp N) (< 0 N)
            ; each level has the same length
            (uniform_listp MREQ)
            ; the last owner has a valid number
            (integerp Last_Granted) (<= 0 Last_Granted)
            (< (+ 1 Last_granted) N)
            ; at least one request
            (not (no_requestp_matrix MREQ))
            (consp MREQ) (consp (cdr MREQ))
            ; each level is a line of bits
            (list_of_1_and_0 (nth (stage_P MREQ) MREQ))
            ; at least one slave unit
            (integerp Card_S) (< 0 Card_S)
            ; L is a valid address
            (integerp L) (<= 0 L) (< L (* Card_S MEM_SIZE))
            ; the size of the slave memory is at least one
            (integerp MEM_SIZE) (< 0 MEM_SIZE)
            ; the slave is active
            (equal Slave_Number (floor L MEM_SIZE))
            ; the operation is 'read
            ;(equal O 'read)
            )
            (equal (O-slave
                    (trans_M_to_S 'read L D N Card_S P Last_Granted MREQ
                                      Slave_Number 'undef MEM_SIZE))
                   'read)))

; Prove 0.65

; validation of the write transmission

(defthm trans_M_to_S_write
  (implies  (and
            ; P is the number of priority level(s)
            (integerp P) (equal P (len MREQ))
            ; N is the length of each level
            (equal (len (car MREQ)) N)
            ; at least one master
            (integerp N) (< 0 N)
            ; each level has the same length
            (uniform_listp MREQ)
            ; the last owner has a valid number
            (integerp Last_Granted) (<= 0 Last_Granted)
            (< (+ 1 Last_granted) N)
            ; at least one request
            (not (no_requestp_matrix MREQ))
            (consp MREQ) (consp (cdr MREQ))
            ; each level is a line of bits
            (list_of_1_and_0 (nth (stage_P MREQ) MREQ))
            ; at least one slave unit
            (integerp Card_S) (< 0 Card_S)
            ; L is a valid address
            (integerp L) (<= 0 L) (< L (* Card_S MEM_SIZE))
            ; the size of the slave memory is at least one
            (integerp MEM_SIZE) (< 0 MEM_SIZE)
            ; the slave is active
            (equal Slave_Number (floor L MEM_SIZE))
            ; the operation is 'write
            ;(equal O 'write)
            )
            (equal (O-slave
                    (trans_M_to_S 'write L D N Card_S P Last_Granted MREQ
                                      Slave_Number 'undef MEM_SIZE))
                   'write)))

; Prove 0.63

(defthm trans_S_to_M_thm
  (implies (and
            ; P is the number of priority level(s)
            (integerp P) (equal P (len MREQ))
            ; N is the length of each level
            (equal (len (car MREQ)) N)
            ; at least one master
            (integerp N) (< 0 N)
            ; each level has the same length
            (uniform_listp MREQ)
            ; the last owner has a valid number
            (integerp Last_Granted) (<= 0 Last_Granted)
            (< (+ 1 Last_granted) N)
            ; at least one request
            (not (no_requestp_matrix MREQ))
            (consp MREQ) (consp (cdr MREQ))
            ; each level is a line of bits
            (list_of_1_and_0 (nth (stage_P MREQ) MREQ))
            ; at least one slave unit
            (integerp Card_S) (< 0 Card_S)
            ; L is a valid address
            (integerp L) (<= 0 L) (< L (* Card_S MEM_SIZE))
            ; the size of the slave memory is at least one
            (integerp MEM_SIZE) (< 0 MEM_SIZE)
            ; the slave is active
            (equal Slave_Number (floor L MEM_SIZE))
            )
           (equal (D-master
                   (trans_S_to_M O L D SD MEM_SIZE Card_S MREQ N P HWRITE HADDR
                                 HWDATA Slave_Number Last_Granted))
                  SD)))
; Prove 4.48


(in-theory (disable trans_S_to_M trans_M_to_S))

; to get a complete transfer a slave application is needed
; we define a small memory

(defun slave_memory (MEMO O UNADDR D)
  (cond ((equal O 'write)
         (list (put-nth UNADDR D MEMO) D))
        ((equal O 'read)
         (list MEMO (nth UNADDR MEMO)))))


(defun single_transfer (O L D N P Card_S Last_Granted MREQ Slave_Number
                        MEM_SIZE MEMO)
  (list
   (trans_S_to_M O L D
                 (nth 1
                      (slave_memory MEMO
                        (O-slave
                         (trans_M_to_S O L D N Card_S P Last_Granted
                                       MREQ Slave_Number 'undef MEM_SIZE))
                        (L-slave
                         (trans_M_to_S O L D N Card_S P Last_Granted
                                       MREQ Slave_Number 'undef MEM_SIZE))
                        (D-slave
                         (trans_M_to_S O L D N Card_S P Last_Granted
                                       MREQ Slave_Number 'undef  MEM_SIZE))))
                 MEM_SIZE Card_S MREQ N P O L D
                 Slave_Number Last_Granted)
   (nth 0
        (slave_memory MEMO
                      (O-slave
                         (trans_M_to_S O L D N Card_S P Last_Granted
                                       MREQ Slave_Number 'undef MEM_SIZE))
                      (L-slave
                       (trans_M_to_S O L D N Card_S P Last_Granted
                                       MREQ Slave_Number 'undef MEM_SIZE))
                      (D-slave
                       (trans_M_to_S O L D N Card_S P Last_Granted
                                       MREQ Slave_Number 'undef MEM_SIZE))))))

; returns a true-list
; a read example
;ACL2 !>(single_transfer 'Read 2 23 2 2 2 0 '((1 0) (1 0) (0 0)) 0 4 '(0 0 33 0 0 0 0 0))
;(((0 0 0) (33)) (0 0 33 0 0 0 0 0))
; a write example
;ACL2 !>(single_transfer 'Write 2 23 2 2 2 0 '((1 0) (1 0) (0 0)) 0 4 '(0 0 33 0 0 0 0 0))
;(((0 0 0) (23)) (0 0 23 0 0 0 0 0))

; the read data by the master is the (nth (mod L MEM_SIZE) MEMO)

(defthm single_read_transfer
  (implies (and
            ; P is the number of priority level(s)
            (integerp P) (equal P (len MREQ))
            ; N is the length of each level
            (equal (len (car MREQ)) N)
            ; at least one master
            (integerp N) (< 0 N)
            ; each level has the same length
            (uniform_listp MREQ)
            ; the last owner has a valid number
            (integerp Last_Granted) (<= 0 Last_Granted)
            (< (+ 1 Last_granted) N)
            ; at least one request
            (not (no_requestp_matrix MREQ))
            (consp MREQ) (consp (cdr MREQ))
            ; each level is a line of bits
            (list_of_1_and_0 (nth (stage_P MREQ) MREQ))
            ; at least one slave unit
            (integerp Card_S) (< 0 Card_S)
            ; L is a valid address
            (integerp L) (<= 0 L) (< L (* Card_S MEM_SIZE))
            ; the size of the slave memory is at least one
            (integerp MEM_SIZE) (< 0 MEM_SIZE)
            ; the slave is active
            (equal Slave_Number (floor L MEM_SIZE))
            ; the operation is 'read
            (equal O 'read)
            )
           (equal (D-Master
                   (nth 0
                        (single_transfer O L D N P Card_S Last_Granted MREQ
                                Slave_Number MEM_SIZE MEMO)))
                  (nth (mod L MEM_SIZE) MEMO)))
  :hints (("GOAL" :use trans_M_to_S_read
                  :do-not-induct t
                  :in-theory (disable D-master O-slave L-slave D-slave mod
                                      trans_M_to_S floor-mod-elim len))))

; Prove 5.25

; a write transfer is a (put-nth (mod ADDR MEM_SIZE) DATA MEMO)

(defthm single_write_transfer
  (implies (and
            ; P is the number of priority level(s)
            (integerp P) (equal P (len MREQ))
            ; N is the length of each level
            (equal (len (car MREQ)) N)
            ; at least one master
            (integerp N) (< 0 N)
            ; each level has the same length
            (uniform_listp MREQ)
            ; the last owner has a valid number
            (integerp Last_Granted) (<= 0 Last_Granted)
            (< (+ 1 Last_granted) N)
            ; at least one request
            (not (no_requestp_matrix MREQ))
            (consp MREQ) (consp (cdr MREQ))
            ; each level is a line of bits
            (list_of_1_and_0 (nth (stage_P MREQ) MREQ))
            ; at least one slave unit
            (integerp Card_S) (< 0 Card_S)
            ; L is a valid address
            (integerp L) (<= 0 L) (< L (* Card_S MEM_SIZE))
            ; the size of the slave memory is at least one
            (integerp MEM_SIZE) (< 0 MEM_SIZE)
            ; the slave is active
            (equal Slave_Number (floor L MEM_SIZE))
            ; the operation is 'read
            (equal O 'write)
            ; mem_size is the size of memo
            (equal (len MEMO) MEM_SIZE)
            )
           (equal (nth (mod L MEM_SIZE)
                       (nth 1 (single_transfer O L D N P Card_S Last_Granted MREQ
                                Slave_Number MEM_SIZE MEMO)))
                  D))
  :hints (("GOAL" :use trans_M_to_S_write
                  :do-not-induct t
                  :in-theory (disable D-master O-slave L-slave D-slave mod
                                      floor-mod-elim len nth trans_M_to_S_write))))
; Prove 6.70

