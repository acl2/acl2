#|$ACL2s-Preamble$;
;; Julien Schmaltz
;; Modified and updated by Amr HELMY 14th august 2007
;; Definition of the data-types used in GeNoC:
;; Transactions, missives, travels, results and attempts
;; June 20th 2005
;; File: GeNoC-types.lisp

;;Amr helmy
;;31st october 2007

;; Rev. January 31st by JS (mainly state related functions)
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

;; book paths on my laptop
(include-book "data-structures/list-defuns"  :dir :system)
(include-book "data-structures/list-defthms"  :dir :system)
;(include-book "textbook/chap11/qsort"  :dir :system)

;;----------------------------------------------|
;;                                              |
;;                TRANSACTIONS                  |
;;                                              |
;;----------------------------------------------|
;; A transaction is a tuple t = (id A msg B  flits time)
;; Accessors are IdT, OrgT, MsgT, destT, FlitT, TimeT
;; TimeT represent the departure time of the flit

(defun Idt (trans) (car trans))
(defun OrgT (trans) (nth 1 trans))
(defun MsgT (trans) (nth 2 trans))
(defun DestT (trans) (nth 3 trans))
(defun FlitT (trans) (nth 4 trans))
(defun TimeT (trans) (nth 5 trans))


(defun T-ids (Transts)
  ;; function that grabs the ids of a list of trans.
  (if (endp Transts)
      nil
    (append (list (caar Transts)) (T-ids (cdr Transts)))))

(defun T-msgs (Trs)
  ;; function that grabs the messages of a list of trans.
  (if (endp Trs)
      nil
    (cons (MsgT (car trs))
          (T-msgs (cdr Trs)))))

(defun T-orgs (Trs)
  ;; function that grabs the origins of a list of trans
  (if (endp Trs)
      nil
    (cons (OrgT (car trs))
          (T-orgs (cdr Trs)))))

(defun T-dests (Trs)
  ;; function that grabs the destinations of a list of trans
  (if (endp Trs)
      nil
    (cons (DestT (car trs))
          (T-dests (cdr Trs)))))

;; The following predicate checks that each transaction has
;; the right number of arguments
(defun validfield-transactionp (trans)
  ;; trans = (id A msg B flits time)
  (and (consp trans)
       (consp (cdr trans))         ;; (A msg B flits Time)
       (consp (cddr trans))        ;; (msg B flits Time)
       (consp (cdddr trans))       ;; (B flits Time)
       (consp (cddddr trans))                ;; (Flits Time)
       (consp (cdr (cddddr trans)))  ;(Time)
       (null (cddr (cddddr trans))))) ;;nil


;; The following predicate recognizes a valid list of transactions
(defun Validfields-T (Transts)
  (if (endp Transts)
      t
    (let ((trans (car Transts)))
      (and (validfield-transactionp trans)
           (natp (Idt trans))                       ;; id is a natural
           (MsgT trans)                             ;; msg /= nil
           (Natp (FlitT trans))
           (<= 1 (FlitT trans))
           (natp (timeT trans))
           (not (equal (OrgT trans) (DestT trans))) ;; A /= B
           (Validfields-T (cdr Transts))))))

;; now we define the predicate that recognizes a valid list of
;; transactions
(defun Transactionsp (Transts NodeSet)
  (let ((T-ids (T-ids Transts)))
    (and (Validfields-T Transts)
         (true-listp Transts)
         (subsetp (T-orgs Transts) NodeSet)
         ;; the origins are members of the nodeset
         (subsetp (T-dests Transts) NodeSet)
         ;; the destinations are members of the nodeset
         (No-Duplicatesp T-ids))))

;;------------------ end of Transactions ----------------------------------


;;-----------------------------------------------|
;;                                               |
;;                         MISSIVES              |
;;                                               |
;;-----------------------------------------------|


;; A missive is a tuple m = (id A frm B Flit Time)
;; Accessors are IdM, OrgM, FrmM and DestM

(defun IdM (m) (car m))
(defun OrgM (m) (nth 1 m))
(defun FrmM (m) (nth 2 m))
(defun DestM (m) (nth 3 m))
(defun FlitM (m) (nth 4 m))
(defun TimeM (m) (nth 5 m))
;;;(defun LocM (m) (nth 6 m))


;; We need a function that grabs the ids of a list of missives
(defun M-ids (M)
  (if (endp M)
      nil
    (append (list (caar M)) (M-ids (cdr M)))))

;; We need a function that grabs the origins of Missives
(defun M-orgs (M)
  (if (endp M)
      nil
    (append (list (OrgM (car M))) (M-orgs (cdr M)))))

;; The same for the destinations
(defun M-dests (M)
  (if (endp M)
      nil
    (append (list (DestM (car M))) (M-dests (cdr M)))))

;; We also need a function that grabs the frames of a list of missives
(defun M-frms (M)
  (if (endp M)
      nil
    (let* ((msv (car M))
           (m-frm (FrmM msv)))
      (append (list m-frm) (M-frms (cdr M))))))


;; The following predicate checks that each missive has
;; the right number of arguments
(defun validfield-missivep (m)
  ;; m = (id A frm B)
  (and (consp m)
       (consp (cdr m))           ;; (A frm B flits time)
       (consp (cddr m))          ;; (frm B flits time)
       (consp (cdddr m))         ;; (B flits time)
       (consp (cddddr m))        ;; (Flits Time)
       (consp (cdr (cddddr  m))) ;; (time)
;;;       (consp (cddr (cddddr m))) ;; loc
       (null  (cddr  (cddddr  m))))) ;;nil

;; The following predicate recognizes a valid list of missives (partially)
(defun Validfields-M (M)
  (if (endp M)
      t
    (let ((msv (car M)))
      (and (validfield-missivep msv)
           (natp (IdM msv))                     ;; id is a natural
           (FrmM msv)                           ;; frm /= nil
           (natp (FlitM msv))
           (>= (FlitM msv) 1)
           (natp (TimeM msv))
           (not (equal (OrgM msv) (DestM msv))) ;; A /= B
;;;           (Validfield-loc (LocM msv) (FlitM msv) nodeset)
           (Validfields-M (cdr M))))))

;; now we define the predicate that recognizes a valid list of
;; missives
(defun Missivesp (M NodeSet)
  (let ((M-ids (M-ids M)))
    (and (Validfields-M M)
         (subsetp (M-orgs M) NodeSet)    ;;origins subset of nodeset
         (subsetp (M-dests M) NodeSet)         ;;destinations subset of nodeset
         (true-listp M)
         (No-Duplicatesp M-ids))))

;;-------------------- end of Missives -------------------------------------


;;------------------------------------------|
;;                                          |
;;           TRAVELING MISSIVES             |
;;                                          |
;;------------------------------------------|


;; A traveling missive is a tuple m = (id A current frm B Flit time)
;; Accessors are IdTM, OrgTM, curTM, FrmTM and DestTM flitm

(defun IdTM (m) (car m))
(defun OrgTM (m) (nth 1 m))
(defun CurTM (m) (nth 2 m))
(defun FrmTM (m) (nth 3 m))
(defun DestTM (m) (nth 4 m))
(defun FlitTM (m) (nth 5 m))
(defun TimeTM (m) (nth 6 m))
(defun LocTM (m) (nth 7 m))

;; We need a function that grabs the ids of a list of missives
(defun TM-ids (M)
  (if (endp M)
      nil
    (append (list (IdTM (car M))) (TM-ids (cdr M)))))

;; We need a function that grabs the origins of Missives
(defun TM-orgs (M)
  (if (endp M)
      nil
    (append (list (OrgTM (car M))) (TM-orgs (cdr M)))))

;; The same for the currents
(defun TM-curs (M)
  (if (endp M)
      nil
    (append (list (CurTM (car M))) (TM-curs (cdr M)))))

;; The same for the destinations
(defun TM-dests (M)
  (if (endp M)
      nil
    (append (list (DestTM (car M))) (TM-dests (cdr M)))))

;; We also need a function that grabs the frames of a list of missives
(defun TM-frms (M)
  ;; grabs the frames of M
  (if (endp M)
      nil
    (let* ((msv (car M))
           (m-frm (FrmTM msv)))
      (append (list m-frm) (TM-frms (cdr M))))))


;; The following predicate checks that each missive has
;; the right number of arguments
(defun validfield-Tmissivep (m)
  ;; m = (id A current frm B)
  (and (consp m)
       (consp (cdr m))            ;; (A current frm B flits time loc)
       (consp (cddr m))           ;; (current frm B flits time loc)
       (consp (cdddr m))          ;; (frm B flits time loc)
       (consp (cddddr m))         ;; (B flits time loc)
       (consp (cdr (cddddr  m)))  ;; (flits Time lco)
       (consp (cddr (cddddr m)))  ;;(time loc)
       (consp (cdddr (cddddr m))) ;; loc
       (null (cddddr (cddddr m))) ;; nil
       ))

;; loc is a valid field iff
;; it is a list with for each flit
;; a node. This node is the current location
;; of the flit.
;; The car of loc denotes the location of the header flit,
;; the cadr of loc dentoes the location of flit 1, etc.
(defun validfield-loc (loc flits nodeset)
  (and (subsetp loc nodeset)
       (true-listp loc)
       (equal (len loc) flits)))


;; The following predicate recognizes a valid list of missives (partially)
(defun Validfields-TM (M nodeset)
  (if (endp M)
      t
    (let ((msv (car M)))
      (and (validfield-Tmissivep msv)
           (natp (IdTM msv))                      ;; id is a natural
           (FrmTM msv)                            ;; frm /= nil
           (Natp (FlitTM msv))
           (natp (TimeTM msv))
           (>= (FlitTM msv) 1)
           ;(member-equal (OrgTM msv) nodeset)
           ;(member-equal (DestTM msv) nodeset)
           (not (equal (OrgTM msv) (DestTM msv))) ;; A /= B
           (not (equal (CurTM msv) (DestTM msv))) ;; current /= B
           (equal (CurTM msv) (car (LocTM msv)))  ;; current destination equals location of header flit
           (ValidField-Loc (LocTM msv) (FlitTM msv) nodeset)
           (Validfields-TM (cdr M) nodeset)))))

;; now we define the predicate that recognizes a valid list of
;; missives
(defun TMissivesp (M NodeSet)
  (let ((M-ids (TM-ids M)))
    (and (Validfields-TM M Nodeset)
         (subsetp (TM-orgs M) NodeSet)                ;;origines subset nodeset
         (subsetp (TM-curs M) NodeSet)                ;;current subset nodeset
         (subsetp (TM-dests M) NodeSet)                ;;destination subset nodeset
         (true-listp M)
         (No-Duplicatesp M-ids))))

;;-------------------- end of Traveling Missives -------------------------


;;------------------------------------------------|
;;                                                |
;;                   TRAVELS                      |
;;                                                |
;;------------------------------------------------|

;; On ajoute l'origine, car elle va pouvoir ne plus apparaitre dans Routes...

;; A travel is a tuple tr = (id org frm Routes flits time)
;; Accessors are IdV, OrgV, FrmV, RoutesV and FlitsV
;; (JS: V comes from the french word for travel, voyage :-)

(defun IdV (tr) (car tr))
(defun OrgV (m) (nth 1 m))
(defun FrmV (tr) (nth 2 tr))
(defun CurV (tr) (nth 3 tr))
(defun NextHopsV (tr) (nth 4 tr))
(defun DestV (tr) (nth 5 tr))
(defun FlitV (tr) (nth 6 tr))
(defun TimeV (tr) (nth 7 tr))
(defun LocV (tr) (nth 8 tr))


;; We need a function that grabs the ids of a list of travels
(defun V-ids (TrLst)
  (if (endp TrLst)
      nil
    (append (list (caar TrLst)) (V-ids (cdr TrLst)))))

;; We need a function that grabs the orgs of a list of travels
(defun V-orgs (TrLst)
  (if (endp TrLst)
      nil
    (append (list (OrgV (car TrLst))) (V-orgs (cdr TrLst)))))


;; The following predicate checks that each travel has
;; the right number of arguments
(defun validfield-travelp (tr nodeset)
  ;; tr = (id org frm Routes flits time)
  (and (consp tr)
       (consp (cdr tr))
       (consp (cddr tr))
       (consp (cdddr tr))
       (consp (cddddr tr))
       (consp (cdr (cddddr tr)))
       (consp (cddr (cddddr tr)))
       (consp (cdddr (cddddr tr)))
       (consp (cddddr (cddddr tr)))
       (null (cdr (cddddr (cddddr tr))))
       (member-equal (orgv tr) nodeset)
       (consp (NextHopsV tr))
       (subsetp (NextHopsV tr) nodeset)
       ;(equal (caar (RoutesV tr)) (car (LocV tr))) ;; routing must begin in location of header flit
;       (A-car= (RoutesV tr) (car (LocV tr)))
       (validfield-loc (locv tr) (flitv tr) nodeset)))#|ACL2s-ToDo-Line|#

;       (validfield-route (routesv tr) (orgv tr) (caar (RoutesV tr)) (car (last (car (RoutesV tr)))) nodeset)))

;; The following predicate recognizes a valid list of missives (partially)
(defun Validfields-TrLst (TrLst nodeset)
  (if (endp TrLst)
      t
    (let ((tr (car TrLst)))
      (and (validfield-travelp tr nodeset)
           (natp (IdV tr))                     ;; id is a natural
           (FrmV tr)                           ;; frm /= nil
           (natp (FlitV tr))
           (>= (FlitV tr) 1)
           (natp (TimeV tr))
           (true-listp (NextHopsV tr))
           (member-equal (CurV tr) nodeset)
           (member-equal (DestV tr) nodeset)
           (equal (car (LocV tr)) (CurV tr))
           (not (equal (CurV tr) (DestV tr)))
           (not (equal (OrgV tr) (DestV tr)))
           (Validfields-TrLst (cdr TrLst) nodeset)))))

;; now we define the predicate that recognizes a valid list of
;; travels
(defun TrLstp (TrLst nodeset)
  (let ((V-ids (V-ids TrLst)))
    (and (Validfields-TrLst TrLst nodeset)
         (true-listp TrLst)
         (No-Duplicatesp V-ids))))

(defun V-frms (TrLst)
  ;; grabs the frames of TrLst
  (if (endp TrLst)
      nil
    (let* ((tr (car Trlst))
           (v-frm (FrmV tr)))
      (append (list v-frm) (V-frms (cdr TrLst))))))

;;-------------------- end of Travels -------------------------------------


;;---------------------------------------------|
;;                                             |
;;                         RESULTS             |
;;                                             |
;;---------------------------------------------|

;; A result is a tuple rst = (Id Dest Msg flit Time)
;; Accessors are IdR, DestR and MsgR

(defun IdR (rst) (car rst))
(defun DestR (rst) (nth 1 rst))
(defun MsgR (rst) (nth 2 rst))
(defun FlitR (rst) (nth 3 rst))
(defun TimeR (rst) (nth 4 rst))

(defun R-ids (R)
  ;; function that grabs the ids of a list of results
  (if (endp R)
      nil
    (append (list (caar R)) (R-ids (cdr R)))))

(defun R-dests (Results)
  ;; function that grabs the destinations of a list of results
  (if (endp Results)
      nil
    (cons (DestR (car Results))
          (R-dests (cdr Results)))))

(defun R-msgs (Results)
  ;; function that grabs the messages of a list of results
  (if (endp Results)
      nil
    (cons (MsgR (car results))
          (R-msgs (cdr Results)))))


;; The following predicate checks that each result has
;; the right number of arguments
(defun validfield-resultp (rst)
  ;; tr = (Id Dest Msg)
  (and (consp rst)
       (consp (cdr rst))         ;; (Dest Msg Flit time)
       (consp (cddr rst))        ;; (Msg Flit time)
       (consp (cdddr rst))                 ;; (flit time)
       (consp (cddddr rst))                 ;;(time)
       (null (cdr(cddddr rst)))));; nil


;; The following predicate recognizes a valid list of results (partially)
(defun Validfields-R (R NodeSet)
  (if (endp R)
      t
    (let ((rst (car R)))
      (and (validfield-resultp rst)
           (natp (IdR rst))                     ;; id is a natural
           (MsgR rst)                           ;; msg /= nil
           (Natp (FlitR rst))
           (natp (TimeR rst))
           (member (DestR rst) NodeSet)
           (Validfields-R (cdr R) NodeSet)))))

;; now we define the predicate that recognizes a valid list of
;; results
(defun Resultsp (R NodeSet)
  (let ((R-ids (R-ids R)))
    (and (Validfields-R R NodeSet)
         (true-listp R)
         (No-Duplicatesp R-ids))))

;;-------------------- end of Results -------------------------------------

;;-----------------------------------------------|
;;                                               |
;;                         STATE                 |
;;                                               |
;;-----------------------------------------------|

;; a state is a list of the form ( (coor (node_id)) (buffers ...)) where
;; node_id a an element of NodeSet
;; we define accessors and predicates defining valid state entries

;; we need accessors to the state elements
(defun get_coor (st_entry)
  ;; st_entry =  ( (coor (id)) (buffers ...))
  ;; this function returns id
  (cadar st_entry))


(defun get_buff (st_entry)
  ;; st_entry =  ( (coor (id)) (buffers ...))
  ;; this function returns ...
  (cadadr st_entry))


(defun getcoordinates (ntkstate)
  (if (endp ntkstate)
      nil
    (cons (get_coor (car ntkstate))
          (getcoordinates (cdr ntkstate)))))

(defun get-buffers (ntkstate)
  (if (endp ntkstate)
      nil
    (cons (get_buff (car ntkstate))
          (get-buffers (cdr ntkstate)))))


(defun validCoord (x)
  ;; x is (coor (id))
  (and (equal (car x) 'Coor)
       (consp x)
       (consp (cdr x))
       (null (cddr x))))

(defun ValidBuffer (x)
  ;; x is (buffers ...)
  (and (equal (car x) 'Buffers)
       (consp x)
       (consp (cdr x))))

(defun ValidCoordlist (x)
  ;; x is a state = ( ((coor (id)) (buffers ...)) ...)
  (if (endp x)
      t
    (and (Validcoord (caar x))
         (Validcoordlist (cdr x)))))

(defun ValidbuffersList (x)
  ;; x is a state = ( ((coor (id)) (buffers ...)) ...)
  (if (endp x)
      t
    (and (ValidBuffer (cadar x))
         (Validbufferslist (cdr x)))))

;; NOTE: nil is a valid state, so nil is also a valid state element

(defun validstate-entryp (st_entry)
  (if (endp st_entry)
      t
    (and (Validcoord (car st_entry))
         (Validbuffer (cadr st_entry)))))


(defun ValidState (ntkstate)
  (if (endp ntkstate)
      t
    (and ;(consp ntkstate)
     (Validstate-entryp (car ntkstate))
     (Validstate (cdr ntkstate)))))
