;; Julien Schmaltz
;; Definition of the data-types used in GeNoC:
;; Transactions, missives, travels, results and attempts
;; June 20th 2005
;; File: GeNoC-types.lisp
;; rev. July 14th 2007
;; js: adding guards

(in-package "ACL2")

;; book paths on my laptop
(include-book "data-structures/list-defuns" :dir :system)
(include-book "data-structures/list-defthms" :dir :system)
(include-book "textbook/chap11/qsort" :dir :system)

;;--------------------------------------------------------------------------
;;
;;                         TRANSACTIONS
;;
;;--------------------------------------------------------------------------
;; A transaction is a tuple t = (id A msg B)
;; Accessors are IdT, OrgT, MsgT and DestT
(defun Idt (trans)   (car trans))
(defun OrgT (trans)  (nth 1 trans))
(defun MsgT (trans)  (nth 2 trans))
(defun DestT (trans) (nth 3 trans))

(defun T-ids (Transts)
  ;; function that grabs the ids of a list of trans.
  (if (endp Transts)
      nil
    (append (list (caar Transts)) (T-ids (cdr Transts)))))

(defun T-dests (Trs)
  ;; function that grabs the destinatiions of a list of trans.
  (if (endp Trs)
      nil
    (cons (DestT (car trs))
          (T-dests (cdr Trs)))))

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

;; The following predicate checks that each transaction has
;; the right number of arguments
(defun validfield-transactionp (trans)
  ;; trans = (id A msg B)
  (and (consp trans)
       (consp (cdr trans))         ;; (A msg B)
       (consp (cddr trans))        ;; (msg B)
       (consp (cdddr trans))        ;; (B)
       (null (cddddr trans))))


;; The following predicate recognizes a valid list of transactions
(defun Validfields-T (Transts)
  (if (endp Transts)
      t
    (let ((trans (car Transts)))
      (and (validfield-transactionp trans)
           (natp (Idt trans))                       ;; id is a natural
           (MsgT trans)                             ;; msg /= nil
	   (eqlablep (OrgT trans))                  ;; needed to prove guard of Transactionsp
	   (eqlablep (DestT trans))
           (not (equal (OrgT trans) (DestT trans))) ;; A /= B
           (Validfields-T (cdr Transts))))))


;; now we define the predicate that recognizes a valid list of
;; transactions
(defun Transactionsp (Transts NodeSet)
  (let ((T-ids (T-ids Transts)))
    (and (Validfields-T Transts)
         (true-listp Transts)
         (subsetp (T-orgs Transts) NodeSet)
         (subsetp (T-dests Transts) NodeSet)
         (No-Duplicatesp T-ids))))
;;------------------ end of Transactions ----------------------------------

;;--------------------------------------------------------------------------
;;
;;                         MISSIVES
;;
;;--------------------------------------------------------------------------


;; A missive is a tuple m = (id A frm B)
;; Accessors are IdM, OrgM, FrmM and DestM
(defun IdM (m)   (car m))
(defun OrgM (m)  (nth 1 m))
(defun FrmM (m)  (nth 2 m))
(defun DestM (m) (nth 3 m))

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

;; We also need a function that grabs the frames of
;; a list of missives
(defun M-frms (M)
  ;; grabs the frames of M
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
       (consp (cdr m))         ;; (A frm B)
       (consp (cddr m))        ;; (frm B)
       (consp (cdddr m))        ;; (B)
       (null (cddddr m))))

;; The following predicate recognizes a valid list of missives (partially)
(defun Validfields-M (M)
  (if (endp M)
      t
    (let ((msv (car M)))
      (and (validfield-missivep msv)
           (natp (IdM msv))                     ;; id is a natural
           (FrmM msv)                           ;; frm /= nil
           (not (equal (OrgM msv) (DestM msv))) ;; A /= B
           (Validfields-M (cdr M))))))

;; now we define the predicate that recognizes a valid list of
;; transactions
(defun Missivesp (M NodeSet)
  (let ((M-ids (M-ids M)))
    (and (Validfields-M M)
         (subsetp (M-orgs M) NodeSet)
         (subsetp (M-dests M) NodeSet)
         (true-listp M)
         (No-Duplicatesp M-ids))))
;;-------------------- end of Missives -------------------------------------

;;--------------------------------------------------------------------------
;;
;;                         TRAVELS
;;
;;--------------------------------------------------------------------------

;; A travel is a tuple tr = (id frm Routes)
;; Accessors are IdV, FrmV and RoutesV
;; (JS: V comes from the french word for travel, voyage :-)
(defun IdV (tr) (car tr))
(defun FrmV (tr) (nth 1 tr))
(defun RoutesV (tr) (nth 2 tr))

;; We need a function that grabs the ids of a list of travels
(defun V-ids (TrLst)
  (if (endp TrLst)
      nil
    (append (list (caar TrLst)) (V-ids (cdr TrLst)))))

;; The following predicate checks that each route of routes
;; has at least two elements
(defun validfield-route (routes)
  ;; checks that every route has at least two elements
  (if (endp routes)
      t
    (let ((r (car routes)))
      (and (consp r)
           (consp (cdr r))
           (validfield-route (cdr routes))))))

;; The following predicate checks that each travel has
;; the right number of arguments
(defun validfield-travelp (tr)
  ;; tr = (id frm Routes)
  (and (consp tr)
       (consp (cdr tr))         ;; (frm Routes)
       (consp (cddr tr))        ;; (Routes) = ( ((R1) (R2) ...))
       (consp (caddr tr))       ;; ((R1) (R2) ...)
       (validfield-route (caddr tr))
       (null (cdddr tr))))

;; The following predicate recognizes a valid list of missives (partially)
(defun Validfields-TrLst (TrLst)
  (if (endp TrLst)
      t
    (let ((tr (car TrLst)))
      (and (validfield-travelp tr)
           (natp (IdV tr))                     ;; id is a natural
           (FrmV tr)                           ;; frm /= nil
           (true-listp (RoutesV tr))
           (Validfields-TrLst (cdr TrLst))))))

;; now we define the predicate that recognizes a valid list of
;; transactions
(defun TrLstp (TrLst )
  (let ((V-ids (V-ids TrLst)))
    (and (Validfields-TrLst TrLst)
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

;;--------------------------------------------------------------------------
;;
;;                         RESULTS
;;
;;--------------------------------------------------------------------------

;; A result is a tuple rst = (Id Dest Msg)
;; Accessors are IdR, DestR and MsgR
(defun IdR (rst) (car rst))
(defun DestR (rst) (nth 1 rst))
(defun MsgR (rst) (nth 2 rst))

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
       (consp (cdr rst))         ;; (Dest Msg)
       (consp (cddr rst))        ;; (Msg)
       (null (cdddr rst))))

;; The following predicate recognizes a valid list of results (partially)
(defun Validfields-R (R NodeSet)
  (if (endp R)
      t
    (let ((rst (car R)))
      (and (validfield-resultp rst)
           (natp (IdR rst))                     ;; id is a natural
           (MsgR rst)                           ;; msg /= nil
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

;;--------------------------------------------------------------------------
;;
;;                         ATTEMPTS
;;
;;--------------------------------------------------------------------------

;; we just need to define the sum of the attempts
(defun SumOfAttempts (att)
  ;; this is the measure for sigma-t
  ;; att has the following form:
  ;; ( ... (i RemAtt) ...)
  (if (endp att)
      0
    (let* ((top (car att))
	   (rem-att (cadr top)))
      (+ (nfix rem-att)
         (SumOfAttempts (cdr att))))))

;;-------------------- end of Attempts -------------------------------------
