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
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2")

;; book paths on my laptop
(include-book "data-structures/list-defuns"  :dir :system)
(include-book "data-structures/list-defthms"  :dir :system)
(include-book "data-structures/structures" :dir :system)
(include-book "macro")

(defthm nth-remove
  (implies (and ;(syntaxp (rationalp n))
                (< 0 n)
                (natp n))
           (equal (nth n x)
                  (nth (1- n) (cdr x)))))

;;-----------------------------------------------|
;;                                               |
;;                         MISSIVES              |
;;                                               |
;;-----------------------------------------------|
;;
;; The main inputs of function GeNoC are a list of
;; uninjected missives and a list of enroute missives.
;; A missive represents a message together with meta
;; information about it.
;;
;; A missive is a tuple m = (id A frm B Flit Time)
;; id: a unique id
;; A: the origin of the message
;; frm: the actual payload/content of the message
;; B: the destination of the message
;; Flit: the number of flits in the message
;; Time: the desired injection time
;;
;; Here is the list of functions related to
;; missives.
;;
;; ------------------------------------------------|
;; IdM, OrgM, FrmM and DestM    |       accessors  |
;; FlitM, TimeM                 |                  |
;; M-ids                        | all id  in M     |
;; M-orgs                       | all org in M     |
;; M-dests                      | all dest in M    |
;; M-frms                       | all frm in M     |
;; Missivesp                    | recognizer for M |
;; ------------------------------------------------|
(defstructure M _id org frame flit time
  (:options (:representation :list)
   ;(:do-not :tag)
   (:assert (and (natp _id)                    ;; id is a natural
                ;frame                           ;; frm /= nil
                (natp flit)
                (>= flit 1)
                (natp time)))))
;(defmacro IdM (m)
;       `(M-id ,m))
(defmacro OrgM (m)
       `(M-org ,m))
(defmacro FrmM (m)
       `(M-frame ,m))
(defmacro FlitM (m)
       `(M-flit ,m))
(defmacro TimeM (m)
       `(M-time ,m))
(defmacro validfield-missivep (m)
       `(weak-M-p ,m))
#|
(defmacro Validfields-M (m)
       `(M-p ,m))
|#

;;------------------------------------------|
;;                                          |
;;           TRAVELING MISSIVES             |
;;                                          |
;;------------------------------------------|
;;
;; Traveling missives are missives which have been
;; injected in the network. They get two additional
;; fields: their current position of the header in
;; the network and the location of all their flits.
;;
;; A traveling missive is a tuple
;; tm = (id A current frm B Flit Time Loc)
;; current = current position of the header
;; Loc = current position of all the flits.
;;
;; Here is the list of functions related to
;; traveling missives.
;;
;; ------------------------------------------------|
;; IdTM, OrgTM, FrmTM, DestTM   |       accessors  |
;; LocTM, CurTM, FlitTM, TimeTM |                  |
;; TM-ids                       | all id  in TM    |
;; TM-orgs                      | all org in TM    |
;; TM-dests                     | all dest in TM   |
;; TM-frms                      | all frm in TM    |
;; TM-curs                      | all curr in TM   |
;; TMissivesp                   | recognizer of TM |
;; ------------------------------------------------|
(defstructure TM _id org cur frame flit time loc
  (:options (:representation :list)
   ;(:do-not :tag)
   ))
;(defmacro IdTM (m)
;       `(TM-id ,m))
(defmacro OrgTM (m)
       `(TM-org ,m))
(defmacro CurTM (m)
       `(TM-cur ,m))
(defmacro FrmTM (m)
       `(TM-frame ,m))
(defmacro FlitTM (m)
       `(TM-flit ,m))
(defmacro TimeTM (m)
       `(TM-time ,m))
(defmacro LocTM (m)
       `(TM-loc ,m))
(defmacro validfield-Tmissivep (m)
       `(weak-TM-p ,m))


;;------------------------------------------------|
;;                                                |
;;                   TRAVELS                      |
;;                                                |
;;------------------------------------------------|
;;
;; A travel is a traveling missive which has been
;; routed. that is, it has a new field containing
;; the possible next hops for the message.
;;
;; A travel is a tuple
;; tr = (id org frm curr NxtHops dest Flits Time Loc)
;; NxtHops: the possible next hops for the travel.
;;
;; Accessors are IdV, OrgV, FrmV, RoutesV and FlitsV
;; (JS: V comes from the french word for travel, voyage :-)
;;
;; Here is the list of functions related to
;; travels.
;;
;; ------------------------------------------------|
;; IdV, OrgV, FrmTM, DestV,CurV |       accessors  |
;; NextHopsV, FlitV,TimeV,LocV  |                  |
;; V-ids                       | all id  in V      |
;; V-orgs                      | all org in V      |
;; V-frms                      | all frm in V      |
;; TrLstp                      | recognizer of V   |
;; ------------------------------------------------|

(defstructure V id org cur frame nexthops flit time loc
  (:options (:representation :list)
   ;(:do-not :tag)
   ))
(defmacro IdV (m)
       `(V-id ,m))
(defmacro OrgV (m)
       `(V-org ,m))
(defmacro CurV (m)
       `(V-cur ,m))
(defmacro FrmV (m)
       `(V-frame ,m))
(defmacro NexthopsV (m)
       `(V-nexthops ,m))
(defmacro FlitV (m)
       `(V-flit ,m))
(defmacro TimeV (m)
       `(V-time ,m))
(defmacro LocV (m)
       `(V-loc ,m))

(defmacro TM-id (v)
  `(V-id ,v))
(defmacro M-id (v)
  `(V-id ,v))
(defmacro IdTM (m)
       `(V-id ,m))
(defmacro IdM (m)
       `(V-id ,m))


(defthm m-id-is-v-id
  (equal (m-_id x)
         (v-id x))
  :hints (("Goal" :in-theory (enable m-_id v-id))))

(defthm tm-id-is-v-id
  (equal (tm-_id x)
         (v-id x))
  :hints (("Goal" :in-theory (enable tm-_id v-id))))


(defthm remove-V-id
  (equal (V-id (TM id org cur frame flit time loc))
         id)
  :hints (("Goal" :in-theory (enable TM V-id))))

(defthm remove-V-id-alt
  (equal (V-id (M id org frame flit time))
         id)
  :hints (("Goal" :in-theory (enable M V-id))))

(create-map V-id :name V-ids)
(defmacro TM-ids (lst)
  `(V-ids ,lst))
(defmacro M-ids (lst)
  `(V-ids ,lst))

;;;; THEORIES

;; We need a function that grabs the ids of a list of missives

;; We need a function that grabs the origins of Missives
(create-map M-org :name M-orgs)
#|
;; The same for the destinations
(defun M-dests (M)
  (if (endp M)
      nil
    (cons (DestM (car M)) (M-dests (cdr M)))))
|#
;; We also need a function that grabs the frames of a list of missives
(create-map M-frame :name M-frms)

(create-for-all M-p :name Validfields-M)

;; now we define the predicate that recognizes a valid list of
;; missives
(defun Missivesp (M NodeSet)
  (let ((M-ids (M-ids M)))
    (and (Validfields-M M)
         (subsetp (M-orgs M) NodeSet)    ;;origins subset of nodeset
       ;  (subsetp (M-dests M) NodeSet)         ;;destinations subset of nodeset
         (true-listp M)
         (No-Duplicatesp M-ids))))



;;-------------------- end of Missives -------------------------------------




;; We need a function that grabs the ids of a list of missives
;(create-map V-id :name tm-ids)

;; We need a function that grabs the origins of Missives
(create-map tm-org :name tm-orgs)

;; The same for the currents
(create-map tm-cur :name tm-curs)

;; We also need a function that grabs the frames of a list of missives
(create-map tm-frame :name tm-frms)

;; loc is a valid field iff
;; it is a list with for each flit
;; a node. This node is the current location
;; of the flit.
;; The car of loc denotes the location of the header flit,
;; the cadr of loc dentoes the location of flit 1, etc.
(defmacro cars (x)
  `(strip-cars ,x))
#|
(defmacro cadrs (x)
  `(strip-cars (strip-cdrs ,x)))
|#
(defun cadrs (x)
  (if (endp x)
    nil
    (cons (cadar x) (cadrs (cdr x)))))

(create-for-all natp)

(defun len= (x n)
  (equal (len x) n))
(create-for-all len= :extra (n))

(defun filter-car=-test (x a)
  (equal (car x) a))

(create-filter filter-car=-test :extra (a) :name filter-car=-alt)
(defmacro filter-car= (a x)
  `(filter-car=-alt ,x ,a))

(defun per-resource-no-duplicate-flits (locs)
  (if (endp locs)
       t
       (and (no-duplicatesp-equal (cadrs (filter-car= (caar locs) locs)))
            (per-resource-no-duplicate-flits (cdr locs)))))
(defun validfield-loc (loc flits nodeset)
  (and (subsetp (cars loc) nodeset)
       (A-natp (cadrs loc))
       (A-len= loc 2)
       (true-listp loc)
       (per-resource-no-duplicate-flits loc)
       (equal (len loc) flits)))


(defun Validfields-TM-test (msv nodeset)
  (and (weak-TM-p msv)
       (natp (IdTM msv))                      ;; id is a natural
       ;(FrmTM msv)                            ;; frm /= nil
       (Natp (FlitTM msv))
       (natp (TimeTM msv))
       (>= (FlitTM msv) 1)
;(not (equal (OrgTM msv) (DestTM msv))) ;; A /= B
;(not (equal (CurTM msv) (DestTM msv))) ;; current /= B
       (equal (CurTM msv) (caar (LocTM msv)))  ;; current destination equals location of header flit
       (ValidField-Loc (LocTM msv) (FlitTM msv) nodeset)))

;; The following predicate recognizes a valid list of missives (partially)
(create-for-all Validfields-TM-test :name Validfields-TM :extra (nodeset))

;; now we define the predicate that recognizes a valid list of
;; missives
(defun TMissivesp (M NodeSet)
  (let ((M-ids (TM-ids M)))
    (and (Validfields-TM M Nodeset)
         (subsetp (TM-orgs M) NodeSet)                ;;origines subset nodeset
         (subsetp (TM-curs M) NodeSet)                ;;current subset nodeset
        ; (subsetp (TM-dests M) NodeSet)                ;;destination subset nodeset
         (true-listp M)
         (No-Duplicatesp M-ids))))

;;-------------------- end of Traveling Missives -------------------------


#|
(defthm V-p-implies-len
  (implies (weak-V-p v)
           (equal (len v) 9))
  :hints (("Goal" :in-theory (enable weak-V-p))))
|#
#|
(defmacro validfield-travelp (m)
       `(weak-V-p ,m))
|#
;; We need a function that grabs the ids of a list of travels

;; We need a function that grabs the orgs of a list of travels
(create-map V-org :name V-orgs)

;; The following predicate checks that each travel has
;; the right number of arguments
(defun validfield-travelp (tr nodeset)
  ;; tr = (id org frm Routes flits time)
  (and (weak-V-p tr)
       (member-equal (orgv tr) nodeset)
       (consp (NextHopsV tr))
       (subsetp (strip-cars (NextHopsV tr)) nodeset)
       ;(equal (caar (RoutesV tr)) (caar (LocV tr))) ;; routing must begin in location of header flit
;       (A-car= (RoutesV tr) (caar (LocV tr)))
       (validfield-loc (locv tr) (flitv tr) nodeset)))
;       (validfield-route (routesv tr) (orgv tr) (caar (RoutesV tr)) (car (last (car (RoutesV tr)))) nodeset)))

(defun Validfields-TrLst-test (Tr nodeset)
      (and (validfield-travelp tr nodeset)
           (natp (IdV tr))                     ;; id is a natural
           ;(FrmV tr)                           ;; frm /= nil
           (natp (FlitV tr))
           (>= (FlitV tr) 1)
           (natp (TimeV tr))
           (true-listp (NextHopsV tr))
           (member-equal (CurV tr) nodeset)
           ;(member-equal (DestV tr) nodeset)
           (equal (caar (LocV tr)) (CurV tr))
          ; (not (equal (CurV tr) (DestV tr)))
          ; (not (equal (OrgV tr) (DestV tr)))
           ))

;; The following predicate recognizes a valid list of missives (partially)
(create-for-all Validfields-TrLst-test :name Validfields-TrLst :extra (nodeset))


;; now we define the predicate that recognizes a valid list of
;; travels
(defun TrLstp (TrLst nodeset)
  (let ((V-ids (V-ids TrLst)))
    (and (Validfields-TrLst TrLst nodeset)
         (true-listp TrLst)
         (No-Duplicatesp V-ids))))

(create-map V-frame :name V-frms)

;;-------------------- end of Travels -------------------------------------

;;-----------------------------------------------|
;;                                               |
;;                         STATE                 |
;;                                               |
;;-----------------------------------------------|

;; a state is a list of the form ( (coor (node_id)) (buffers ...)) where
;; node_id a an element of NodeSet
;; we define accessors and predicates defining valid state entries

;; we need accessors to the state elements
(defun get_resource_from_rstate (rstate)
  ;; st_entry =  ( (coor (id)) (buffers ...))
  ;; this function returns id
  (cadar rstate))


(defun get_buffer_from_rstate (rstate)
  ;; st_entry =  ( (coor (id)) (buffers ...))
  ;; this function returns ...
  (cadadr rstate))

(create-map get_buffer_from_rstate :name get_buffers_from_rstate)
(create-map get_resource_from_rstate :name get_resources_from_ntkstate)

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

;; x is a state = ( ((coor (id)) (buffers ...)) ...)
(create-for-all validcoord :name ValidCoordlist :element-name x :map ((car x)))

;; x is a state = ( ((coor (id)) (buffers ...)) ...)
(create-for-all ValidBuffer :name ValidbuffersList :element-name x :map ((cadr x)))

;; NOTE: nil is a valid state, so nil is also a valid state element

(defun validstate-entryp (st_entry)
  (if (endp st_entry)
      t
    (and (Validcoord (car st_entry))
         (Validbuffer (cadr st_entry)))))

(create-for-all Validstate-entryp :name ValidState)#|ACL2s-ToDo-Line|#



