#|$ACL2s-Preamble$;
;; Amr HELMY
;; Miscelaneous definitions and lemmas

;;31st october 2007
;; File: GeNoC-misc.lisp
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "GeNoC-types")
(include-book "make-event/defspec"  :dir :system)
;;|-------------------------------------------------|
;;|                                                    |
;;|                    Not-in                            |
;;|                                                    |
;;|-------------------------------------------------|

(defun not-in (x y)
  (if (or (endp x) (endp y))
      t
    (and (not (member (car x) y))
         (not-in (cdr x) y))))

(defthm not-in->not-insched
  (implies (and (subsetp x y)
                (not-in z y))
           (not-in z x)))

(defthm not-in-2->not-in-append
  (implies (and (not-in x z)
                (not-in y z))
           (not-in (append x y) z)))

(defthm not-in-no-duplicatesp-equal-append
  ;; if x is not in y and both do not have duplicates then
  ;; their append has no duplicate too
  (implies (and (no-duplicatesp-equal x)
                (not-in x y)
                (no-duplicatesp-equal y))
           (no-duplicatesp-equal (append x y))))



;;|---------------------------------------|
;;|                                          |
;;|         Theoremes about Subsetp              |
;;|                                          |
;;|---------------------------------------|
;; we prove some useful lemmas about subsetp
(defthm subsetp-expand
  (implies (subsetp x y)
           (subsetp x (cons z y))))

(defthm subsetp-x-x
  (subsetp x x))

(defthm subsetp-append
  (implies (and (subsetp x S)
                (subsetp y S))
           (subsetp (append x y) S)))

(defthm member-equal-subsetp-last
  (implies (and (subsetp x NodeSet)
                (consp x))
           (member-equal (car (last x)) NodeSet)))

(defthm subsetp-trans
  ;; transitivity of subsetp
  (implies (and (subsetp x y)
                (subsetp y z))
           (subsetp x z)))

(defthm subsetp-not-in
  ;; if a list y and no element in common with z
  ;; then any sublist x of y has no element in z
  (implies (and (not-in delayed scheduled)
                (subsetp x delayed))
           (not-in x scheduled)))
;;|------------------------------------------|
;;|                                          |
;;|              Routing                     |
;;|                                          |
;;|------------------------------------------|
;; The predicates associated with the routing part are:
;; - ValidRoutep
;; - CorrectRoutesp

(defun ValidRoutep (r m)
  ;; a route r is valid according to a traveling missive m if:
  ;; a/ the origin of the r is the current node of m
  ;; b/ the destination of r is the destination node of m
  ;; c/ r is a subset of NodeSet
  ;; d/ a route r has a len >= 2
  (and (equal (car r) (CurTM m))
       (equal (car (last r)) (DestTM m))
       (not (equal (car R) (car (last R))))    ; cur /= dest
       (not (equal (OrgTM m) (car (last R))))  ; org /= dest
       ))

(defun CheckRoutes (routes m NodeSet)
  ;; checks that a list of routes is correct according to a traveling missive m
  (if (endp routes)
      t
    (let ((r (car routes)))
      (and (ValidRoutep r m)
           (subsetp r NodeSet)
           (member-equal (orgTM m) NodeSet)
           (CheckRoutes (cdr routes) m NodeSet)))))

(defun CorrectRoutesp (TrLst TM NodeSet)
  ;; TrLst is a travel list, TM is a list of traveling missives
  (if (endp TrLst)
      (if (endp TM)
          t
        nil)
    (let* ((tr (car TrLst))
           (msv (car TM))
           (routes (RoutesV tr)))
      (and (CheckRoutes routes msv NodeSet)
           (equal (IdV tr) (IdTM msv))
           (equal (FrmV tr) (FrmTM msv))
           (equal (OrgV tr) (OrgTM msv))
           (equal (FlitV tr) (FlitTm msv))
           (equal (timeV tr) (TimeTm msv))
           (CorrectRoutesp (cdr TrLst) (cdr TM) NodeSet)))))


;; the following three theorems have been moved from the file
;; GeNoC-scheduling

(defthm checkroutes-member-equal
  (implies (and (checkroutes routes m NodeSet)
                (member-equal r Routes))
           (validroutep r m)))

(defthm checkroutes-subsetp-validroute
  (implies (and (checkroutes routes m NodeSet)
                (consp r)
                (subsetp r routes))
           (and (validroutep (car r) m)
                (subsetp (car r) NodeSet))))

(defthm checkroutes-subsetp
  (implies (and (checkroutes routes m NodeSet)
                (subsetp routes1 routes))
           (checkroutes routes1 m NodeSet)))

(defthm checkroutes-orgTM
  (implies (and (checkroutes Routes TM NodeSet)
                (validfield-route Routes (Orgv TM) nodeset)
                (consp routes))
           (member-equal (orgTM TM) NodeSet)))
;;|--------------------------------|
;;|                                   |
;;|             Extract-sublst           |
;;|                                   |
;;|--------------------------------|

(defun extract-sublst (Lst Ids)
  ;; extracts the element with the Id in Ids
  ;; the output is ordered according to Ids
  (if (endp Ids)
      nil
    (append (list (assoc-equal (car Ids) Lst))
            (extract-sublst Lst (cdr Ids)))))

;;|--------------------------------|
;;|                                   |
;;|General theoremes used later on |
;;|                                   |
;;|--------------------------------|

(defthm assoc-equal-not-nil
  ;; if (assoc-equal e L) is not nil, then
  ;; its car is e !!
  (implies (assoc-equal e L)
           (equal (car (assoc-equal e L))
                  e)))

(defthm cdr-last-equal
  (implies (consp (cdr y))
           (equal (not (equal x (car (last y))))
                  (not (equal x (car (last (cdr y))))))))

;; the next theorems would be better in GeNoC-misc but then we'll
;; loose the reason for their existence
;; to have this lemma used we need to prove some
;; additional properties between len and extract-sublst
;; and len and v-ids (e.g. a is a call to v-ids)

(defthm len-extract-sublst
  (equal (len (extract-sublst l ids))
         (len ids)))

(defthm len-v-ids
  (equal (len (v-ids x))
         (len x)))

;;|---------------------------------|
;;|                                    |
;;|             tomissives             |
;;|                                 |
;;|---------------------------------|
(defun ToMissives (TmLst)
  ;;  convert a Traveling missives List to a Missive List
  (if (endp TmLst)
      nil
    (let* ((tr (car TmLst))
           (id (IdTm tr))
           (org (OrgTm tr))
           (frm (FrmTm Tr))
           (dest (DestTm tr))
           (Flit (FlitTM tr))
           (time (timeTM tr)))
      (cons (list Id org frm dest Flit time)
            (ToMissives (cdr TmLst))))))

;; for the proof of the correctness of GeNOC
;; two important lemmas are needed

;; the first one rewrites (ToMissives (extract-sublst ..))
;; to (extract-sublst (tomissives) ... )
(defthm tomissives-append     ;; OK
  ;; we first link ToMissives and append
  (equal (ToMissives (append A B))
         (append (ToMissives A) (ToMissives B))))


(defthm member-equal-assoc-equal-not-nil
  ;; if e is an Id of a travel of L
  ;; then (assoc-equal e L) is not nil
  (implies (and (member-equal e (V-ids L))
                (TrLstp L NodeSet))
           (assoc-equal e L)))


(defthm member-equal-assoc-equal-not-nil-1
  ;; if e is an Id of a travel of L
  ;; then (assoc-equal e L) is not nil
  (implies (and (member-equal e (tm-ids L))
                (tmissivesp L NodeSet))
           (assoc-equal e L)))


(defthm ToMissives-assoc-equal   ;; OK
  ;; if (assoc-equal e L) is not nil then we can link
  ;; assoc-equal and ToTMissives as follows:
  ;; (this lemma is needed to prove the next defthm)
  (implies (assoc-equal e L)
           (equal (ToMissives (list (assoc-equal e L)))
                  (list (assoc-equal e (ToMissives L))))))


(defthm ToMissives-extract-sublst   ;; OK
  ;; now we prove our main lemma
  (implies (and (subsetp ids (tm-ids L))
                (tmissivesp L NodeSet))
           (equal (ToMissives (extract-sublst L ids))
                  (extract-sublst (ToMissives L) ids)))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize)
           :induct (extract-sublst L ids)
           :do-not-induct t
           :in-theory (disable ToMissives append))
          ("Subgoal *1/2"
           :use ((:instance member-equal-assoc-equal-not-nil-1
                            (e (car ids)))))))


(defthm member-equal-assoc-equal-not-nil-M-ids   ;; OK
  ;; if a is in the ids of L then (assoc-equal e L)
  ;; is not nil
  (implies (and (member-equal e (M-ids L))
                (ValidFields-M L))
           (assoc-equal e L)))

(defthm member-equal-M-ids-assoc-equal   ;; OK
  ;; obviously if e in not in the ids of L
  ;; then (assoc-equal e L) is nil
  (implies (not (member-equal e (M-ids L)))
           (not (assoc-equal e L))))

(defthm Missivesp-not-assoc-equal      ;; OK
  ;; if M is Missivesp then nil is not a key in L
  (implies (ValidFields-M M)
           (not (assoc-equal nil M))))

(defthm assoc-equal-extract-sublst-M-lemma     ;; OK
  ;; if e is not in id1 there is no key equal to e
  ;; after filtering according to id1
  (implies (and (not (member-equal e id1))
                (ValidFields-M M))
           (not (assoc-equal e (extract-sublst M id1)))))

(defthm assoc-equal-extract-sublst-M-1    ;; OK
  ;; if e is a key in id1 then e is still a key
  ;; after filtering according to id1
  (implies (and (member-equal e id1)
                (ValidFields-M M))
           (equal (assoc-equal e (extract-sublst M id1))
                  (assoc-equal e M)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :induct (extract-sublst M id1))
          ("Subgoal *1/2"
           :cases ((member-equal (car id1) (M-ids M))))))


(defthm extract-sublst-cancel-M      ;; OK
  ;; and now we can prove our second main lemma
  (implies (and (subsetp id2 id1)
                (ValidFields-m M))
           (equal (extract-sublst (extract-sublst M id1) id2)
                  (extract-sublst M id2))))
(defthm equalid-tomissives
  (implies (TMissivesp m nodeset)
           (equal (M-ids (ToMissives m))
                  (Tm-ids m)))
  :rule-classes nil)

(defthm nodup-tmissivesp-tomissives
  (implies (TMissivesp m nodeset)
           (no-duplicatesp (M-ids (ToMissives m))))
  :hints (("Goal" :use (:instance equalid-tomissives))))

(defthm subset-orgs-tomissives
  (implies  (TMissivesp m nodeset)
            (subsetp (m-orgs (tomissives m))nodeset)))

(defthm subset-dests-tomissives
  (implies  (TMissivesp m nodeset)
            (subsetp (m-dests (tomissives m)) nodeset)))

(defthm fwd-missivesp
  ;; as missivesp is disabled we prove this rule to add
  ;; the content of missivesp as hypotheses
  (implies (missivesp M NodeSet)
           (and (Validfields-M M)
                (subsetp (M-orgs M) NodeSet)
                (subsetp (M-dests M) NodeSet)
                (True-listp M)
                (No-duplicatesp-equal (M-ids M))))
  :rule-classes :forward-chaining)

(defthm valid-fieldstm-implies-validfieldm
  (implies (tmissivesp m nodeset)
           (validfields-m (ToMissives m))))

(defthm tomissives-truelistp
  (implies (Tmissivesp M nodeset)
           (true-listp (tomissives m))))

(defthm to-missives-missivesp
  (implies (TMissivesp m nodeset)
           (Missivesp (ToMissives m) NodeSet))
  :hints(("Goal"
          :use ((:instance nodup-tmissivesp-tomissives)
                (:instance subset-dests-tomissives)
                (:instance subset-orgs-tomissives)
                (:instance valid-fieldstm-implies-validfieldm)
                (:instance tomissives-truelistp))
          :in-theory (disable tomissives-truelistp tmissivesp
                              subset-dests-tomissives
                              subset-orgs-tomissives
                              valid-fieldstm-implies-validfieldm))))


(defthm tomissives-len-equal
  (equal  (len (tomissives x))
          (len x)))

(defthm m-ids-append-invert
  ;; append out of the mids
  (implies (and (missivesp a nodeset)
                (missivesp b nodeset))
           (equal (m-ids (append a b))
                  (append (m-ids a) (m-ids b)))))

(defthm missivesp-append-noduplicates
  ;; appending the ids of two missivesp that has no ids in common
  ;; result in a non duplicates list
  (implies (and (missivesp a nodeset)
                (missivesp b nodeset)
                (not-in (m-ids a) (m-ids b)))
           (no-duplicatesp (append (m-ids a) (m-ids b)) ))
  :hints (("Goal" :do-not '(eliminate-destructors generalize))))

(defthm missivesp-append-missivesp
  ;;appending 2 missivesp with no intersections in the ids result in a
  ;;missivesp
  (implies (and (missivesp a nodeset)
                (missivesp b nodeset)
                (not-in (m-ids a) (m-ids b)))
           (missivesp (append a b) nodeset))
  :hints (("Goal" :do-not '(eliminate-destructors generalize) )
          ("Subgoal *1/2" :use ((:instance m-ids-append-invert )
                                (:instance missivesp-append-noduplicates)))))


(defthm extract-sublst-subsetp-M-ids       ;; OK
  ;; filtering a list l according to a subset ids of its identifiers
  ;; produces a list the ident. of which are ids
  (implies (and (subsetp ids (M-ids l))
                (true-listp ids)
                (missivesp l nodeset))
           (equal (M-ids (extract-sublst l ids))
                  ids)))

(defthm valid-missive-assoc-equal       ;; OK
  ;; a list of a member of a valid list of missives
  ;; is a valid list of missives
  (implies (and (Missivesp M NodeSet)
                (member-equal e (M-ids M)))
           (Missivesp (list (assoc-equal e M)) NodeSet)))

(defthm Missivesp-cons       ;; OK
  ;; lemma used in the next defthm
  ;; if we cons a valid missive to a filtered valid list
  ;; of missives, we obtain a valid list of missives if the
  ;; the id of the consed missive is not in the filter
  (implies (and (Missivesp (extract-sublst M ids) nodeset)
                (Missivesp (list (assoc-equal e M)) nodeset)
                (not (member-equal e ids))
                (subsetp ids (M-ids M)))
           (Missivesp (cons (assoc-equal e M) (extract-sublst M ids))
                      nodeset)))

(defthm missivespx-m-ids-car-x-equal-idm-carx ;;OK
  ;;equivalence between idm of car of a list
  ;;and the car of the m-ids of the same list
  (implies (missivesp x nodeset)
           (equal (Idm (car x))(car(m-ids x))))
  :rule-classes nil)

(defthm memberequal-implies-id-member-missives ;OK
  ;; member of a list then the id of the element is a member of the
  ;; ids of the list
  (implies (member-equal  x l)
           (member-equal (idm x) (m-ids l))))

(defthm member-cdr-id-not-eq-car-missives ;OK
  ;;if x is a member in the cdr y then the id of car of y is not equal
  ;;to x's id
  (implies (and (no-duplicatesp-equal (m-ids y))
                (member-equal x (cdr y)))
           (not (equal (idm x)  (idm (car y)))))
    :hints (("Goal"
             :use (:instance memberequal-implies-id-member-missives
                             (l (cdr y))))))

(defthm member-cdr-id-not-eq-carbis-missives ;;OK
  ;;same as the previous theorem but with the car instead of the idm
  ;; to use in some cases instead of removing the idm
  ;; this theorem might be removed
  (implies (and (no-duplicatesp (m-ids y))
                (member-equal x (cdr y)))
           (not (equal (idm x)  (car (car y)))))
  :hints (("Goal"  :use (:instance member-cdr-id-not-eq-car-missives
                                   ))))

(defthm assoc-eq-member-cdr-eq-extraction-missives ;;ok
  (implies (and  (missivesp y nodeset)
                 (member x (cdr y)))
           (equal (assoc-equal (idm  x) y)
                  (assoc-equal (idm  x) (cdr y)) ))
  :hints (("Goal"
           :use (:instance member-cdr-id-not-eq-carbis-missives)
           :in-theory (disable Idm m-ids validfields-m)
           :do-not '(eliminate-destructors generalize))))


(defthm id-not-eq-car-member-cdr-missives
  ;; the inverse of one of the previous lemmas, if the id of x isn't
  ;; equal to the id of the first element of y and x is  a member of y
  ;; then x is a member of cdr y
  (implies (and (not (equal (idm x) (caar y)))
                (member-equal x y))
           (member-equal x (cdr y))))

(defthm missivesy-missives-cdry
  ;; missivesp y then missivesp cdr y
  (implies (missivesp y nodeset)
           (missivesp (cdr y) nodeset)))

(defthm member-assoc-eq-equalx-missives
  ;;using th eid of x which is a member of a missivep y to extract an
  ;;element from y will be equal to x
  (implies (and  (missivesp y nodeset)
                 (consp x)
                 (member-equal x y))
           (equal (assoc-equal (idm  x) y) x))
  :hints (("Goal"
           :use (:instance missivesy-missives-cdry)
           :in-theory (disable Idm t-ids validfields-m)
           :do-not '(eliminate-destructors generalize))))


(defthm m-ids-cdr-equal-cdr-m-ids
  (implies (missivesp x nodeset )
           (equal (cdr(m-ids x))
                  (m-ids (cdr x)) ))
  :rule-classes nil)

(defthm missivesp-equal-subsetp ;;OK
  (implies (and (missivesp x nodeset)
                (missivesp y nodeset)
                (subsetp x y))
           (equal (extract-sublst y (m-ids x)) x))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance member-assoc-eq-equalx-missives (x (car x)))
                 (:instance missivespx-m-ids-car-x-equal-idm-carx)
                 (:instance m-ids-cdr-equal-cdr-m-ids))
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable member-assoc-eq-equalx-missives))
          ("Subgoal *1/2"
           :use ((:instance member-assoc-eq-equalx-missives (x (car x)))
                 (:instance m-ids-cdr-equal-cdr-m-ids)))))


(defthm missivesp-equal-extract-two-levels ;;ok
  (implies (and (missivesp x nodeset)
                (subsetp x m)
                (subsetp y x)
                (missivesp m nodeset)
                (missivesp y nodeset))
           (equal (extract-sublst m (m-ids y))
                  (extract-sublst x (m-ids y))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance missivesp-equal-subsetp (y M) (x y))
                        (:instance missivesp-equal-subsetp (y X) (x y)))
           :in-theory (disable Validfields-m)
           :do-not '(eliminate-destructors))))



(defthm missivesp-sublst-subsetp ;;ok
  (implies (and (missivesp x nodeset)
                (missivesp y nodeset)
                (missivesp z nodeset))
           (equal
            (append (extract-sublst x (m-ids y)) (extract-sublst x (m-ids z)))
            (extract-sublst x (append (m-ids y) (m-ids z)))))
  :rule-classes nil)



(defthm tmissives-subset-extract-tomissives-equal
  (implies (and (tmissivesp x nodeset)
                (subsetp ids (tm-ids x)))
           (equal (extract-sublst (tomissives x) ids)
                  (tomissives (extract-sublst  x ids))))
  :rule-classes nil
  :hints (("Goal"
           :use (:instance ToMissives-extract-sublst (l x) )
           :do-not '(eliminate-destructors generalize))))


(defthm subsetpx-y-equal-extract-missives
  (implies (and (subsetp x y)
                (subsetp ids (m-ids x))
                (subsetp (m-ids x) (m-ids  y))
                (missivesp x nodeset)
                (missivesp y nodeset))
           (equal (extract-sublst (extract-sublst Y (m-ids x)) ids)
                  (extract-sublst x ids)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance missivesp-equal-subsetp)))))

(defthm subsetpx-y-equal-extract-final-missives
  ;; if x subsetp of y and ids is subsetp of x's ids then the
  ;; extraction from x is equal to the extraction of y
  (implies (and (subsetp x y)
                (subsetp ids (m-ids x))
                (subsetp (m-ids x) (m-ids  y))
                (missivesp x nodeset)
                (missivesp y nodeset))
           (equal (extract-sublst x ids)
                  (extract-sublst y ids)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance subsetpx-y-equal-extract-missives )
                 (:instance extract-sublst-cancel-M
                            (M y)
                            (Id2 ids)
                            (Id1 (m-ids x)))))))



;;|------------------------------|
;;|                              |
;;|            toTmissives                 |
;;|                                 |
;;|------------------------------|

(defun ToTMissives (TrLst)
  ;;  convert a Travel List to a Traveling Missive List
  (if (endp TrLst)
      nil
    (let* ((tr (car TrLst))
           (frm (FrmV tr))
           (org (OrgV tr))
           (routes (RoutesV tr))
           (id (IdV tr))
           (Flit (FlitV tr))
           (Time (TimeV tr)))
      (cons (list id org (caar routes) frm (car (last (car routes))) Flit time)
            (ToTMissives (cdr TrLst))))))

(defthm correctroutesp-=>-toTmissives    ;; OK
  (implies (and (CorrectRoutesp TrLst TM NodeSet)
                (TMissivesp TM NodeSet)
                (TrLstp TrLst NodeSet))
           (equal (ToTMissives TrLst) TM)))

(defthm TM-ids-ToMissives-V-ids    ;; OK
  (equal (TM-ids (ToTMissives x)) (V-ids x)))

(defthm CorrectRoutesp-member-equal     ;; OK
  (implies (and (correctRoutesp TrLst (ToTMissives TrLst) NodeSet)
                (TrLstp TrLst NodeSet)
                (member-equal e (v-ids TrLst)))
           (checkroutes (RoutesV (assoc-equal e TrLst))
                        (assoc-equal e (ToTMissives TrLst))
                        NodeSet)))





;; for the proof of the correctness of GeNOC
;; two important lemmas are needed

;; the first one rewrites (ToMissives (extract-sublst ..))
;; to (extract-sublst (tomissives) ... )
(defthm ToTMissives-append    ;; OK
  ;; we first link ToTMissives and append
  (equal (ToTMissives (append A B))
         (append (ToTMissives A) (ToTMissives B))))

(defthm ToTMissives-assoc-equal   ;; OK
  ;; if (assoc-equal e L) is not nil then we can link
  ;; assoc-equal and ToTMissives as follows:
  ;; (this lemma is needed to prove the next defthm)
  (implies (assoc-equal e L)
           (equal (ToTMissives (list (assoc-equal e L)))
                  (list (assoc-equal e (ToTMissives L))))))

(defthm ToTMissives-extract-sublst   ;; OK
  ;; now we prove our main lemma
  (implies (and (subsetp ids (V-ids L))
                (TrLstp L NodeSet))
           (equal (ToTMissives (extract-sublst L ids))
                  (extract-sublst (ToTMissives L) ids)))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize)
           :induct (extract-sublst L ids)
           :do-not-induct t
           :in-theory (disable ToTMissives append))
          ("Subgoal *1/2"
           :use ((:instance member-equal-assoc-equal-not-nil
                            (e (car ids)))))))


;; the second lemma we need, allow us to cancel
;; one successive call of extract-sublst
(defthm member-equal-assoc-equal-not-nil-TM-ids   ;; OK
  ;; if a is in the ids of L then (assoc-equal e L)
  ;; is not nil
  (implies (and (member-equal e (TM-ids L))
                (ValidFields-TM L))
           (assoc-equal e L)))

(defthm member-equal-TM-ids-assoc-equal   ;; OK
  ;; obviously if e in not in the ids of L
  ;; then (assoc-equal e L) is nil
  (implies (not (member-equal e (TM-ids L)))
           (not (assoc-equal e L))))

(defthm TMissivesp-not-assoc-equal      ;; OK
  ;; if M is Missivesp then nil is not a key in L
  (implies (ValidFields-TM M)
           (not (assoc-equal nil M))))


(defthm assoc-equal-extract-sublst-TM-lemma     ;; OK
  ;; if e is not in id1 there is no key equal to e
  ;; after filtering according to id1
  (implies (and (not (member-equal e id1))
                (ValidFields-TM M))
           (not (assoc-equal e (extract-sublst M id1)))))

(defthm assoc-equal-extract-sublst-M    ;; OK
  ;; if e is a key in id1 then e is still a key
  ;; after filtering according to id1
  (implies (and (member-equal e id1)
                (ValidFields-TM M))
           (equal (assoc-equal e (extract-sublst M id1))
                  (assoc-equal e M)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :induct (extract-sublst M id1))
          ("Subgoal *1/2"
           :cases ((member-equal (car id1) (TM-ids M))))))

(defthm extract-sublst-cancel-TM      ;; OK
  ;; and now we can prove our second main lemma
  (implies (and (subsetp id2 id1)
                (ValidFields-TM M))
           (equal (extract-sublst (extract-sublst M id1) id2)
                  (extract-sublst M id2))))





;;;--------------------------------------
;; Finally, we prove that the correctness of the routes
;; is preserved by extract-sublst
(defthm extract-sublst-identity
  (implies (TrLstp TrLst nodeset)
           (equal (extract-sublst TrLst (V-ids TrLst))
                  TrLst)))

(defthm assoc-equal-ToTMissives-not-nil   ;; OK
  ;; if e is in the ids of L then there is a key equal to
  ;; e in (ToTMissives L)
  (implies (and (TrLstp L nodeset)
                (member-equal e (V-ids L)))
           (assoc-equal e (ToTMissives L))))

(defthm ToTMissives-CorrectRoutesp-Extract-sublst  ;; OK
  ;; we prove the current lemma
  (implies (and (subsetp ids (V-ids TrLst))
                (TrLstp TrLst nodeset)
                (CorrectRoutesp TrLst (ToTMissives TrLst) NodeSet))
           (CorrectRoutesp (extract-sublst TrLst ids)
                           (ToTMissives (extract-sublst TrLst ids))
                           NodeSet)))


;; Finally, we prove that converting a list of travels
;; to a list of Tmissives gives something that is recoginized
;; by TMissivesp
(defthm TMissivesp-ToMissives
  (implies (and (correctroutesp TrLst (ToTMissives TrLst) NodeSet)
                (TrLstp TrLst nodeset))
           (TMissivesp (ToTMissives TrLst) NodeSet)))

;; next theorem is a generalisation of the previous one

(defthm TMissivesp-ToMissives-bis
  (implies (trlstp trlst nodeset)
           (TMissivesp (ToTMissives TrLst) NodeSet)))

(defthm fwd-tmissivesp
  ;; as Tmissivesp is disabled we prove this rule to add
  ;; the content of Tmissivesp as hypotheses
  (implies (Tmissivesp M NodeSet)
           (and (Validfields-TM M)
                (subsetp (TM-orgs M) NodeSet)
                (subsetp (TM-curs M) NodeSet)
                (subsetp (TM-dests M) NodeSet)
                (True-listp M)
                (No-duplicatesp-equal (TM-ids M))))
  :rule-classes :forward-chaining)


(defthm tm-ids-append-invert
  (implies (and (tmissivesp a nodeset)
                (tmissivesp b nodeset))
           (equal (tm-ids (append a b))
                  (append (tm-ids a) (tm-ids b)))))

(defthm tmissivesp-append-noduplicates
  (implies (and        (tmissivesp a nodeset)
                (tmissivesp b nodeset)
                (not-in (tm-ids a) (tm-ids b)))
           (no-duplicatesp (append (tm-ids a) (tm-ids b)) ))
  :hints (("Goal" :do-not '(eliminate-destructors generalize))))

(defthm tmissivesp-append-tmissivesp
  (implies (and (tmissivesp a nodeset)
                (tmissivesp b nodeset)
                (not-in (tm-ids a) (tm-ids b)))
           (tmissivesp (append a b) nodeset))
  :hints (("Goal" :do-not '(eliminate-destructors generalize) )
          ("Subgoal *1/2" :use ((:instance tm-ids-append-invert )
                                (:instance tmissivesp-append-noduplicates)))))


(defthm extract-sublst-subsetp-TM-ids       ;; OK
  ;; filtering a list l according to a subset ids of its identifiers
  ;; produces a list the ident. of which are ids
  (implies (and (subsetp ids (TM-ids l))
                (true-listp ids)
                (Tmissivesp l nodeset))
           (equal (TM-ids (extract-sublst l ids))
                  ids)))
(defthm valid-tmissive-assoc-equal       ;; OK
  ;; a list of a member of a valid list of missives
  ;; is a valid list of missives
  (implies (and (TMissivesp M NodeSet)
                (member-equal e (TM-ids M)))
           (TMissivesp (list (assoc-equal e M)) NodeSet)))

(defthm TMissivesp-cons       ;; OK
  ;; lemma used in the next defthm
  ;; if we cons a valid missive to a filtered valid list
  ;; of missives, we obtain a valid list of missives if the
  ;; the id of the consed missive is not in the filter
  (implies (and (TMissivesp (extract-sublst M ids) nodeset)
                (TMissivesp (list (assoc-equal e M)) nodeset)
                (not (member-equal e ids))
                (subsetp ids (TM-ids M)))
           (TMissivesp (cons (assoc-equal e M) (extract-sublst M ids))
                       nodeset)))

(defthm tmissivesp-extract
  ;;extracting a part of Tmissives list will give a Tmissivesp
  (implies (and (tmissivesp M nodeset)
                (subsetp ids (tm-ids M))
                (no-duplicatesp-equal ids))
           (tmissivesp (extract-sublst M ids) nodeset)))

(defthm tmissivespx-tm-ids-car-x-equal-idtm-carx
  ;; getting the car out of the IDTM
  (implies (tmissivesp x nodeset)
           (equal (IDTM (car x))(car(tm-ids x))))
  :rule-classes nil)

(defthm memberequal-implies-id-member ;OK
  ;; the IDs of a member of a list are part of the ids of this list
  (implies (member-equal  x l)
           (member-equal (idtm x) (tm-ids l))))


(defthm member-cdr-id-not-eq-car
  (implies (and (no-duplicatesp-equal (tm-ids y))
                (member-equal x (cdr y)))
           (not (equal (idtm x) (idtm (car y)))))
  :hints (("Goal"
           :use (:instance memberequal-implies-id-member
                           (l (cdr y))))))

;; the following theorem is to be removed as soon as i find the place
;; where it's used and then deactivate the functino IDTM


(defthm member-cdr-id-not-eq-carbis
  ;; if x is a member of cdr y and no duplicates y then idtm of x is
  ;; not equal to idtm of car y
  (implies (and (no-duplicatesp (tm-ids y))
                (member-equal x (cdr y)))
           (not (equal (idtm x)  (car (car y)))))
  :hints (("Goal"
           :use (:instance member-cdr-id-not-eq-car))))

(defthm assoc-eq-member-cdr-eq-extraction ;;ok
  ;; x member of cdr y the idtm is only in the ids of cdr y
  (implies (and  (tmissivesp y nodeset)
                 (member x (cdr y)))
           (equal (assoc-equal (idtm  x) y)
                  (assoc-equal (idtm  x) (cdr y)) ))
  :hints (("Goal"
           :use (:instance member-cdr-id-not-eq-carbis)
           :in-theory (disable Idtm tm-ids validfields-tm)
           :do-not '(eliminate-destructors generalize))))

(defthm id-not-eq-car-member-cdr
  (implies (and (not (equal (idtm x) (caar y)))
                (member-equal x y))
           (member-equal x (cdr y))))

(defthm tmissivesy-tmissives-cdry
  (implies (tmissivesp y nodeset)
           (tmissivesp (cdr y) nodeset)))

(defthm member-assoc-eq-equalx
  (implies (and  (tmissivesp y nodeset)
                 (consp x)
                 (member-equal x y))
           (equal (assoc-equal (idtm  x) y) x))
  :hints (("Goal"
           :use (:instance tmissivesy-tmissives-cdry )
           :in-theory (disable Idtm tm-ids validfields-tm)
           :do-not '(eliminate-destructors generalize))))


(defthm tm-ids-cdr-equal-cdr-tm-ids
  ;; getting the cdr out of the tm-ids
  (implies (tmissivesp x nodeset )
           (equal  (cdr(tm-ids x))(tm-ids (cdr x)) ))
  :rule-classes nil)



(defthm tmissivesp-equal-subsetp ;;ok
  ;;extracting from a tmissivesp a list based upon the ids of subsetp
  ;;qill be equal to the subset list
  (implies (and (tmissivesp x nodeset)
                (tmissivesp y nodeset)
                (subsetp x y))
           (equal (extract-sublst y (tm-ids x)) x))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance member-assoc-eq-equalx (x (car x)))
                 (:instance tmissivespx-tm-ids-car-x-equal-idtm-carx)
                 (:instance tm-ids-cdr-equal-cdr-tm-ids))
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable member-assoc-eq-equalx ))
          ("Subgoal *1/2"
           :use  ((:instance member-assoc-eq-equalx (x (car x)))
                  (:instance tm-ids-cdr-equal-cdr-tm-ids)))))

(defthm tmissivesp-equal-extract-two-levels ;;ok
  (implies (and (tmissivesp x nodeset)
                (subsetp x m)
                (subsetp y x)
                (tmissivesp m nodeset)
                (tmissivesp y nodeset))
           (equal (extract-sublst m (tm-ids y))
                  (extract-sublst x (tm-ids y))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance tmissivesp-equal-subsetp (y M) (x y))
                 (:instance tmissivesp-equal-subsetp (y X) (x y)))
           :in-theory (disable Validfields-Tm)
           :do-not '(eliminate-destructors))))



(defthm tmissivesp-sublst-subsetp ;;ok
  ;; getting the append into the extract sublst
  (implies (and (tmissivesp x nodeset)
                (tmissivesp y nodeset)
                (tmissivesp z nodeset))
           (equal
            (append (extract-sublst x (tm-ids y))
                    (extract-sublst x (tm-ids z)))
            (extract-sublst x (append (tm-ids y) (tm-ids z)))))
  :rule-classes nil)

(defthm subsetpx-y-equal-extract
  (implies (and (subsetp x y)
                (subsetp ids (tm-ids x))
                (subsetp (Tm-ids x) (tm-ids  y))
                (tmissivesp x nodeset)
                (tmissivesp y nodeset))
           (equal (extract-sublst (extract-sublst Y (tm-ids x)) ids)
                  (extract-sublst x ids)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance tmissivesp-equal-subsetp) ))))


(defthm subsetpx-y-equal-extract-final
  (implies (and (subsetp x y)
                (subsetp ids (tm-ids x))
                (subsetp (Tm-ids x) (tm-ids  y))
                (tmissivesp x nodeset)
                (tmissivesp y nodeset))
           (equal (extract-sublst x ids)
                  (extract-sublst y ids)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance subsetpx-y-equal-extract )
                 (:instance extract-sublst-cancel-tM
                            (M y)
                            (Id2 ids)
                            (Id1 (tm-ids x)))))))

(defthm tm-frms-to-v-frms             ;; ok
  ;; this rule is only used to rewrite the theorem arrived-v-frms-m-frms to
  ;;s/d-travel-v-frms.
  (equal  (tm-frms (totmissives x))
          (v-frms x))
  :rule-classes nil)
;;|------------------------------|
;;|                                 |
;;|              Travels            |
;;|                                 |
;;|------------------------------|

(defthm valid-trlstp-assoc-equal
  (implies (and (TrLstp L nodeset)
                (member-equal e (V-ids L)))
           (TrLstp (list (assoc-equal e L))nodeset)))

(defthm TrLstp-cons
  ;; lemma used in the next defthm
  ;; if we cons a valid travel to a filtered valid list
  ;; of travel, we obtain a valid list of travel if the
  ;; consed travel has an id less than the first of the filter
  ;; and this id is not in the filter
  (implies (and (trlstp (extract-sublst L ids)nodeset)
                (trlstp (list (assoc-equal e L))nodeset)
                (not (member-equal e ids))
                (subsetp ids (V-ids L)))
           (trlstp (cons (assoc-equal e L)
                         (extract-sublst L ids))nodeset)))

(defthm trlstp-extract-sublst
  (implies (and (TrLstp TrLst nodeset)
                (subsetp ids (v-ids TrLst))
                (no-duplicatesp ids)
                (true-listp ids))
           (trlstp (extract-sublst TrLst ids) nodeset)))

(defthm extract-sublst-subsetp-v-ids
  (implies (and (subsetp ids (V-ids l))
                (true-listp ids)
                (TrLstp l nodeset))
           (equal (v-ids (extract-sublst l ids))
                  ids))
  :hints (("GOAL"
           :in-theory (disable TrLstp))))

(defthm fwd-trlstp
  ;; because we disable trlstp, this rule adds its content
  ;; as hypotheses
  (implies (TrLstp TrLst nodeset)
           (and (validfields-trlst trlst nodeset)
                (true-listp trlst)
                (no-duplicatesp-equal (v-ids trlst))))
  :rule-classes :forward-chaining)

(defthm validfields-append
  ;; lemma for validfields-trlst-genoc_nt
  (implies (and (validfields-trlst l1 nodeset)
                (validfields-trlst l2 nodeset))
           (validfields-trlst (append l1 l2) nodeset)))

(defthm trlstpx-v-ids-car-x-equal-idv-carx ;;OK
  ;;equivalence between idm of car of a list and the car of the m-ids
  ;;of the same list
  (implies (trlstp x nodeset)
           (equal (Idv (car x))(car(v-ids x))))
  :rule-classes nil)

(defthm memberequal-implies-id-member-trlst ;OK
  ;; member of a list then the id of the element is a member of the
  ;; ids of the list
  (implies (member-equal  x l)
           (member-equal (idv x) (v-ids l))))


(defthm member-cdr-id-not-eq-car-trlst ;OK
  ;;if x is a member in the cdr y then the id of car of y is not equal
  ;;to x's id
  (implies (and (no-duplicatesp-equal (v-ids y))
                (member-equal x (cdr y)))
           (not (equal (idv x)  (idv (car y)))))

  :hints (("Goal"
           :use
           (:instance memberequal-implies-id-member-trlst (l (cdr y))))))

(defthm member-cdr-id-not-eq-carbis-trlst ;OK
  ;;same as the previous theorem but with the car instead of the idm
  ;; to use in some cases instead of removing the idm
  ;; this theorem might be removed
  (implies (and (no-duplicatesp (v-ids y))
                (member-equal x (cdr y)))
           (not (equal (idv x)  (car (car y)))))
  :hints (("Goal"  :use (:instance member-cdr-id-not-eq-car-trlst ))))

(defthm assoc-eq-member-cdr-eq-extraction-trlst ;;ok
  (implies (and  (trlstp y nodeset)
                 (member x (cdr y)))
           (equal (assoc-equal (idv  x) y)
                  (assoc-equal (idv  x) (cdr y)) ))
  :hints (("Goal" :use (:instance member-cdr-id-not-eq-carbis-trlst)
           :in-theory (disable Idv v-ids validfields-trlst)
           :do-not '(eliminate-destructors generalize))))


(defthm id-not-eq-car-member-cdr-trlst
  ;; the inverse of one of the previous lemmas, if the id of x isn't
  ;; equal to the id of the first element of y and x is  a member of y
  ;; then x is a member of cdr y
  (implies (and (not (equal (idv x) (caar y)))
                (member-equal x y))
           (member-equal x (cdr y))))

(defthm trlsty-trlst-cdry
  ;; missivesp y then missivesp cdr y
  (implies (trlstp y nodeset)
           (trlstp (cdr y) nodeset)))

(defthm member-assoc-eq-equalx-trlst
  ;;using the id of x which is a member of a missivep y to extract an
  ;;element from y will be equal to x
  (implies (and  (trlstp y nodeset)
                 (consp x)
                 (member-equal x y))
           (equal (assoc-equal (idv  x) y) x))
  :hints (("Goal" :use (:instance trlsty-trlst-cdry )
           :in-theory (disable Idv v-ids validfields-trlst)
           :do-not '(eliminate-destructors generalize))))


(defthm v-ids-cdr-equal-cdr-v-ids
  (implies (trlstp x nodeset )
           (equal  (cdr(v-ids x))(v-ids (cdr x)) ))
  :rule-classes nil)

(defthm trlstp-equal-subsetp ;;OK
  (implies (and (trlstp x nodeset)
                (trlstp y nodeset)
                (subsetp x y))
           (equal (extract-sublst y (v-ids x)) x))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance member-assoc-eq-equalx-trlst (x (car x)))
                 (:instance trlstpx-v-ids-car-x-equal-idv-carx)
                 (:instance v-ids-cdr-equal-cdr-v-ids))
           :do-not '(eliminate-destructors generalize)
           :in-theory (disable member-assoc-eq-equalx-trlst))
          ("Subgoal *1/2"
           :use ((:instance member-assoc-eq-equalx-trlst (x (car x)))
                 (:instance v-ids-cdr-equal-cdr-v-ids)))))


(defthm trlstp-equal-extract-two-levels ;;ok
  (implies (and (trlstp x nodeset)
                (subsetp x m)
                (subsetp y x)
                (trlstp m nodeset)
                (trlstp y nodeset))
           (equal (extract-sublst m (v-ids y))
                  (extract-sublst x (v-ids y))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance trlstp-equal-subsetp (y M) (x y))
                 (:instance trlstp-equal-subsetp (y X) (x y)))
           :in-theory (disable Validfields-trlst)
           :do-not '(eliminate-destructors))))


(defthm member-equal-assoc-equal-not-nil-v-ids   ;; OK
  ;; if a is in the ids of L then (assoc-equal e L)
  ;; is not nil
  (implies (and (member-equal e (v-ids L))
                (ValidFields-Trlst l nodeset))
           (assoc-equal e L)))



(defthm member-equal-v-ids-assoc-equal   ;; OK
  ;; obviously if e in not in the ids of L
  ;; then (assoc-equal e L) is nil
  (implies (not (member-equal e (v-ids L)))
           (not (assoc-equal e L))))

(defthm Trlstp-not-assoc-equal      ;; OK
  ;; if M is Missivesp then nil is not a key in L
  (implies (ValidFields-Trlst M nodeset)
           (not (assoc-equal nil M))))

(defthm assoc-equal-extract-sublst-Trlst-lemma     ;; OK
  ;; if e is not in id1 there is no key equal to e
  ;; after filtering according to id1
  (implies (and (not (member-equal e id1))
                (ValidFields-Trlst M nodeset))
           (not (assoc-equal e (extract-sublst M id1)))))



(defthm assoc-equal-extract-sublst-trlst    ;; OK
  ;; if e is a key in id1 then e is still a key
  ;; after filtering according to id1
  (implies (and (member-equal e id1)
                (ValidFields-Trlst M nodeset))
           (equal (assoc-equal e (extract-sublst M id1))
                  (assoc-equal e M)))
  :otf-flg t
  :hints (("GOAL"
           :do-not-induct t
           :induct (extract-sublst M id1))
          ("Subgoal *1/2"

           :cases ((member-equal (car id1) (v-ids M))))
          ("Subgoal *1/2.1"
           :use (:instance Trlstp-not-assoc-equal))))

(defthm extract-sublst-cancel-Trlst      ;; OK
  ;; and now we can prove our second main lemma
  (implies (and (subsetp id2 id1)
                (ValidFields-Trlst M nodeset))
           (equal (extract-sublst (extract-sublst M id1) id2)
                  (extract-sublst M id2))))


;;|------------------------------|
;;|                                 |
;;|                 rev                 |
;;|------------------------------|
(defun rev (x)
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

(defthm subset-rev
  (implies (and (trlstp x nodeset)
                (trlstp y nodeset)
                (subsetp x y))
           (subsetp x (rev y))))

(defthm subset-rev-1st
  (implies (and (trlstp x nodeset)
                (trlstp y nodeset)
                (subsetp x y))
           (subsetp (rev x) y)))

(defthm subsetpvids-rev
  (implies (and (trlstp x nodeset)
                (trlstp y nodeset)
                (subsetp (v-ids x) (v-ids y)))
           (subsetp (rev (v-ids  x)) (v-ids y))))

;;|------------------------------|
;;|                                 |
;;|            Transactionsp                 |
;;|                                 |
;;|------------------------------|

(defthm fwd-chaining-transactionsp
  (implies (transactionsp trs nodeset)
           (and (validfields-t trs)
                (true-listp trs)
                (subsetp (t-orgs trs) nodeset)
                (subsetp (t-dests trs) nodeset)
                (no-duplicatesp-equal (t-ids trs))))
  :rule-classes :forward-chaining)

(defthm fwd-chaining-transactionsp-bis
  (implies (transactionsp trs nodeset)
           (and (validfields-t trs)
                (true-listp trs)
                (subsetp (t-orgs trs) nodeset)
                (subsetp (t-dests trs) nodeset)))
  :rule-classes :forward-chaining)#|ACL2s-ToDo-Line|#


;; valid ntkstate
(defthm validstate-entry-implies-coord-and-buffer
  (implies (and (validstate-entryp x)
                (consp x))
           (and (validcoord (car x))
                (validbuffer (cadr x)))))