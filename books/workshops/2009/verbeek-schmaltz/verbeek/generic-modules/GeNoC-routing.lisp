#|$ACL2s-Preamble$;
;; Julien Schmaltz
;; Generic Routing Module of GeNoC
;; June 20th 2005
;; File: GeNoC-routing.lisp
;; Edited by Amr HELMY and Laurence PIERRE
;; november 27th 2007
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

;; we import the books for the set of nodes and about the data-types
(include-book "GeNoC-nodeset")
(include-book "GeNoC-misc") ;; import also GeNoC-types

(defspec GenericRouting
  ;; Routing computes the route of each message within the network
  ;; It takes as arguments: TM and NodeSet
  ;; It outputs a list of travel TrLst = (... (Id org frm Route) ...)
  ;; Constraints:
  ;; 1/ If the input is a list of valid missives, the output must be
  ;;    a list of valid travels (Ids are still unique)
  ;; 2/ Every route of every travel must be correct
  ;; 3/ Frms of the output must be equal to the frms of the input
  ;; 4/ Orgs of the output must be equal to the orgs of the input

  (((Routing * *) => *))

  ;; local witnesses
  (local (defun route (TM)
           ;; this would be the routing in a bus
           (if (endp TM)
               nil
             (let* ((msv (car TM))
                    (Id (IdTM msv))
                    (frm (FrmTM msv))
                    (origin (OrgTM msv))
                    (current (CurTM msv))
                    (destination (DestTM msv))
                    (flit (FlitTM msv))
                    (time (TimeTM msv)))
               (cons (list Id origin frm (list (list current
                                                     destination))
                           Flit time)

                     (route (cdr TM)))))))

  (local (defun routing (M NodeSet)
           (declare (ignore NodeSet))
           (route M)))

  ;; 1/ If the input is a list of valid missives, the output must be
  ;;    a list of valid travels (Ids are still unique)

  ;; local lemmas
  (local (defthm route-ids
           ;; ids of the output TrLst are equal to the ids of
           ;; the initial missives
           (equal (V-Ids (route M)) (TM-Ids M))))

  (local (defthm route-orgs                         ;; EN LOCAL ?????
           ;; orgs of the output TrLst are equal to the orgs of
           ;; the initial missives
           (equal (V-orgs (route M)) (TM-orgs M))))

  (local (defthm TrLstp-route
           ;; typing of the result of the function route
           (implies (TMissivesp M nodeset)
                    (TrLstp (route M) nodeset))))

  (defthm TrLstp-routing
    ;; 1st constraint
    ;; the travel list is recognized by TrLst
    ;; Params is a free variable
    (let ((NodeSet (NodeSetGenerator Params)))
      (implies (and (TMissivesp M NodeSet)
                    (ValidParamsp Params))
               (TrLstp (routing M NodeSet) NodeSet))))

  ;; 2/ Routes must satisfy the predicate CorrectRoutesp
  (local
   (defthm correctroutesp-route
     ;; the routes preoduced by route are correct
     (implies (TMissivesp M NodeSet)
              (CorrectRoutesp (route M) M NodeSet))))

  (defthm Routing-CorrectRoutesp
    ;; 2nd constraint
    ;; The routes produced by routing are correct
    (let ((NodeSet (NodeSetGenerator Params)))
      (implies (and (TMissivesp M NodeSet)
                    (ValidParamsp Params))
               (CorrectRoutesp (Routing M NodeSet) M NodeSet))))

  ;; some additional constraints
  (defthm true-listp-routing
    (true-listp (routing M NodeSet))
    :rule-classes :type-prescription)

  (defthm routing-nil
    ;; the routing has to return nil if the list of missives is nil
    (not (routing nil NodeSet)))
  ) ;; end of routing



(defthm tomissives-routing
  ;; the result of the routing converted into Tmisssives is equal to
  ;; the original input
  ;;list of Tmissives passed to the function as input
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (TMissivesp M NodeSet)
                  (ValidParamsp Params))
             (equal (ToTMissives (routing M NodeSet)) M)))
  :hints (("GOAL"
           :use (:instance correctroutesp-=>-toTmissives
                           (TrLst (Routing M (NodeSetGenerator Params)))
                           (TM M)
                           (NodeSet (NodeSetGenerator Params)))
           :in-theory (disable TMissivesp
                               correctroutesp-=>-toTmissives)
           :do-not-induct t)))

(defthm ids-routing
  ;; the ids of the output of routing are equal to the ids
  ;; of the initial list of missives
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (TMissivesp M NodeSet)
                  (ValidParamsp Params))
             (equal (V-ids (routing M NodeSet))
                    (TM-ids M))))
  :hints (("GOAL"
           :use ((:instance ToMissives-Routing))
           :in-theory (disable ToMissives-Routing))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

