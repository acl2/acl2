;; Julien Schmaltz
;; Generic Routing Module of GeNoC
;; June 20th 2005
;; File: GeNoC-routing.lisp

(in-package "ACL2")

;; we import the books for the set of nodes and about the data-types
(include-book "GeNoC-nodeset")

(include-book "GeNoC-misc") ;; import also GeNoC-types

(encapsulate
 ;; Routing computes the route of each message within the network
 ;; It takes as arguments: M and NodeSet
 ;; It outputs a list of travel TrLst = (... (Id frm Route) ...)
 ;; Constraints:
 ;; 1/ If the input is a list of valid missives, the output must be
 ;;    a list of valid travels (Ids are still unique)
 ;; 2/ Every route of every travel must be correct
 ;; 3/ Frms of the output must be equal to the frms of the input
 (((Routing * *) => *))

 ;; local witnesses
 (local (defun route (M)
          ;; this would be the routing in a bus
          (if (endp M)
              nil
            (let* ((msv (car M))
                   (Id (IdM msv))
                   (frm (FrmM msv))
                   (origin (OrgM msv))
                   (destination (DestM msv)))
              (cons (list Id frm (list (list origin destination)))
                    (route (cdr M)))))))

 (local (defun routing (M NodeSet)
          (declare (ignore NodeSet))
          (route M)))

 ;; 1/ If the input is a list of valid missives, the output must be
 ;;    a list of valid travels (Ids are still unique)

 ;; local lemmas
 (local (defthm route-ids
          ;; ids of the output TrLst are equal to the ids of
          ;; the initital missives
          (equal (V-Ids (route M)) (M-Ids M))))

 (local (defthm validfields-route
          (implies (Validfields-M M)
                   (validfields-TrLst (route M)))))

 (local (defthm TrLstp-route
          (implies (and (Validfields-M M)
                        (No-duplicatesp (M-ids M)))
                   (TrLstp (route M)))))

 (defthm TrLstp-routing
   ;; 1st constraint
   ;; the travel list is recognized by TrLst
   ;; Params is a free variable
   (let ((NodeSet (NodeSetGenerator Params)))
     (implies (and (Missivesp M NodeSet)
                   (ValidParamsp Params))
              (TrLstp (routing M NodeSet)))))

 ;; 2/ Routes must satisfy the predicate CorrectRoutesp
 (local
  (defthm correctroutesp-route
    (implies (Missivesp M NodeSet)
             (CorrectRoutesp (route M) M NodeSet))))

 (defthm Routing-CorrectRoutesp
   ;; 2nd constraint
   ;; The routes produced by routing are correct
   (let ((NodeSet (NodeSetGenerator Params)))
     (implies (and (Missivesp M NodeSet)
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
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (Missivesp M NodeSet)
                  (ValidParamsp Params))
             (equal (ToMissives (routing M NodeSet)) M)))
  :hints (("GOAL"
           :use (:instance correctroutesp-=>-tomissives
                           (TrLst (Routing M (NodeSetGenerator Params)))
                           (NodeSet (NodeSetGenerator Params)))
           :in-theory (disable Missivesp
                               correctroutesp-=>-tomissives)
           :do-not-induct t)))

;; A useful theorem.
(defthm ids-routing
  ;; the ids of the output of routing are equal to the ids
  ;; of the initial list of missives
  (let ((NodeSet (NodeSetGenerator Params)))
    (implies (and (Missivesp M NodeSet)
                  (ValidParamsp Params))
             (equal (V-ids (routing M NodeSet))
                    (M-ids M))))
  :hints (("GOAL"
           :use ((:instance ToMissives-Routing))
           :in-theory (disable ToMissives-Routing))))
