;; Julien Schmaltz
;; Misceaneous definitions and lemmas
;; June 20th 2005
;; File: GeNoC-misc.lisp

(in-package "ACL2")

(include-book "GeNoC-types")

;;                    ROUTING

;; The predicates associated with the routing part are:
;; - ValidRoutep
;; - CorrectRoutesp

(defun ValidRoutep (r m)
  ;; a route r is valid according to a missive m if:
  ;; a/ the origin of the r is the source node of m
  ;; b/ the destination of r is the destination node of m
  ;; c/ r is a subset of NodeSet
  ;; d/ a route r has a len >= 2
  (and (equal (car r) (OrgM m))
       (equal (car (last r)) (DestM m))
       (not (equal (car R) (car (last R))))))

(defun CheckRoutes (routes m NodeSet)
  ;; checks that a list of routes is correct according to a missive m
  (if (endp routes)
      t
    (let ((r (car routes)))
      (and (ValidRoutep r m)
           (subsetp r NodeSet)
           (CheckRoutes (cdr routes) m NodeSet)))))

(defun CorrectRoutesp (TrLst M NodeSet)
  (if (endp TrLst)
      (if (endp M)
          t
        nil)
    (let* ((tr (car TrLst))
           (msv (car M))
           (routes (RoutesV tr)))
      (and (CheckRoutes routes msv NodeSet)
           (equal (IdV tr) (IdM msv))
           (equal (FrmV tr) (FrmM msv))
           (CorrectRoutesp (cdr TrLst) (cdr M) NodeSet)))))

;;                     TO MISSIVES

(defun ToMissives (TrLst)
  ;;  convert a Travel List to a Missive
  (if (endp TrLst)
      nil
    (let* ((tr (car TrLst))
           (frm (FrmV Tr))
           (routes (RoutesV Tr))
           (id (IdV tr)))
      (cons (list Id (caar routes) frm (car (last (car routes))))
            (ToMissives (cdr TrLst))))))

(defthm correctroutesp-=>-tomissives
  (implies (and (CorrectRoutesp TrLst M NodeSet)
                (Missivesp M NodeSet)
                (TrLstp TrLst))
           (equal (ToMissives TrLst) M)))

(defthm M-ids-ToMissives-V-ids
  (equal (M-ids (ToMissives x)) (V-ids x)))

(defthm CorrectRoutesp-member-equal
  (implies (and (correctRoutesp TrLst (ToMissives TrLst) NodeSet)
                (TrLstp TrLst)
                (member-equal e (v-ids TrLst)))
           (checkroutes (nth 2 (assoc-equal e TrLst))
                        (assoc-equal e (ToMissives TrLst))
                        NodeSet)))

;;                   EXTRACT SUBLIST

(defun extract-sublst (Lst Ids)
  ;; extracts the element with the Id in Ids
  ;; the output is ordered according to Ids
  (if (endp Ids)
      nil
    (append (list (assoc-equal (car Ids) Lst))
            (extract-sublst Lst (cdr Ids)))))


;; for the proof of the correctness of GeNOC
;; two important lemmas are needed

;; the first one rewrites (ToMissives (extract-sublst ..))
;; to (extract-sublst (tomissives) ... )

(defthm ToMissives-append
  ;; we first link ToMissives and append
  (equal (ToMissives (append A B))
         (append (ToMissives A) (ToMissives B))))

(defthm member-equal-assoc-equal-not-nil
  ;; if e is an Id of a travel of L
  ;; then (assoc-equal e L) is not nil
  (implies (and (member-equal e (V-ids L))
                (TrLstp L))
           (assoc-equal e L)))

(defthm ToMissives-assoc-equal
  ;; if (assoc-equal e L) is not nil then we can link
  ;; assoc-equal and ToMissives as follows:
  ;; (this lemma is needed to prove the next defthm)
  (implies (assoc-equal e L)
           (equal (ToMissives (list (assoc-equal e L)))
                  (list (assoc-equal e (ToMissives L))))))

(defthm ToMissives-extract-sublst
  ;; now we prove our main lemma
  (implies (and (subsetp ids (V-ids L))
                (TrLstp L))
           (equal (ToMissives (extract-sublst L ids))
                  (extract-sublst (ToMissives L) ids)))
  :otf-flg t
  :hints (("GOAL"
           :do-not '(eliminate-destructors generalize)
           :induct (extract-sublst L ids)
           :do-not-induct t
           :in-theory (disable ToMissives append))))

;; the second lemma we need, allow us to cancel
;; one successive call of extract-sublst

(defthm member-equal-assoc-equal-not-nil-m-ids
  ;; if a is ain the ids of L then (assoc-equal e L)
  ;; is not nil
  (implies (and (member-equal e (M-ids L))
                (validfields-m L))
           (assoc-equal e L)))

(defthm member-equal-M-ids-assoc-equal
  ;; obviously if e in not in the ids of L
  ;; then (assoc-equal e L) is nil
  (implies (not (member-equal e (M-ids L)))
           (not (assoc-equal e L))))

(defthm Missivesp-not-assoc-equal
  ;; if M is Missivesp then nil is not a key in L
  (implies (ValidFields-M M)
           (not (assoc-equal nil M))))

(defthm assoc-equal-not-nil
  ;; if (assoc-equal e L) is not nil, then
  ;; its car is e !!
  (implies (assoc-equal e L)
           (equal (car (assoc-equal e L))
                  e)))

(defthm assoc-equal-extract-sublst-M-lemma
  ;; if e is not in id1 there is no key equal to e
  ;; after filtering according to id1
  (implies (and (not (member-equal e id1))
                (ValidFields-M M))
           (not (assoc-equal e (extract-sublst M id1)))))

(defthm assoc-equal-extract-sublst-M
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

(defthm extract-sublst-cancel-M
  ;; and now we can prove our second main lemma
  (implies (and (subsetp id2 id1)
                (ValidFields-M M))
           (equal (extract-sublst (extract-sublst M id1) id2)
                  (extract-sublst M id2))))

;; Finally, we prove that the correctness of the routes
;; is preserved by extract-sublst

(defthm extract-sublst-identity
  (implies (TrLstp TrLst)
           (equal (extract-sublst TrLst (V-ids TrLst))
                  TrLst)))

(defthm assoc-equal-tomissives-not-nil
  ;; if e is in the ids of L then there is a key equal to
  ;; e in (ToMissives L)
  (implies (and (TrLstp L) (member-equal e (V-ids L)))
           (assoc-equal e (ToMissives L))))

(defthm ToMissives-CorrectRoutesp-Extract-sublst
  ;; we prove the current lemma
  (implies (and (subsetp ids (V-ids TrLst))
                (TrLstp TrLst)
                (CorrectRoutesp TrLst (ToMissives TrLst) NodeSet))
           (CorrectRoutesp (extract-sublst TrLst ids)
                           (ToMissives (extract-sublst TrLst ids))
                           NodeSet)))

;;                  NOT IN

(defun not-in (x y)
  (if (or (endp x) (endp y))
      t
    (and (not (member (car x) y))
         (not-in (cdr x) y))))


;;                 SUBSETP
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
  (implies (and (subsetp x NodeSet) (consp x))
           (member-equal (car (last x)) NodeSet)))

;; Finally, we prove that converting a list of travels
;; to a list of missives gives something that is recoginized
;; by Missivesp
(defthm checkroutes-caar
  (implies (and (checkroutes Routes M NodeSet)
                (validfield-route Routes) (consp routes))
           (member-equal (caar routes) NodeSet)))

(defthm checkroutes-car-last-car
  (implies (and (checkroutes Routes M NodeSet)
                (validfield-route Routes) (consp routes))
           (member-equal (car (last (car routes))) NodeSet)))

(defthm Missivesp-ToMissives
  (implies (and (correctroutesp TrLst (ToMissives TrLst) NodeSet)
                (TrLstp TrLst))
           (Missivesp (ToMissives TrLst) NodeSet)))

