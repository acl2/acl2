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
    (and (not (member-equal (car x) y))
         (not-in (cdr x) y))))


(defthm no-dups-append
  (equal (no-duplicatesp-equal (append x y))
         (and (no-duplicatesp-equal x)
              (no-duplicatesp-equal y)
              (not-in x y))))


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
  (equal (subsetp (append x y) z)
         (and (subsetp x z)
              (subsetp y z))))

(defthm subsetp-trans
  ;; transitivity of subsetp
  (implies (and (subsetp x y)
                (subsetp y z))
           (subsetp x z)))



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

(defthm m-ids-tomissives
  (equal (M-ids (ToMissives m)) (Tm-ids m)))

(defthm fwd-missivesp
  ;; as missivesp is disabled we prove this rule to add
  ;; the content of missivesp as hypotheses
  (implies (missivesp M NodeSet)
           (and (Validfields-M M )
                (subsetp (M-orgs M) NodeSet)
                (subsetp (M-dests M) NodeSet)
                (True-listp M)
                (No-duplicatesp-equal (M-ids M))))
  :rule-classes :forward-chaining)


(defthm tomissives-truelistp
  (implies (Tmissivesp M nodeset)
           (true-listp (tomissives m))))

(defthm to-missives-missivesp
  (implies (TMissivesp m nodeset)
           (Missivesp (ToMissives m) NodeSet)))

(defthm tomissives-len-equal
  (equal  (len (tomissives x))
          (len x)))

(defthm m-ids-append-invert
  ;; append out of the mids
  (equal (m-ids (append a b))
         (append (m-ids a) (m-ids b))))

(defthm rewrite-missivesp-append
  (implies (true-listp x)
           (equal (missivesp (append x y) nodeset)
                  (and (missivesp x nodeset)
                       (missivesp y nodeset)
                       (not-in (m-ids x) (m-ids y))))))



(defthm memberequal-implies-id-member-missives ;OK
  ;; member of a list then the id of the element is a member of the
  ;; ids of the list
  (implies (member-equal  x l)
           (member-equal (idm x) (m-ids l))))

(defthm missivesy-missives-cdry
  ;; missivesp y then missivesp cdr y
  (implies (missivesp y nodeset)
           (missivesp (cdr y) nodeset)))

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
           (curr (CurV tr))
           (dest (DestV tr))
           (id (IdV tr))
           (Flit (FlitV tr))
           (Time (TimeV tr))
           (Loc (LocV tr)))
      (cons (list id org curr frm dest Flit time loc)
            (ToTMissives (cdr TrLst))))))

(defun equal-locs (trlst TM)
  (if (endp TrLst)
      (if (endp TM)
          t
        nil)
      (and (equal (LocV (car trlst)) (LocTM (car TM)))
           (equal-locs (cdr trlst) (cdr TM)))))
(defthm TM-ids-ToMissives-V-ids    ;; OK
  (equal (TM-ids (ToTMissives x)) (V-ids x)))


;; for the proof of the correctness of GeNOC
;; two important lemmas are needed

;; the first one rewrites (ToMissives (extract-sublst ..))
;; to (extract-sublst (tomissives) ... )
(defthm ToTMissives-append    ;; OK
  ;; we first link ToTMissives and append
  (equal (ToTMissives (append A B))
         (append (ToTMissives A) (ToTMissives B))))

(defthm TMissivesp-ToMissives-bis
  (implies (trlstp trlst nodeset)
           (TMissivesp (ToTMissives TrLst) NodeSet)))

(defthm fwd-tmissivesp
  ;; as Tmissivesp is disabled we prove this rule to add
  ;; the content of Tmissivesp as hypotheses
  (implies (Tmissivesp M NodeSet)
           (and (Validfields-TM M nodeset)
                (subsetp (TM-orgs M) NodeSet)
                (subsetp (TM-curs M) NodeSet)
                (subsetp (TM-dests M) NodeSet)
                (True-listp M)
                (No-duplicatesp-equal (TM-ids M))))
  :rule-classes :forward-chaining)


(defthm tm-ids-append-invert
  (equal (tm-ids (append a b))
         (append (tm-ids a) (tm-ids b))))

(defthm memberequal-implies-id-member ;OK
  ;; the IDs of a member of a list are part of the ids of this list
  (implies (member-equal  x l)
           (member-equal (idtm x) (tm-ids l))))

(defthm tmissivesy-tmissives-cdry
  (implies (tmissivesp y nodeset)
           (tmissivesp (cdr y) nodeset)))


(defthm tm-ids-append-->append-tm-ids
  (equal (tm-ids (append x y))
         (append (tm-ids x) (tm-ids y))))
(defthm rewrite-nodups-tm-ids-append
  (equal (no-duplicatesp-equal (tm-ids (append x y)))
         (and (no-duplicatesp-equal (tm-ids x))
              (no-duplicatesp-equal (tm-ids y))
              (not-in (tm-ids x) (tm-ids y)))))
(in-theory (disable tm-ids-append-->append-tm-ids))
(defthm rewrite-validfields-tm-append
  (equal (validfields-tm (append x y) nodeset)
         (and (validfields-tm x nodeset)
              (validfields-tm y nodeset))))
(defthm tm-orgs-append
  (equal (tm-orgs (append x y))
         (append (tm-orgs x) (tm-orgs y))))
(defthm tm-curs-append
  (equal (tm-curs (append x y))
         (append (tm-curs x) (tm-curs y))))
(defthm tm-dests-append
  (equal (tm-dests (append x y))
         (append (tm-dests x) (tm-dests y))))
(in-theory (disable subsetp-append))
(defthm rewrite-subsetp-append-l
  (equal (subsetp (append x y) z)
         (and (subsetp x z)
              (subsetp y z))))
(defthm rewrite-tmissivesp-append
  (implies (true-listp tmissives1)
           (equal (tmissivesp (append tmissives1 tmissives2) nodeset)
                  (and (tmissivesp tmissives1 nodeset)
                       (tmissivesp tmissives2 nodeset)
                       (not-in (tm-ids tmissives1) (tm-ids tmissives2))))))
;;|------------------------------|
;;|                                 |
;;|              Travels            |
;;|                                 |
;;|------------------------------|

(defthm v-ids-append-->append-v-ids
  (equal (v-ids (append a b))
         (append (v-ids a) (v-ids b))))
(in-theory (disable v-ids-append-->append-v-ids))
(defthm append-v-ids-->v-ids-append
  (equal (append (v-ids trlst1) (v-ids trlst2))
         (v-ids (append trlst1 trlst2))))
(defthm rewrite-trlstp-append
  (implies (true-listp x)
           (equal (trlstp (append x y) nodeset)
                  (and (trlstp x nodeset)
                       (trlstp y nodeset)
                       (not-in (v-ids x) (v-ids y)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (locv v-ids-append-->append-v-ids) (append-v-ids-->v-ids-append)))))

(defthm fwd-trlstp
  ;; because we disable trlstp, this rule adds its content
  ;; as hypotheses
  (implies (TrLstp TrLst nodeset)
           (and (validfields-trlst trlst nodeset)
                (true-listp trlst)
                (no-duplicatesp-equal (v-ids trlst))))
  :rule-classes :forward-chaining)

;;|------------------------------|
;;|                                 |
;;|                 rev                 |
;;|------------------------------|
(defun rev (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))

(defthm subsetp-rev-l
  (equal (subsetp (rev x) y)
         (subsetp x y)))
(defthm member-rev
  (iff (member-equal a (rev x))
       (member-equal a x)))
(defthm subsetp-rev-r
  (equal (subsetp x (rev y))
         (subsetp x y)))


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


;;|------------------------------|
;;|                                 |
;;|            ntkstate                 |
;;|                                 |
;;|------------------------------|

;; valid ntkstate
(defthm validstate-entry-implies-coord-and-buffer
  (implies (and (validstate-entryp x)
                (consp x))
           (and (validcoord (car x))
                (validbuffer (cadr x)))))#|ACL2s-ToDo-Line|#

