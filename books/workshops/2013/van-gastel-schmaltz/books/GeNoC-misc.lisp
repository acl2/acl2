#|$ACL2s-Preamble$;
;; Amr HELMY
;; Miscelaneous definitions and lemmas

;;31st october 2007
;; File: GeNoC-misc.lisp
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "GeNoC-types")
(include-book "make-event/defspec"  :dir :system)

;;
;;  nil_list
;;
(defun nil_list (n)
  (if (zp n)
    nil
    (cons nil (nil_list (1- n)))))

;;|-------------------------------------------------|
;;|                                                    |
;;|                    Not-in                            |
;;|                                                    |
;;|-------------------------------------------------|
(defun not-in-test (x y)
  (not (member-equal x y)))
(create-for-all not-in-test :name not-in :extra (y))
(defcong permp equal (not-in x y) 2)
(defthm not-in-append-alt
  (equal (not-in x (append y z))
         (and (not-in x y)
              (not-in x z))))
(defthm not-in-empty-list-always-true
  (implies (endp y)
           (not-in x y)))
(defthm subset-not-in
  (implies (and (subsetp x y)
                (not-in a y))
           (not-in a x)))
(defcong permp equal (not-in x y) 2)
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

(defthm subsetp-cons-cdr-part
  (implies (subsetp (cons x xs) y)
           (subsetp xs y)))

(defthm subsetp-cons-car-part
  (implies (subsetp (cons x xs) y)
           (member-equal x y)))

;;|---------------------------------|
;;|                                    |
;;|             tomissives             |
;;|                                 |
;;|---------------------------------|
(defun ToMissive-TM (tr)
    (let* ((id (IdTm tr))
           (org (OrgTm tr))
           (frm (FrmTm Tr))
           ;(dest (DestTm tr))
           (Flit (FlitTM tr))
           (time (timeTM tr)))
     (M Id org frm Flit time)))
(create-map tomissive-TM :name tomissives)

;; for the proof of the correctness of GeNOC
;; two important lemmas are needed

;; the first one rewrites (ToMissives (extract-sublst ..))
;; to (extract-sublst (tomissives) ... )
(defthm m-ids-tomissives
  (equal (M-ids (ToMissives m)) (Tm-ids m))
    :hints (("Goal" :in-theory (e/d (v-id M)()) ))
)

(defthm fwd-missivesp
  ;; as missivesp is disabled we prove this rule to add
  ;; the content of missivesp as hypotheses
  (implies (missivesp M NodeSet)
           (and (Validfields-M M )
                (subsetp (M-orgs M) NodeSet)
                ;(subsetp (M-dests M) NodeSet)
                (True-listp M)
                (No-duplicatesp-equal (M-ids M))))
  :rule-classes :forward-chaining)


(defthm tomissives-truelistp
  (implies (Tmissivesp M nodeset)
           (true-listp (tomissives m))))

(defthm to-missives-missivesp
  (implies (TMissivesp tmissives nodeset)
           (Missivesp (ToMissives tmissives) NodeSet))
      :hints (("Goal" :in-theory (e/d (v-id m-_id M M-p weak-M-p M-frame TM-frame M-flit M-time M-org)()) ))
)

(defthm rewrite-missivesp-append
  (implies (true-listp x)
           (equal (missivesp (append x y) nodeset)
                  (and (missivesp x nodeset)
                       (missivesp y nodeset)
                       (not-in (m-ids x) (m-ids y))))))

(defthm missivesy-missives-cdry
  ;; missivesp y then missivesp cdr y
  (implies (missivesp y nodeset)
           (missivesp (cdr y) nodeset)))

;;|------------------------------|
;;|                              |
;;|            toTmissives                 |
;;|                                 |
;;|------------------------------|

(defun ToTMissive-V (tr)
    (let ((frm (FrmV tr))
           (org (OrgV tr))
           (curr (CurV tr))
           ;(dest (DestV tr))
           (id (IdV tr))
           (Flit (FlitV tr))
           (Time (TimeV tr))
           (Loc (LocV tr)))
      (TM id org curr frm Flit time loc)))

(create-map ToTMissive-V :name ToTMissives)

(defun tomissive-V (v)
  (M (IdV v) (OrgV v) (FrmV v) (FlitV v) (TimeV v)))

(defun equal-locs (trlst TM)
  (if (endp TrLst)
      (if (endp TM)
          t
        nil)
      (and (equal (LocV (car trlst)) (LocTM (car TM)))
           (equal-locs (cdr trlst) (cdr TM)))))
(defthm TM-ids-ToMissives-V-ids    ;; OK
  (equal (TM-ids (ToTMissives x)) (V-ids x))
      :hints (("Goal" :in-theory (e/d (v-id TM)()) ))
)


;; for the proof of the correctness of GeNOC
;; two important lemmas are needed

;; the first one rewrites (ToMissives (extract-sublst ..))
;; to (extract-sublst (tomissives) ... )
(defthm TMissivesp-ToMissives-bis
  (implies (trlstp trlst nodeset)
           (TMissivesp (ToTMissives TrLst) NodeSet))
        :hints (("Goal" :in-theory (e/d (v-id TM TM-p weak-TM-p TM-frame TM-flit TM-time TM-org TM-cur TM-loc)()) ))
        )


(defthm fwd-tmissivesp
  ;; as Tmissivesp is disabled we prove this rule to add
  ;; the content of Tmissivesp as hypotheses
  (implies (Tmissivesp M NodeSet)
           (and (Validfields-TM M nodeset)
                (subsetp (TM-orgs M) NodeSet)
                (subsetp (TM-curs M) NodeSet)
                ;(subsetp (TM-dests M) NodeSet)
                (True-listp M)
                (No-duplicatesp-equal (TM-ids M))))
  :rule-classes :forward-chaining)

(defthm tmissivesy-tmissives-cdry
  (implies (tmissivesp y nodeset)
           (tmissivesp (cdr y) nodeset)))

(defthm rewrite-nodups-tm-ids-append
  (equal (no-duplicatesp-equal (tm-ids (append x y)))
         (and (no-duplicatesp-equal (tm-ids x))
              (no-duplicatesp-equal (tm-ids y))
              (not-in (tm-ids x) (tm-ids y)))))
(defthm rewrite-validfields-tm-append
  (equal (validfields-tm (append x y) nodeset)
         (and (validfields-tm x nodeset)
              (validfields-tm y nodeset))))
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
(defthm rewrite-trlstp-append
  (implies (true-listp x)
           (equal (trlstp (append x y) nodeset)
                  (and (trlstp x nodeset)
                       (trlstp y nodeset)
                       (not-in (v-ids x) (v-ids y)))))
  :otf-flg t)

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
;;|            ntkstate                 |
;;|                                 |
;;|------------------------------|

;; valid ntkstate
(defthm validstate-entry-implies-coord-and-buffer
  (implies (and (validstate-entryp x)
                (consp x))
           (and (validcoord (car x))
                (validbuffer (cadr x)))))#|ACL2s-ToDo-Line|#


