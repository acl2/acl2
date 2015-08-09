#|$ACL2s-Preamble$;
;; Amr Helmy
;; instance of interfaces
;; October 26th 2007
;; File: Interfaces-computes.lisp
;; Amr helmy
;; 31st october 2007

(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")
(include-book "GeNoC-misc")
(include-book "GeNoC-interfaces")
(defun p2psend2 (msg) msg)
(defun p2precv2 (frm) frm)



;;|-----------------------------------------------------------------------|
;;|   ComputeTmissives & Computeresults                                          |
;;|-----------------------------------------------------------------------|

(defun computetmissives (transactions)
  ;; apply the function p2psend to build a list of tmissives
  ;; from a list of transactions
  (if (endp transactions)
      nil
    (let* ((trans (car transactions))
           (id (idt trans))
           (org (orgt trans))
           (msg (msgt trans))
           (dest (destt trans))
           (flit (flitt trans))
           (time (timet trans)))
      (cons (list id org org (p2psend2 msg) dest flit time)
            (computetmissives (cdr transactions))))))

(defthm tm-ids-computestmissives       ;; ok
  ;; lemma for the next defthm
  (equal (tm-ids (computetmissives trs))
         (t-ids trs)))

(defthm tm-dests-computetmissives      ;; ok
  (equal (tm-dests (computetmissives trs))
         (t-dests trs)))

(defthm tm-orgs-computetmissives      ;; ok
  (equal (tm-orgs (computetmissives trs))
         (t-orgs trs)))

(defthm tmissivesp-computetmissives     ;; ok
  (implies (transactionsp trs nodeset)
           (tmissivesp (computetmissives trs) nodeset)))

(defthm tmissivesp-computetmissives-extract-sublst
  (implies (and (transactionsp trs nodeset)
                (no-duplicatesp-equal ids)
                (subsetp ids (tm-ids (computetmissives trs))))
           (tmissivesp (extract-sublst (computetmissives trs) ids) nodeset)))

(defthm m-ids-computtmisives-tomissives ;;change name
  (equal (m-ids (tomissives (computetmissives trs))) (t-ids trs)))

(defthm m-dests-computtmisives-tomissives
  (equal (m-dests (tomissives (computetmissives trs))) (t-dests trs)))

;; the next four lemmas are similar to those used to prove
;; the lemma tomissives-extract-sublst .... (proof by analogy)

(defthm computetmissives-append       ;; ok
  (equal (computetmissives (append a b))
         (append (computetmissives a) (computetmissives b))))

(defthm member-equal-assoc-equal-not-nil-t-ids
  ;; if e is an id of a travel of l
  ;; then (assoc-equal e l) is not nil
  (implies (and (member-equal e (t-ids trs))
                (validfields-t trs))
           (assoc-equal e trs)))

(defthm computetmissives-assoc-equal       ;; ok
  ;; if (assoc-equal e l) is not nil then we can link
  ;; assoc-equal and computetmissives as follows:
  ;; (this lemma is needed to prove the next defthm)
  (implies (assoc-equal e l)
           (equal (computetmissives (list (assoc-equal e l)))
                  (list (assoc-equal e (computetmissives l))))))

(defthm computetmissives-extract-sublst      ;; ok
  ;; calls of computetmissives are moved into calls
  ;; of extract-sublst
  (implies (and (subsetp ids (t-ids trs))
                (validfields-t trs))
           (equal (computetmissives (extract-sublst trs ids))
                  (extract-sublst (computetmissives trs) ids)))
  :otf-flg t
  :hints (("goal"
           :induct (extract-sublst trs ids)
           :do-not-induct t
           :in-theory (disable computetmissives append))))

(defthm m-dest-t-dests-extract-sublst-inst      ;; ok
  (implies (and (subsetp ids (t-ids trs))
                (validfields-t trs))
           (equal (tm-dests (extract-sublst (computetmissives trs) ids))
                  (t-dests (extract-sublst trs ids))))
  :hints (("goal"
           :do-not-induct t
           :use (:instance tm-dests-computetmissives
                           (trs (extract-sublst trs ids)))
           :in-theory (disable tm-dests-computetmissives))))


;; computeresults
;; -------------
(defun computeresults (trlst)
  ;; apply the function p2precv to build a list of results
  ;; from a list of travels
  (if (endp trlst)
      nil
    (let* ((tr (car trlst))
           (id (idv tr))
           (r (car (routesv tr)))
           (dest (car (last r)))
           (frm (frmv tr))
           (flit (flitv tr)))
      (cons (list id dest (p2precv2 frm) flit)
            (computeresults (cdr trlst))))))

(defthm r-ids-computeresults
  (equal (r-ids (computeresults x))
         (v-ids x)))