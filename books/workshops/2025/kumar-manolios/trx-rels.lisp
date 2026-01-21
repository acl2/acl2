(in-package "ACL2S")
(include-book "good-fn")

(encapsulate ()
  ;; Find forwarding peer that will forward m in s
  (property prop=in-m-cdr-pending (s :s-fn m :mssg)
    :h (^ (in m (union-set (mget :pending (cdr (car s)))
                           (fn-pending-mssgs (cdr s))))
          (not (in m (mget :pending (cdr (car s))))))
    (in m (fn-pending-mssgs (cdr s)))
    :hints (("Goal" :use ((:instance in-union2
                                     (x (mget :pending (cdr (car s))))
                                     (y (fn-pending-mssgs (cdr s))))))))
  (local 
   (property h0 (s :s-fn m :mssg)
     :h (in m (isort-set (mget :pending (cdr (car s)))))
     (in m (mget :pending (cdr (car s))))))

  (local
   (in-theory (enable fn-pending-mssgs
                      new-fn-mssgp
                      acl2::maximal-records-theory)))

  (property prop=new-fn-mssgp1 (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s))))
    (! (new-fn-mssgp m s)))
  
  (property prop=new-fn-mssgp2 (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :seen (mget p s))))
    (! (new-fn-mssgp m s)))
  
  (definec find-forwarder (s :s-fn m :mssg) :peer
    :ic (in m (fn-pending-mssgs s))
    :oc (^ (mget (find-forwarder s m) s)
           (in m (mget :pending (mget (find-forwarder s m) s)))
           (! (new-fn-mssgp m s)))
    :function-contract-hints (("Goal" :induct (find-forwarder s m)))
    (match s
      (((p . &)) p)
      (((p . pst) . rst)
       (if (in m (mget :pending pst))
           p
         (find-forwarder rst m))))))

(definecd rel-skip-bn (s u :s-bn) :bool
  (== u s))

(definec brd-receivers-bn (m :mssg s :s-bn) :lop
  (match s
    (() ())
    (((p . pst) . rst)
     (if (in m (mget :seen pst))
         (cons p (brd-receivers-bn m rst))
       (brd-receivers-bn m rst)))))


(property prop=brd-receivers-bn-fn (m :mssg ms :lom s :s-fn)
  :h (! (in m ms))
  (== (brd-receivers m s)
      (brd-receivers-bn m (f2b-help s ms)))
  :instructions
  (:pro
   :induct :pro
   (:claim (== (brd-receivers m (cdr s))
               (brd-receivers-bn m (f2b-help (cdr s) ms))))
   (:claim (s-bnp (f2b-help s ms)))
   (:claim (== (f2b-help s ms)
               (cons (cons (car (car s))
                           (f2b-st (cdr (car s)) ms))
                     (f2b-help (cdr s) ms)))
           :hints (("Goal" :use ((:instance prop=f2b-helper-def)))))
   (:demote 9)
   (:equiv (f2b-help s ms)
           (cons (cons (car (car s))
                       (f2b-st (cdr (car s)) ms))
                 (f2b-help (cdr s) ms)))
   :pro
   (:dv 2) (:r brd-receivers-bn) :s :up
   (:dv 1) (:r brd-receivers) :s :up

   (= (cdr (car (f2b-help s ms)))
      (f2b-st (cdr (car s)) ms)
      :hints (("Goal" :use ((:instance prop=f2b-helper-cdar)))))
   (=  (mget :seen (f2b-st (cdr (car s)) ms))
       (set-difference-equal (mget :seen (cdr (car s))) ms)
       :hints (("Goal" :use ((:instance prop=f2b-st-check
                                        (ps (cdr (car s))))))))
   (= (in m (set-difference-equal (mget :seen (cdr (car s))) ms))
      (in m (mget :seen (cdr (car s))))
      :hints (("Goal" :use ((:instance in-diff1
                                       (x (mget :seen (cdr (car s))))
                                       (y ms))))))
   (= (car (car (f2b-help s ms)))
      (car (car s))
      :hints (("Goal" :use ((:instance prop=f2b-helper-caar)))))
   :s
   (:prove :hints (("Goal" :in-theory (enable brd-receivers f2b-help))))))



(defdata maybe-mssg (v nil mssg))

(property prop=cadr-sbn (s :s-bn)
  :h (consp s)
  (ps-bnp (cdar s))
  :hints (("Goal" :in-theory (enable s-bnp))))

(property prop=lomp-seen-diff-bn (pst qst :ps-bn)
  :check-contracts? nil
  :h (set-difference-equal (mget :seen qst) (mget :seen pst))
  (mssgp (car (set-difference-equal (mget :seen qst) (mget :seen pst))))
  :hints (("Goal" :in-theory (enable ps-bnp))))

(definec br-mssg-witness (s u :s-bn) :maybe-mssg
  :function-contract-hints (("Goal" :in-theory (enable s-bnp ps-bnp)))
  (cond
   ((v (endp s) (endp u)) nil)
   ((== (car s) (car u)) (br-mssg-witness (cdr s) (cdr u)))
   (t (car (set-difference-equal (mget :seen (cdar u))
                                 (mget :seen (cdar s)))))))


(definecd rel-broadcast-partial-bn (s u :s-bn) :bool
  (^ (br-mssg-witness s u)
     (new-bn-mssgp (br-mssg-witness s u) s)
     (== u (broadcast-partial (br-mssg-witness s u)
                              (brd-receivers-bn (br-mssg-witness s u) u)
                              s))))


(defdata maybe-ptops (v nil (cons peer lot)))

(property prop=lomp-subs-diff-bn (pst qst :ps-bn)
  :check-contracts? nil
  :h (set-difference-equal (mget :subs qst) (mget :subs pst))
  (lotp (set-difference-equal (mget :subs qst) (mget :subs pst)))
  :hints (("Goal" :in-theory (enable ps-bnp))))
  
(definec bn-topics-witness (s u :s-bn) :maybe-ptops
  :function-contract-hints (("Goal" :in-theory (enable s-bnp ps-bnp)))
  (cond
   ((v (endp s) (endp u)) nil)
   ((== (car s) (car u)) (bn-topics-witness (cdr s) (cdr u)))
   ((^ (== (caar s)
           (caar u))
       (set-difference-equal (mget :subs (cdar u))
                             (mget :subs (cdar s))))
    (cons (caar s)
          (set-difference-equal (mget :subs (cdar u))
                                (mget :subs (cdar s)))))
   (t nil)))

(encapsulate ()
  (local
   (in-theory (enable acl2::maximal-records-theory)))

  (local
   (property prop=bn-topics-witness-mget1 (s u :s-bn)
     :h (bn-topics-witness s u)
     (mget (car (bn-topics-witness s u)) s)
     :instructions
     (:pro
      (:induct (bn-topics-witness s u)) :bash
      :pro
      (= (car (bn-topics-witness s u)) (car (car s)))
      :prove
      :pro
      (:claim (bn-topics-witness (cdr s) (cdr u)))
      (:claim (mget (car (bn-topics-witness (cdr s) (cdr u)))
                    (cdr s)))
      (:dv 1 1) (:r bn-topics-witness) :s :top
      (:prove :hints (("Goal" :use ((:instance prop=mget-cdr-mget
                                               (p (car (bn-topics-witness
                                                        (cdr s) (cdr u)))))))))
      :bash
      )))

  (local
   (property prop=bn-topics-witness-mget2 (s u :s-bn)
     :h (bn-topics-witness s u)
     (mget (car (bn-topics-witness s u)) u)
     :instructions
     (:pro
      (:induct (bn-topics-witness s u)) :bash
      :pro
      (= (car (bn-topics-witness s u)) (car (car u)))
      :prove
      :pro
      (:claim (bn-topics-witness (cdr s) (cdr u)))
      (:claim (mget (car (bn-topics-witness (cdr s) (cdr u)))
                    (cdr u)))
      (:dv 1 1) (:r bn-topics-witness) :s :top
      (:prove :hints (("Goal" :use ((:instance prop=mget-cdr-mget
                                               (p (car (bn-topics-witness
                                                        (cdr s) (cdr u))))
                                               (s u))))))
      :bash
      )))

  (property prop=bn-topics-witness-mget (s u :s-bn)
    :h (bn-topics-witness s u)
    (^ (mget (car (bn-topics-witness s u)) s)
       (mget (car (bn-topics-witness s u)) u))))


(definecd rel-subscribe-bn (s u :s-bn) :bool
  (^ (bn-topics-witness s u)
     (mget (car (bn-topics-witness s u)) s)
     (== u (subscribe-bn (car (bn-topics-witness s u))
                         (cdr (bn-topics-witness s u))
                         s))))

(definecd rel-unsubscribe-bn (s u :s-bn) :bool
  (^ (bn-topics-witness u s)
     (mget (car (bn-topics-witness u s)) s)
     (== u (unsubscribe-bn (car (bn-topics-witness u s))
                           (cdr (bn-topics-witness u s))
                           s))))



(defdata maybe-ppsbn (v nil
                        (cons peer ps-bn)))

(definec bn-join-witness (s u :s-bn) :maybe-ppsbn
  (match (list s u)
    ((() ((q . qst) . &)) `(,q . ,qst))
    ((((p . pst) . rs1)
      ((q . qst) . rs2))
     (cond
      ((== `(,p . ,pst)
           `(,q . ,qst))
       (bn-join-witness rs1 rs2))
      ((!= q p)
       `(,q . ,qst))
      (t nil)))
    (& nil)))

(property prop=bn-join-witness-mget (s u :s-bn)
  :h (bn-join-witness s u)
  (== (mget (car (bn-join-witness s u)) u)
      (cdr (bn-join-witness s u)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))

(property prop=bn-join-witness-mset-pst (s :s-bn p :peer pst :ps-bn)
  :h (! (mget p s))
  (bn-join-witness s (mset p pst s))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))

(definecd rel-leave-bn (s u :s-bn) :bool
  (^ (bn-join-witness u s)
     (mget (car (bn-join-witness u s)) s)
     (== u (leave-bn (car (bn-join-witness u s)) s))))

(definecd rel-join-bn (s u :s-bn) :bool
  (^ (bn-join-witness s u)
     (b* ((p (car (bn-join-witness s u)))
          (pst (cdr (bn-join-witness s u))))
       (^ (! (mget p s))
          (== u (join-bn p
                         (mget :pubs pst)
                         (mget :subs pst)
                         s))))))

(definec rel-step-bn (s u :s-bn) :bool
  (v (rel-skip-bn s u)
     (rel-broadcast-partial-bn s u)
     (rel-subscribe-bn s u)
     (rel-unsubscribe-bn s u)
     (rel-leave-bn s u)
     (rel-join-bn s u)))

(property prop=empty-rel-step-bn (s u :s-bn)
  :h (^ (null s)
        (rel-step-bn s u))
  (v (rel-skip-bn s u)
     (rel-join-bn s u))
  :hints (("Goal" :in-theory (enable rel-skip-bn
                                     rel-subscribe-bn
                                     rel-broadcast-partial-bn
                                     rel-unsubscribe-bn
                                     rel-leave-bn
                                     rel-join-bn))))
                                     


(definecd rel-skip-fn (s u :s-fn) :bool
  (== u s))

(definec rel-produce-help-fn (s u :s-fn ms :lom) :bool
  (match ms
    (() nil)
    ((m . rst)
     (v (^ (produce-fn-pre m s)
           (== u (produce-fn m s)))
        (rel-produce-help-fn s u rst)))))

(property prop=rel-produce-help-fn (s u :s-fn m :mssg ms :lom)
  :h (^ (in m ms)
        (produce-fn-pre m s)
        (== u (produce-fn m s)))
  (rel-produce-help-fn s u ms)
  :hints (("Goal" :in-theory (disable produce-fn-pre))))

(definecd rel-produce-fn (s u :s-fn) :bool
  (rel-produce-help-fn s u (fn-pending-mssgs u)))




(definec rel-forward-help-fn (s u :s-fn ms :lom) :bool
  (match ms
    (() nil)
    ((m . rst)
     (v (^ (in m (fn-pending-mssgs s))
           (== u (forward-fn (find-forwarder s m) m s)))
        (rel-forward-help-fn s u rst)))))

(property prop=rel-forward-help-fn (s u :s-fn m :mssg ms :lom)
  :h (^ (in m ms)
        (in m (fn-pending-mssgs s))
        (== u (forward-fn (find-forwarder s m) m s)))
  (rel-forward-help-fn s u ms))
  
(definecd rel-forward-fn (s u :s-fn) :bool
    (rel-forward-help-fn s u (fn-pending-mssgs s)))



(definec fn-topics-witness (s u :s-fn) :maybe-ptops
  (bn-topics-witness (f2b s) (f2b u)))


;; (definec fn-topics-witness (s u :s-fn) :maybe-ptops
;;   :function-contract-hints (("Goal" :in-theory (enable s-fnp ps-fnp)))
;;   (cond
;;    ((v (endp s) (endp u)) nil)
;;    ((== (car s) (car u)) (fn-topics-witness (cdr s) (cdr u)))
;;    ((^ (== (caar s)
;;            (caar u))
;;        (set-difference-equal (mget :subs (cdar u))
;;                              (mget :subs (cdar s))))
;;     (cons (caar s)
;;           (set-difference-equal (mget :subs (cdar u))
;;                                 (mget :subs (cdar s)))))
;;    (t (fn-topics-witness (cdr s) (cdr u)))))

;; (encapsulate ()
;;   (local
;;    (in-theory (enable acl2::maximal-records-theory)))

;;   (local
;;    (property prop=fn-topics-witness-mget1 (s u :s-fn)
;;      :h (fn-topics-witness s u)
;;      (mget (car (fn-topics-witness s u)) s)
;;      :instructions
;;      (:pro
;;       (:induct (fn-topics-witness s u)) :bash
;;       :pro
;;       (= (car (fn-topics-witness s u)) (car (car s)))
;;       :prove
;;       :pro
;;       (:claim (fn-topics-witness (cdr s) (cdr u)))
;;       (:claim (mget (car (fn-topics-witness (cdr s) (cdr u)))
;;                     (cdr s)))
;;       (:dv 1 1) (:r fn-topics-witness) :s :top
;;       (:prove :hints (("Goal" :use ((:instance prop=mget-cdr-mget
;;                                                (p (car (fn-topics-witness
;;                                                         (cdr s) (cdr u)))))))))
;;       :bash
;;       )))

;;   (local
;;    (property prop=fn-topics-witness-mget2 (s u :s-fn)
;;      :h (fn-topics-witness s u)
;;      (mget (car (fn-topics-witness s u)) u)
;;      :instructions
;;      (:pro
;;       (:induct (fn-topics-witness s u)) :bash
;;       :pro
;;       (= (car (fn-topics-witness s u)) (car (car u)))
;;       :prove
;;       :pro
;;       (:claim (fn-topics-witness (cdr s) (cdr u)))
;;       (:claim (mget (car (fn-topics-witness (cdr s) (cdr u)))
;;                     (cdr u)))
;;       (:dv 1 1) (:r fn-topics-witness) :s :top
;;       (:prove :hints (("Goal" :use ((:instance prop=mget-cdr-mget
;;                                                (p (car (fn-topics-witness
;;                                                         (cdr s) (cdr u))))
;;                                                (s u))))))
;;       :bash
;;       )))

;;   (property prop=fn-topics-witness-mget (s u :s-fn)
;;     :h (fn-topics-witness s u)
;;     (^ (mget (car (fn-topics-witness s u)) s)
;;        (mget (car (fn-topics-witness s u)) u))))


;; (property prop=fn-topics-witness-eq-help (s u :s-fn ms :lom)
;;   (== (fn-topics-witness s u)
;;       (bn-topics-witness (f2b-help s ms)
;;                          (f2b-help u ms)))
;;   :instructions
;;   (:pro :induct :pro
;;         (:claim (equal (fn-topics-witness (cdr s) (cdr u))
;;                    (bn-topics-witness (f2b-help (cdr s) ms)
;;                                       (f2b-help (cdr u) ms))))
;;         (:casesplit (== (car s) (car u)))
;;         (= (fn-topics-witness s u)
;;            (fn-topics-witness (cdr s) (cdr u)))
;;         (:claim (== (f2b-help s ms)
;;                     (cons (cons (caar s)
;;                                 (f2b-st (cdar s) ms))
;;                           (f2b-help (cdr s) ms)))
;;                 :hints (("Goal" :use ((:instance
;;                                        prop=f2b-helper-def)))))
;;         (:claim (s-bnp (f2b-help s ms)))
;;         (:demote 10)
;;         (:equiv (f2b-help s ms)
;;                 (cons (cons (caar s)
;;                             (f2b-st (cdar s) ms))
;;                       (f2b-help (cdr s) ms)))
;;         (:claim (== (f2b-help u ms)
;;                     (cons (cons (caar s)
;;                                 (f2b-st (cdar u) ms))
;;                           (f2b-help (cdr u) ms)))
;;                 :hints (("Goal" :use ((:instance
;;                                        prop=f2b-helper-def (s u))))))
;;         (:claim (s-bnp (f2b-help u ms)))
;;         (:demote 11)
;;         (:equiv (f2b-help u ms)
;;                 (cons (cons (caar s)
;;                                 (f2b-st (cdar u) ms))
;;                           (f2b-help (cdr u) ms)))
;;         :pro
;;         (= (bn-topics-witness (cons (cons (car (car s))
;;                                       (f2b-st (cdr (car s)) ms))
;;                                 (f2b-help (cdr s) ms))
;;                           (cons (cons (car (car s))
;;                                       (f2b-st (cdr (car u)) ms))
;;                                 (f2b-help (cdr u) ms)))
;;            (bn-topics-witness (f2b-help (cdr s) ms)
;;                               (f2b-help (cdr u) ms)))
;;         :s

;;         (:casesplit (endp s))
;;         (= (f2b-help s ms) nil
;;            :hints (("Goal" :in-theory (enable f2b-help))))
;;         (= (fn-topics-witness s u) nil)
;;         :prove

;;         (:casesplit (^ (== (caar s)
;;                            (caar u))
;;                        (set-difference-equal (mget :subs (cdar u))
;;                                              (mget :subs (cdar s)))))
;;         (:dv 1) (:r fn-topics-witness) :s :up

;;         (:dv 2) (:r bn-topics-witness) :s :top

        
;;         (:claim (== (f2b-help s ms)
;;                     (cons (cons (caar s)
;;                                 (f2b-st (cdar s) ms))
;;                           (f2b-help (cdr s) ms)))
;;                 :hints (("Goal" :use ((:instance
;;                                        prop=f2b-helper-def)))))
;;         (:claim (s-bnp (f2b-help s ms)))
;;         (:demote 13)
;;         (:equiv (f2b-help s ms)
;;                 (cons (cons (caar s)
;;                                 (f2b-st (cdar s) ms))
;;                       (f2b-help (cdr s) ms)))
;;         :pro
;;         (:claim (== (f2b-help u ms)
;;                     (cons (cons (caar u)
;;                                 (f2b-st (cdar u) ms))
;;                           (f2b-help (cdr u) ms)))
;;                 :hints (("Goal" :use ((:instance
;;                                        prop=f2b-helper-def (s u))))))
;;         (:claim (s-bnp (f2b-help u ms)))
;;         (:demote 15)
;;         (:equiv (f2b-help u ms)
;;                 (cons (cons (caar u)
;;                                 (f2b-st (cdar u) ms))
;;                       (f2b-help (cdr u) ms)))
;;         :pro
;;         (:claim (set-difference-equal (mget :subs (f2b-st (cdr (car u)) ms))
;;                                       (mget :subs (f2b-st (cdr (car s)) ms)))
;;                 :hints (("Goal" :use ((:instance prop=f2b-st-check
;;                                                  (ps (cdr (car u))))
;;                                       (:instance prop=f2b-st-check
;;                                                  (ps (cdr (car s))))))))

;;         (:dv 2) :s
;;         (:equiv (f2b-help s ms)
;;                 (cons (cons (caar s)
;;                                 (f2b-st (cdar s) ms))
;;                       (f2b-help (cdr s) ms)))
;;         (= (car (cons (cons (car (car s))
;;                           (f2b-st (cdr (car s)) ms))
;;                       (f2b-help (cdr s) ms)))
;;            (cons (car (car s))
;;                  (f2b-st (cdr (car s)) ms)))
;;         (:claim (!= (f2b-st (cdr (car u)) ms)
;;                     (f2b-st (cdr (car s)) ms)))
;;         :s
;;         (= (mget :subs (f2b-st (cdr (car s)) ms))
;;            (mget :subs (cdr (car s)))
;;            :hints (("Goal" :use ((:instance prop=f2b-st-check
;;                                             (ps (cdr (car s))))))))
;;         (= (mget :subs (f2b-st (cdr (car u)) ms))
;;            (mget :subs (cdr (car u)))
;;            :hints (("Goal" :use ((:instance prop=f2b-st-check
;;                                             (ps (cdr (car u))))))))
;;         :top :s
        
;;         (= (fn-topics-witness s u)
;;            (fn-topics-witness (cdr s) (cdr u)))
;;         (:dv 2) (:r bn-topics-witness) :s :top
;;         (:claim (== (f2b-help s ms)
;;                     (cons (cons (caar s)
;;                                 (f2b-st (cdar s) ms))
;;                           (f2b-help (cdr s) ms)))
;;                 :hints (("Goal" :use ((:instance
;;                                        prop=f2b-helper-def)))))
;;         (:claim (s-bnp (f2b-help s ms)))
;;         (:demote 12)
;;         (:equiv (f2b-help s ms)
;;                 (cons (cons (caar s)
;;                                 (f2b-st (cdar s) ms))
;;                       (f2b-help (cdr s) ms)))
;;         :pro
;;         (:claim (== (f2b-help u ms)
;;                     (cons (cons (caar u)
;;                                 (f2b-st (cdar u) ms))
;;                           (f2b-help (cdr u) ms)))
;;                 :hints (("Goal" :use ((:instance
;;                                        prop=f2b-helper-def (s u))))))
;;         (:claim (s-bnp (f2b-help u ms)))
;;         (:demote 14)
;;         (:equiv (f2b-help u ms)
;;                 (cons (cons (caar u)
;;                                 (f2b-st (cdar u) ms))
;;                       (f2b-help (cdr u) ms)))
;;         :pro (:dv 2) :s

;;         (:casesplit (equal (car (f2b-help s ms))
;;                            (car (f2b-help u ms))))
;;         :s :top :s

;;         :s
;;         (:equiv (f2b-help s ms)
;;                 (cons (cons (car (car s))
;;                        (f2b-st (cdr (car s)) ms))
;;                       (f2b-help (cdr s) ms)))
;;         (:equiv (f2b-help u ms)
;;                 (cons (cons (car (car u))
;;                        (f2b-st (cdr (car u)) ms))
;;                  (f2b-help (cdr u) ms)))
;;         (= (car (car (cons (cons (car (car s))
;;                        (f2b-st (cdr (car s)) ms))
;;                       (f2b-help (cdr s) ms))))
;;            (car (car s)))
;;         (= (car (car (cons (cons (car (car u))
;;                        (f2b-st (cdr (car u)) ms))
;;                  (f2b-help (cdr u) ms))))
;;            (car (car u)))
;;         (= (cdr (car (cons (cons (car (car u))
;;                                             (f2b-st (cdr (car u)) ms))
;;                            (f2b-help (cdr u) ms))))
;;            (f2b-st (cdr (car u)) ms))
;;         (= (cdr (car (cons (cons (car (car s))
;;                                             (f2b-st (cdr (car s)) ms))
;;                            (f2b-help (cdr s) ms))))
;;            (f2b-st (cdr (car s)) ms))
;;    ))




;; (i-am-here)



(definecd rel-subscribe-fn (s u :s-fn) :bool
  (^ (fn-topics-witness s u)
     (mget (car (fn-topics-witness s u)) s)
     (== u (subscribe-fn (car (fn-topics-witness s u))
                         (cdr (fn-topics-witness s u))
                         s))))

(definecd rel-unsubscribe-fn (s u :s-fn) :bool
  (^ (fn-topics-witness u s)
     (mget (car (fn-topics-witness u s)) s)
     (== u (unsubscribe-fn (car (fn-topics-witness u s))
                           (cdr (fn-topics-witness u s))
                           s))))


(defdata maybe-ppsfn (v nil
                        (cons peer ps-fn)))

(property mset-psbn->psfn (pst :ps-bn tlm :topic-lop-map)
  :hints (("Goal" :in-theory (enable ps-bnp
                                     ps-fnp)))
  (ps-fnp (mset :0tag 'ps-fn
                (mset :nsubs tlm
                      pst))))


;; (definec fn-join-witness (s u :s-fn) :maybe-ppsfn
;;   (match (list s u)
;;     ((() ((q . qst) . &)) `(,q . ,qst))
;;     ((((p . pst) . rs1)
;;       ((q . qst) . rs2))
;;      (cond
;;       ((== `(,p . ,pst)
;;            `(,q . ,qst))
;;        (fn-join-witness rs1 rs2))
;;       ((!= q p)
;;        `(,q . ,qst))
;;       (t nil)))
;;     (& nil)))

;; (property prop=fn-join-witness-mget (s u :s-fn)
;;   :h (fn-join-witness s u)
;;   (== (mget (car (fn-join-witness s u)) u)
;;       (cdr (fn-join-witness s u)))
;;   :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))


;; (property prop=fn-join-witness-preserves-pubs-subs-help (s u :s-fn ms :lom)
;;   :check-contracts? nil
;;   :h (fn-join-witness s u)
;;   (^ (== (mget :pubs (cdr (fn-join-witness s u)))
;;          (mget :pubs (cdr (bn-join-witness (f2b-help s ms) (f2b-help u ms)))))
;;      (== (mget :subs (cdr (fn-join-witness s u)))
;;          (mget :subs (cdr (bn-join-witness (f2b-help s ms) (f2b-help u ms))))))
;;   :instructions
;;   (:pro :induct :bash
;;         :pro
;;         (:claim (== (f2b-help s ms)
;;                     (cons (cons (caar s)
;;                                 (f2b-st (cdar s) ms))
;;                           (f2b-help (cdr s) ms)))
;;                 :hints (("Goal" :use ((:instance prop=f2b-helper-def)))))
;;         (:claim (== (f2b-help u ms)
;;                     (cons (cons (caar u)
;;                                 (f2b-st (cdar u) ms))
;;                           (f2b-help (cdr u) ms)))
;;                 :hints (("Goal" :use ((:instance prop=f2b-helper-def
;;                                                  (s u))))))
;;         (:claim (s-bnp (cons (cons (caar s)
;;                                 (f2b-st (cdar s) ms))
;;                              (f2b-help (cdr s) ms))))
;;         (:claim (s-bnp (cons (cons (caar u)
;;                                 (f2b-st (cdar u) ms))
;;                              (f2b-help (cdr u) ms))))
;;         (:equiv (f2b-help s ms)
;;                 (cons (cons (caar s)
;;                             (f2b-st (cdar s) ms))
;;                       (f2b-help (cdr s) ms)))
;;         (:equiv (f2b-help u ms)
;;                 (cons (cons (caar u)
;;                             (f2b-st (cdar u) ms))
;;                       (f2b-help (cdr u) ms)))

;;         (:claim (consp s))
;;         (= (cdr (bn-join-witness (cons (cons (car (car s))
;;                                              (f2b-st (cdr (car s)) ms))
;;                                        (f2b-help (cdr s) ms))
;;                                  (cons (cons (car (car u))
;;                                              (f2b-st (cdr (car u)) ms))
;;                                        (f2b-help (cdr u) ms))))
;;            (f2b-st (cdr (car u)) ms))
;;         (= (cdr (fn-join-witness s u)) (cdr (car u)))
;;         (:prove :hints (("Goal" :use ((:instance prop=f2b-st-check
;;                                                  (ps (cdr (car s))))))))

;;         :pro
;;         (:claim (== (f2b-help s ms)
;;                     (cons (cons (caar s)
;;                                 (f2b-st (cdar s) ms))
;;                           (f2b-help (cdr s) ms)))
;;                 :hints (("Goal" :use ((:instance prop=f2b-helper-def)))))
;;         (:claim (== (f2b-help u ms)
;;                     (cons (cons (caar u)
;;                                 (f2b-st (cdar u) ms))
;;                           (f2b-help (cdr u) ms)))
;;                 :hints (("Goal" :use ((:instance prop=f2b-helper-def
;;                                                  (s u))))))
;;         (:claim (s-bnp (cons (cons (caar s)
;;                                 (f2b-st (cdar s) ms))
;;                              (f2b-help (cdr s) ms))))
;;         (:claim (s-bnp (cons (cons (caar u)
;;                                 (f2b-st (cdar u) ms))
;;                              (f2b-help (cdr u) ms))))
;;         (:equiv (f2b-help s ms)
;;                 (cons (cons (caar s)
;;                             (f2b-st (cdar s) ms))
;;                       (f2b-help (cdr s) ms)))
;;         (:equiv (f2b-help u ms)
;;                 (cons (cons (caar u)
;;                             (f2b-st (cdar u) ms))
;;                       (f2b-help (cdr u) ms)))
;;         (:claim (== (car (car s))
;;                     (car (car u))))
;;         (:claim (== (cdr (car s))
;;                     (cdr (car u))))
;;         (:claim (== (f2b-st (cdr (car s)) ms)
;;                     (f2b-st (cdr (car u)) ms))
;;                 :hints (("Goal" :in-theory (enable f2b-st))))
;;         (= (bn-join-witness (cons (cons (car (car s))
;;                                         (f2b-st (cdr (car s)) ms))
;;                                   (f2b-help (cdr s) ms))
;;                             (cons (cons (car (car u))
;;                                         (f2b-st (cdr (car u)) ms))
;;                                   (f2b-help (cdr u) ms)))
;;            (bn-join-witness (f2b-help (cdr s) ms)
;;                             (f2b-help (cdr u) ms)))
;;         (= (fn-join-witness s u)
;;            (fn-join-witness (cdr s) (cdr u)))
;;         :prove

;;         :pro
;;         (= (f2b-help s ms) nil
;;            :hints (("Goal" :in-theory (enable f2b-help))))
;;         (:claim (== (f2b-help u ms)
;;                     (cons (cons (caar u)
;;                                 (f2b-st (cdar u) ms))
;;                           (f2b-help (cdr u) ms)))
;;                 :hints (("Goal" :use ((:instance prop=f2b-helper-def
;;                                                  (s u))))))
;;         (:claim (s-bnp (cons (cons (caar u)
;;                                 (f2b-st (cdar u) ms))
;;                              (f2b-help (cdr u) ms))))
;;         (:equiv (f2b-help u ms)
;;                 (cons (cons (caar u)
;;                             (f2b-st (cdar u) ms))
;;                       (f2b-help (cdr u) ms)))
;;         (= (cdr (bn-join-witness nil
;;                                  (cons (cons (car (car u))
;;                                              (f2b-st (cdr (car u)) ms))
;;                                        (f2b-help (cdr u) ms))))
;;            (f2b-st (cdr (car u)) ms))
;;         (= (cdr (fn-join-witness s u))
;;            (cdr (car u)))
;;          (:prove :hints (("Goal" :use ((:instance prop=f2b-st-check
;;                                                  (ps (cdr (car s))))))))))


;; (property prop=fn-join-witness-preserves-pubs-subs (s u :s-fn)
;;   :check-contracts? nil
;;   :h (^ (fn-join-witness s u)
;;         (== (fn-pending-mssgs s)
;;             (fn-pending-mssgs u)))
;;   (^ (== (mget :pubs (cdr (fn-join-witness s u)))
;;          (mget :pubs (cdr (bn-join-witness (f2b s) (f2b u)))))
;;      (== (mget :subs (cdr (fn-join-witness s u)))
;;          (mget :subs (cdr (bn-join-witness (f2b s) (f2b u))))))
;;   :instructions
;;   (:pro
;;    (= (f2b s)
;;       (f2b-help s (fn-pending-mssgs s))
;;       :hints (("Goal" :in-theory (enable f2b))))
;;    (= (f2b u)
;;       (f2b-help u (fn-pending-mssgs s))
;;       :hints (("Goal" :in-theory (enable f2b))))
;;    (:prove :hints (("Goal" :use ((:instance
;;                                   prop=fn-join-witness-preserves-pubs-subs-help
;;                                   (ms (fn-pending-mssgs s)))))))))

  

(definec fn-join-witness (s u :s-fn) :maybe-ppsfn
  :function-contract-hints
  (("Goal" :use ((:instance prop=mget-f2b=>mget
                            (p (car (bn-join-witness
                                     (f2b s) (f2b u))))
                            (s u)))))
  (b* ((res (bn-join-witness (f2b s) (f2b u)))
       ((when (null res)) nil))
    (cons (car res)
          (mget (car res) u))))


(property prop=fn-join-witness-preserves-pubs-subs (s u :s-fn)
  :h (fn-join-witness s u)
  (^ (== (mget :pubs (cdr (fn-join-witness s u)))
         (mget :pubs (cdr (bn-join-witness (f2b s) (f2b u)))))
     (== (mget :subs (cdr (fn-join-witness s u)))
         (mget :subs (cdr (bn-join-witness (f2b s) (f2b u))))))
  :instructions
  (:pro
   (:claim (bn-join-witness (f2b s) (f2b u)))
   (= (cdr (bn-join-witness (f2b s) (f2b u)))
      (mget (car (bn-join-witness (f2b s) (f2b u))) (f2b u))
      :hints (("Goal" :use ((:instance prop=bn-join-witness-mget
                                       (s (f2b s))
                                       (u (f2b u)))))))
   (= (car (bn-join-witness (f2b s) (f2b u)))
      (car (fn-join-witness s u)))
   (:claim (mget (car (fn-join-witness s u))
                 (f2b u)))
   (:claim (mget (car (fn-join-witness s u)) u))
   (= (f2b u)
      (f2b-help u (fn-pending-mssgs u))
      :hints (("Goal" :in-theory (enable f2b))))
   (= (mget (car (fn-join-witness s u))
            (f2b-help u (fn-pending-mssgs u)))
      (f2b-st (mget (car (fn-join-witness s u)) u)
              (fn-pending-mssgs u))
      :hints (("Goal" :use ((:instance prop=f2b-st-f2b-mget
                                       (p (car (fn-join-witness s u)))
                                       (s u)
                                       (ms (fn-pending-mssgs u)))))))
   (= (mget :pubs (f2b-st (mget (car (fn-join-witness s u)) u)
                          (fn-pending-mssgs u)))
      (mget :pubs (mget (car (fn-join-witness s u)) u))
      :hints (("Goal" :use ((:instance prop=f2b-st-check
                                       (ps (mget (car (fn-join-witness s u))
                                                 u))
                                       (ms (fn-pending-mssgs u)))))))
   (= (mget :subs (f2b-st (mget (car (fn-join-witness s u)) u)
                          (fn-pending-mssgs u)))
      (mget :subs (mget (car (fn-join-witness s u)) u))
      :hints (("Goal" :use ((:instance prop=f2b-st-check
                                       (ps (mget (car (fn-join-witness s u))
                                                 u))
                                       (ms (fn-pending-mssgs u)))))))
   :prove))



(definecd rel-leave-fn (s u :s-fn) :bool
  (^ (fn-join-witness u s)
     (mget (car (fn-join-witness u s)) s)
     (endp (mget :pending (mget (car (fn-join-witness u s)) s)))
     (== u (leave-fn (car (fn-join-witness u s)) s))))

(definec topic-lop-map->lop (x :topic-lop-map) :lop
  (match x
    (() ())
    (((& . ps) . rs)
     (app ps (topic-lop-map->lop rs)))))

(definecd rel-join-fn (s u :s-fn) :bool
  :body-contracts-hints (("Goal"
                          :use ((:instance prop=mget-f2b=>mget
                                           (p (car (fn-join-witness (f2b s) (f2b u))))
                                           (s u)))))
  (^ (fn-join-witness s u)
     (b* ((p (car (fn-join-witness s u)))
          (pst (cdr (fn-join-witness s u)))
          (nbrs (topic-lop-map->lop (mget :nsubs pst))))
       (^ (! (mget p s))
          (nin p nbrs)
          (== u (join-fn p
                         (mget :pubs pst)
                         (mget :subs pst)
                         nbrs
                         s))))))


(definec rel-step-fn (s u :s-fn) :bool
  (v (rel-skip-fn s u)
     (rel-produce-fn s u)
     (rel-forward-fn s u)
     (rel-subscribe-fn s u)
     (rel-unsubscribe-fn s u)
     (rel-leave-fn s u)
     (rel-join-fn s u)))

(property prop=empty-rel-produce-fn1 (s u :s-fn ms :lom)
  (! (rel-produce-help-fn nil u ms))) 

(property prop=empty-rel-produce-fn2 (u :s-fn)
  (! (rel-produce-fn nil u))
  :hints (("Goal" :in-theory (enable
                              rel-produce-fn))))
  
(property prop=empty-rel-step-fn (u :s-fn)
  :h (rel-step-fn nil u)
  (v (rel-skip-fn nil u)
     (rel-join-fn nil u))
  :hints (("Goal" :in-theory (enable rel-skip-fn
                                     rel-produce-help-fn
                                     rel-produce-fn
                                     rel-forward-fn
                                     rel-subscribe-fn
                                     rel-unsubscribe-fn
                                     rel-leave-fn
                                     rel-join-fn))))

(definec good-rel-step-fn (s u :s-fn) :bool
  (^ (good-s-fnp s)
     (good-s-fnp u)
     (rel-step-fn s u)))
