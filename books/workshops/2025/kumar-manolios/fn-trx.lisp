(in-package "ACL2S")
(include-book "utils")

(defdata ps-fn
  (record  (pubs . lot)
           (subs . lot)            ;; self subscriptions
           (nsubs . topic-lop-map) ;; nbr topic subscriptions
           (pending . lom)
           (seen . lom)))

(property ps-fn-check-prop (x :ps-fn)
  (^ (lomp (mget :seen x))
     (lomp (mget :pending x))
     (topic-lop-mapp (mget :nsubs x))
     (lotp (mget :subs x))
     (lotp (mget :pubs x)))
  :rule-classes :forward-chaining)

(defdata s-fn (map peer ps-fn))

(property s-fn-check (st :s-fn i :peer)
          (=> (mget i st)
              (ps-fnp (mget i st)))
          :rule-classes :forward-chaining)


(definecd add-pending-psfn (m :mssg pst :ps-fn) :ps-fn
  ;; A message already seen is not forwarded.
  ;; We assume that each messages is augmented with a timestamp such that no
  ;; two messages are the same.
  (if (v (in m (mget :pending pst))
         (in m (mget :seen pst)))
      pst
    (mset :pending
          (cons m (mget :pending pst))
          pst)))

(property prop=add-pending-psfn-seen (m :mssg pst :ps-fn)
  (== (mget :seen (add-pending-psfn m pst))
      (mget :seen pst))
  :hints (("Goal" :in-theory (enable add-pending-psfn))))

(property prop=add-pending-psfn-pending (m :mssg pst :ps-fn)
  :h (! (v (in m (mget :pending pst))
           (in m (mget :seen pst))))
  (in m (mget :pending (add-pending-psfn m pst)))
  :hints (("Goal" :in-theory (enable add-pending-psfn))))

(property prop=add-pending-psfn-pending2 (m :mssg pst :ps-fn)
  :h (in m (mget :pending pst))
  (in m (mget :pending (add-pending-psfn m pst)))
  :hints (("Goal" :in-theory (enable add-pending-psfn))))

(encapsulate ()
  (property prop=add-pending-psfn-pending3 (m :mssg pst :ps-fn)
    :h (in m (mget :pending pst))
    (== (mget :pending (add-pending-psfn m pst))
        (mget :pending pst))
    :hints (("Goal" :in-theory (enable add-pending-psfn)))))

(definecd new-fn-mssgp (m :mssg s :s-fn) :bool
  :function-contract-hints
  (("Goal" :in-theory (enable acl2::maximal-records-theory)))
  (v (endp s)
     (^ (nin m (mget :seen (cdar s)))
        (nin m (mget :pending (cdar s)))
        (new-fn-mssgp m (cdr s)))))

(property new-mssg=>not-seen-peer (s :s-fn p :peer m :mssg)
  :h (^ (new-fn-mssgp m s)
        (mget p s))
  (! (v (in m (mget :pending (mget p s)))
        (in m (mget :seen (mget p s)))))
  :hints (("Goal" :in-theory (enable new-fn-mssgp
                                     acl2::maximal-records-theory))))

;; Produce conditions
(definec produce-fn-pre (m :mssg s :s-fn) :bool
  (b* ((origin (mget :or m))
       (origin-st (mget origin s)))
    (^ (new-fn-mssgp m s)
       origin-st
       (in (mget :tp m)
           (mget :pubs origin-st)))))

(definecd produce-fn (m :mssg s :s-fn) :s-fn
  :ic (produce-fn-pre m s)
  (mset (mget :or m)
        (add-pending-psfn m
                          (mget (mget :or m) s))
        s))

(definecd forwarder-new-pst (pst :ps-fn m :mssg) :ps-fn
  (mset :seen
        (insert-unique m (mget :seen pst))
        (mset :pending
              (remove-equal m (mget :pending pst))
              pst)))

(definecd forward-help-fn (s :s-fn nbrs :lop m :mssg) :s-fn
  :function-contract-hints (("Goal" :in-theory
                             (enable acl2::maximal-records-theory)))
  :body-contracts-hints (("Goal" :in-theory
                          (enable add-pending-psfn)))
  (match s
    (() '())
    (((q . qst) . rst)
     (cons (if (in q nbrs)
               `(,q . ,(add-pending-psfn m qst))
             `(,q . ,qst))
           (forward-help-fn rst nbrs m)))))

(propertyd prop=forward-help-fn-cdr (m :mssg nbrs :lop s :s-fn)
  :h (consp s)
  (== (cdr (forward-help-fn s nbrs m))
      (forward-help-fn (cdr s) nbrs m))
  :hints (("Goal" :in-theory (enable forward-help-fn))))

(property prop=in-m-forward-help-fn (m :mssg nbrs :lop s :s-fn)
  :check-contracts? nil
  :h (^ (consp s)
        (in m (mget :pending (cdr (car s)))))
  (in m (mget :pending (cdr (car (forward-help-fn s nbrs m)))))
  :hints (("Goal" :in-theory (enable forward-help-fn))))

(property prop=in-m-forward-help-fn2 (m :mssg nbrs :lop s :s-fn)
  :check-contracts? nil
  :h (^ (consp s)
        (in m (mget :pending (cdr (car s)))))
  (== (mget :pending (cdr (car (forward-help-fn s nbrs m))))
      (mget :pending (cdr (car s))))
  :hints (("Goal" :in-theory (enable forward-help-fn))))

(property prop=in-m-forward-help-fn3 (m :mssg nbrs :lop s :s-fn)
  :check-contracts? nil
  :h (consp s)
  (v (== (mget :pending (cdr (car (forward-help-fn s nbrs m))))
         (mget :pending (cdr (car s))))
     (== (mget :pending (cdr (car (forward-help-fn s nbrs m))))
         (cons m (mget :pending (cdr (car s))))))
  :hints (("Goal" :in-theory (enable forward-help-fn
                                     add-pending-psfn))))

(property prop=forward-help-fn-seen (p :peer s :s-fn nbrs :lop m :mssg)
  :check-contracts? nil
  :h (mget p s)
  (== (mget :seen (mget p (forward-help-fn s nbrs m)))
      (mget :seen (mget p s)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory
                                     forward-help-fn))))

(property rem-peer-check (i :peer ps :lop)
  (lopp (remove-equal i ps)))
(property topic-lop-map-check (tp :topic subs :topic-lop-map)
  (lopp (mget tp subs)))


(definec update-forwarder-fn (p :peer m :mssg s :s-fn) :s-fn
  :function-contract-hints (("Goal" :in-theory
                             (enable acl2::maximal-records-theory)))
  :body-contracts-hints (("Goal" :in-theory
                          (enable forwarder-new-pst)))
  (match s
    (() '())
    (((!p . pst) . rst)
     (cons `(,p . ,(forwarder-new-pst pst m)) rst))
    ((r . rst)
     (cons r (update-forwarder-fn p m rst)))))

(property prop=update-forwarder-fn-cdr (p :peer m :mssg s :s-fn)
  :h (consp s)
  (== (cdr (update-forwarder-fn p m s))
      (update-forwarder-fn p m (cdr s)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))

(encapsulate ()
  (local
   (propertyd prop=update-forwarder-fn1 (p :peer m :mssg s :s-fn)
     :check-contracts? nil
     :h (^ (consp s)
           (!= p (car (car s))))
     (== (mget :pending (cdr (car (update-forwarder-fn p m s))))
         (mget :pending (cdr (car s))))
     :hints (("Goal" :in-theory (enable update-forwarder-fn
                                        forwarder-new-pst)))))

   (local
    (propertyd prop=update-forwarder-fn2 (p :peer m :mssg s :s-fn)
      :check-contracts? nil
      :h (^ (consp s)
            (== p (car (car s))))
      (== (mget :pending (cdr (car (update-forwarder-fn p m s))))
          (remove-equal m (mget :pending (cdr (car s)))))
      :hints (("Goal" :in-theory (enable update-forwarder-fn
                                         forwarder-new-pst)))))

   (property prop=update-forwarder-fn3 (p :peer m :mssg s :s-fn)
     :h (consp s)
     (v (== (mget :pending (cdr (car (update-forwarder-fn p m s))))
            (mget :pending (cdr (car s))))
        (== (mget :pending (cdr (car (update-forwarder-fn p m s))))
            (remove-equal m (mget :pending (cdr (car s))))))
     :hints (("Goal" :use (prop=update-forwarder-fn1
                           prop=update-forwarder-fn2)))))

;; do a recursive func. update all.
(definecd forward-fn (p :peer m :mssg s :s-fn) :s-fn
  :body-contracts-hints (("Goal" :in-theory (enable ps-fn)))
  :ic (^ (mget p s)
         (in m (mget :pending (mget p s))))
  (b* ((tp (mssg-tp m))
       (pst (mget p s))
       (nsubs (mget :nsubs pst))
       (fwdnbrs (mget tp nsubs)))
    (forward-help-fn (update-forwarder-fn p m s)
                     fwdnbrs m)))

(property prop=forward-fn-cdr (p :peer m :mssg s :s-fn)
  :check-contracts? nil
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (mget p (cdr s)))
  (== (forward-fn p m (cdr s))
      (cdr (forward-fn p m s)))
  :hints (("Goal" :in-theory (enable forward-fn
                                     forward-help-fn
                                     acl2::maximal-records-theory))))

(definecd set-subs (topics :lot p :peer nsubs acc :topic-lop-map)
  :topic-lop-map
  (match nsubs
    (() acc)
    (((tp . ps) . rst)
     (set-subs topics p rst
                            (if (in tp topics)
                                (mset tp
                                      (union-equal (list p) ps)
                                      acc)
                              (mset tp
                                    (remove-equal p ps)
                                    acc))))))

(definecd set-subs-psfn (nbrs :lop topics :lot n p :peer pst :ps-fn) :ps-fn
  (if (in n nbrs)
      (mset :nsubs (set-subs topics p (mget :nsubs pst) '()) pst)
    pst))

(property prop=set-subs-psfn-check (nbrs :lop topics :lot n p :peer pst :ps-fn)
  (^ (== (mget :pubs (set-subs-psfn nbrs topics n p pst))
         (mget :pubs pst))
     (== (mget :subs (set-subs-psfn nbrs topics n p pst))
         (mget :subs pst))
     (== (mget :seen (set-subs-psfn nbrs topics n p pst))
         (mget :seen pst))
     (== (mget :pending (set-subs-psfn nbrs topics n p pst))
         (mget :pending pst))) 
  :hints (("Goal" :in-theory (enable set-subs-psfn))))


;; Given a peer p and topics it subscribes to, share p subs with its
;; neighboring peers
(definecd set-subs-sfn (nbrs :lop topics :lot p :peer s :s-fn)
  :s-fn
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (match s
    (() '())
    (((n . pst) . rst)
     (cons `(,n . ,(set-subs-psfn nbrs topics n p pst))
           (set-subs-sfn nbrs topics p rst)))))

(property prop=cdr-set-subs-sfn (nbrs :lop subs :lot p :peer s
                                                   :s-fn)
  (== (cdr (set-subs-sfn nbrs subs p s))
      (set-subs-sfn nbrs subs p (cdr s)))
  :hints (("Goal" :in-theory (enable set-subs-sfn))))

;; Calculate nsubs, given neighbors in a fn state
(definecd calc-nsubs-fn (nbrs :lop s :s-fn acc :topic-lop-map) :topic-lop-map
  (match nbrs
    (() acc)
    ((n . rst) (b* ((pst (mget n s))
                    ((when (null pst))
                     (calc-nsubs-fn rst s acc)))
                 (calc-nsubs-fn rst
                                s
                                (set-subs (mget :subs pst)
                                                       n
                                                       acc
                                                       '()))))))

(sig set-difference-equal ((listof :a) (listof :a)) => (listof :a))
(sig union-equal ((listof :a) (listof :a)) => (listof :a))

(definecd ps-fn-nbrs-help (xs :topic-lop-map acc :lop) :lop
  (match xs
    (() acc)
    (((& . peers) . rst)
     (ps-fn-nbrs-help rst (union-equal peers acc)))))

(definecd ps-fn-nbrs (pst :ps-fn) :lop
  (ps-fn-nbrs-help (mget :nsubs pst) '()))


(definec new-joinee-st-fn (pubs subs :lot nbrs :lop s :s-fn) :ps-fn
  :function-contract-hints (("Goal" :in-theory (enable ps-fnp)))
  (ps-fn pubs subs (calc-nsubs-fn nbrs s '()) '() '()))

(definecd join-fn (p :peer pubs subs :lot nbrs :lop s :s-fn) :s-fn
  :ic (^ (! (mget p s))
	 (nin p nbrs))
  (set-subs-sfn nbrs
                subs
                p
                (mset p
                      (new-joinee-st-fn pubs subs nbrs s)
                      s)))


;; Following 3 Lemmas are about joining peer with no nbrs
(property set-subs-psfn-nbrs-nil (topics :lot n p :peer pst :ps-fn)
  (== (set-subs-psfn '() topics n p pst)
      pst)
  :hints (("Goal" :in-theory (enable set-subs-psfn))))

(property set-subs-sfn-nbrs-nil (subs :lot p :peer s :s-fn)
  (== (set-subs-sfn '() subs p s)
      s)
  :hints (("Goal" :in-theory (enable set-subs-sfn
                                     acl2::maximal-records-theory))))

(property join-fn-nbrs-nil (p :peer pubs subs :lot s :s-fn)
  :h (! (mget p s))
  (== (join-fn p pubs subs '() s)
      (mset p
            (new-joinee-st-fn pubs subs '() s)
            s))
  :instructions
  (:pro
   (:dv 1) (:r 2) :s :top
   (:claim (s-fnp (mset p (new-joinee-st-fn pubs subs nil s)
                        s)))
   (:prove :hints (("Goal"
                    :use ((:instance
                           set-subs-sfn-nbrs-nil
                           (s (mset p (new-joinee-st-fn
                                       pubs subs nil s)
                                    s)))))))))


(definecd subscribe-fn (p :peer topics :lot s :s-fn) :s-fn
  :function-contract-hints (("Goal" :in-theory (enable ps-fnp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-fnp)))
  :ic (mget p s)
  (let ((pst (mget p s)))
    (set-subs-sfn (ps-fn-nbrs pst)
                  topics
                  p
                  (mset p 
                        (mset :subs (union-equal (mget :subs pst)
                                                 topics)
                              pst)
                        s))))

(definecd unsubscribe-fn (p :peer topics :lot s :s-fn) :s-fn
  :function-contract-hints (("Goal" :in-theory (enable ps-fnp)))
  :body-contracts-hints (("Goal" :in-theory (enable ps-fnp)))
  :ic (mget p s)
  (let ((pst (mget p s)))
          (set-subs-sfn (ps-fn-nbrs pst)
                                     topics
                                     p
                                     (mset p 
                                           (mset :subs (set-difference-equal
                                                        (mget :subs pst)
                                                        topics)
                                                 pst)
                                           s))))

(property prop=mget-cdr (p :peer s :s-fn )
  :h (^ (mget p s)
        (!= p (car (car s))))
  (mget p (cdr s))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))

(property prop=mget=car (p :peer s :s-fn)
  :h (^ (consp s)
        (== p (car (car s))))
  (== (mget p s)
      (cdr (car s)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))


(definecd leave-fn (p :peer s :s-fn) :s-fn
  :function-contract-hints
  (("Goal" :in-theory (enable acl2::maximal-records-theory)))
  :ic (mget p s)
  (match s
    (() '())
    (((!p . &) . rst) rst)
    ((r . rst) (cons r (leave-fn p rst)))))
  
(sig union-set ((listof :a) (listof :a)) => (listof :a))

(definec fn-pending-mssgs (s :s-fn) :lom
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
  (match s
    (() '())
    (((& . pst) . rst) (union-set (mget :pending pst)
                                  (fn-pending-mssgs rst)))))


(property prop=in-p-fn-pending (p :peer m :mssg s :s-fn)
  :h (mget p s)
  (=> (in m (mget :pending (mget p s)))
      (in m (fn-pending-mssgs s)))
  :instructions
  (:pro
   :induct :bash
   :pro
   (:casesplit (== p (car (car s))))
   (:claim (== (mget p s) (cdr (car s))))
   (:claim (in m (mget :pending (mget p s))))
   :bash
   
   (:claim (mget p (cdr s))
           :hints (("Goal" :use (prop=mget-cdr))))
   (:claim (== (mget p s) (mget p (cdr s)))
           :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))
   (:claim (in m (mget :pending (mget p (cdr s)))))
   (:claim (in m (fn-pending-mssgs (cdr s))))
   (:dv 2) :r :s :top
   (:claim (in m
               (union-set (fn-pending-mssgs (cdr s))
                          (mget :pending (cdr (car s)))))
           :hints (("Goal" :use ((:instance in-union
                                            (x (fn-pending-mssgs (cdr s)))
                                            (y (mget :pending (cdr (car s))))
                                            )))))
   (:claim (in m
               (union-set  (mget :pending (cdr (car s)))
                           (fn-pending-mssgs (cdr s))))
           :hints (("Goal" :in-theory (enable union-set-symm))))
   :s :pro :bash))


(encapsulate ()
  (local
   (property h0 (s :s-fn)
     :check-contracts? nil
     :h (consp s)
     (equal (fn-pending-mssgs s)
            (union-set (mget :pending (cdar s))
                       (fn-pending-mssgs (cdr s))))))
  
  (local
   (property h1 (p :peer subs :lot nbrs :lop s :s-fn)
     :check-contracts? nil
     :h (consp s)
     (equal (fn-pending-mssgs (set-subs-sfn nbrs subs p s))
            (union-set (mget :pending (cdar (set-subs-sfn nbrs subs p s)))
                         (fn-pending-mssgs (cdr (set-subs-sfn nbrs subs p s)))))
     :hints (("Goal" :use ((:instance h0 (s (set-subs-sfn nbrs subs p s))))))))

  (local
   (property h2 (p :peer subs :lot nbrs :lop s :s-fn)
     :check-contracts? nil
     :h (consp s)
     (== (mget :pending (cdar (set-subs-sfn nbrs subs p s)))
         (mget :pending (cdar s)))
     :hints (("Goal" :in-theory (enable acl2::maximal-records-theory
                                        set-subs-sfn)
              :use (prop=set-subs-psfn-check)))))

  (local
   (property h3 (p :peer subs :lot nbrs :lop s :s-fn)
     :check-contracts? nil
     :h (consp s)
     (equal (fn-pending-mssgs (set-subs-sfn nbrs subs p s))
            (union-set (mget :pending (cdar s))
                         (fn-pending-mssgs (cdr (set-subs-sfn nbrs subs p s)))))))

  (local 
   (property h4 (p :peer subs :lot nbrs :lop s :s-fn)
     :check-contracts? nil
     :h (consp s)
     (equal (fn-pending-mssgs (set-subs-sfn nbrs subs p s))
            (union-set (mget :pending (cdar s))
                         (fn-pending-mssgs (set-subs-sfn nbrs subs p (cdr s)))))
     :hints (("Goal" :use (h2 prop=cdr-set-subs-sfn)))))

  (local 
   (property h5 (p :peer subs :lot nbrs :lop s :s-fn)
     :h (== s nil)
     (== (set-subs-sfn nbrs subs p s) nil)
     :hints (("Goal" :in-theory (enable set-subs-sfn)))))

  (property prop=pending-mssgs-set-topics-subscribe (p :peer subs :lot nbrs :lop s :s-fn)
    (== (fn-pending-mssgs (set-subs-sfn nbrs subs p s))
        (fn-pending-mssgs s)))

  (local
   (in-theory (enable fn-pending-mssgs forward-help-fn forward-fn)))

  (local
   (property prop=fn-pending-mssgs-update-forwarder-fn (p :peer m :mssg s :s-fn)
     (v (== (fn-pending-mssgs (update-forwarder-fn p m s))
            (remove-equal m (fn-pending-mssgs s)))
        (== (fn-pending-mssgs (update-forwarder-fn p m s))
            (fn-pending-mssgs s)))
     :instructions
     (:pro
      :induct :bash :pro
      (:claim (v (equal (fn-pending-mssgs (update-forwarder-fn p m (cdr s)))
                        (remove-equal m (fn-pending-mssgs (cdr s))))
                 (equal (fn-pending-mssgs (update-forwarder-fn p m (cdr s)))
                        (fn-pending-mssgs (cdr s)))))
      
      (:claim (consp (update-forwarder-fn p m s)))
      (:claim (== (fn-pending-mssgs (update-forwarder-fn p m s))
                  (union-set (mget :pending (cdr (car (update-forwarder-fn p m s))))
                             (fn-pending-mssgs (cdr (update-forwarder-fn p m s)))))
              :hints (("Goal" :use ((:instance h0 (s (update-forwarder-fn p m s)))))))
      
      (:claim (== (fn-pending-mssgs (cdr (update-forwarder-fn p m s)))
                  (fn-pending-mssgs (update-forwarder-fn p m (cdr s))))
              :hints (("Goal" :use ((:instance prop=update-forwarder-fn-cdr)))))

      (= (fn-pending-mssgs (update-forwarder-fn p m s))
         (union-set (mget :pending (cdr (car (update-forwarder-fn p m s))))
                    (fn-pending-mssgs (update-forwarder-fn p m (cdr s)))))

      (:claim (v (== (mget :pending (cdr (car (update-forwarder-fn p m s))))
                     (mget :pending (cdr (car s))))
                 (== (mget :pending (cdr (car (update-forwarder-fn p m s))))
                     (remove-equal m (mget :pending (cdr (car s))))))
              :hints (("Goal" :use ((:instance prop=update-forwarder-fn3)))))

      (:casesplit (== (mget :pending (cdr (car (update-forwarder-fn p m s))))
                      (mget :pending (cdr (car s)))))
      (= (mget :pending (cdr (car (update-forwarder-fn p m s))))
         (mget :pending (cdr (car s))))
      (:casesplit (equal (fn-pending-mssgs (update-forwarder-fn p m (cdr s)))
                         (fn-pending-mssgs (cdr s))))
      (= (fn-pending-mssgs (update-forwarder-fn p m (cdr s)))
         (fn-pending-mssgs (cdr s)))
      (= (union-set (mget :pending (cdr (car s)))
                    (fn-pending-mssgs (cdr s)))
         (fn-pending-mssgs s))
      :s

      (:claim (== (fn-pending-mssgs (update-forwarder-fn p m (cdr s)))
                  (remove-equal m (fn-pending-mssgs (cdr s)))))
      (= (fn-pending-mssgs (update-forwarder-fn p m (cdr s)))
         (remove-equal m (fn-pending-mssgs (cdr s))))
      (= (union-set (mget :pending (cdr (car s)))
                    (remove-equal m (fn-pending-mssgs (cdr s))))
         (union-set (remove-equal m (fn-pending-mssgs (cdr s)))
                    (mget :pending (cdr (car s))))
         :hints (("Goal" :use ((:instance union-set-symm
                                          (x (mget :pending (cdr (car s))))
                                          (y (remove-equal m (fn-pending-mssgs
                                                              (cdr s)))))))))
      (= (fn-pending-mssgs s)
         (union-set (mget :pending (cdr (car s))) (fn-pending-mssgs (cdr s))))
      (= (union-set (mget :pending (cdr (car s))) (fn-pending-mssgs (cdr s)))
         (union-set (fn-pending-mssgs (cdr s)) (mget :pending (cdr (car s))))
         :hints (("Goal" :use ((:instance union-set-symm
                                          (x (mget :pending (cdr (car s))))
                                          (y (fn-pending-mssgs (cdr s))))))))
      (:prove :hints (("Goal" :use ((:instance remove-union-set-options
                                               (x (fn-pending-mssgs (cdr s)))
                                               (y (mget :pending (cdr (car
                                                                       s)))))))))

      (:claim (== (mget :pending (cdr (car (update-forwarder-fn p m s))))
                  (remove-equal m (mget :pending (cdr (car s))))))
      (= (mget :pending (cdr (car (update-forwarder-fn p m s))))
         (remove-equal m (mget :pending (cdr (car s)))))

      (:claim (== (fn-pending-mssgs (update-forwarder-fn p m (cdr s)))
                  (fn-pending-mssgs (cdr s))))
      (= (fn-pending-mssgs (update-forwarder-fn p m (cdr s)))
         (fn-pending-mssgs (cdr s)))
      (= (fn-pending-mssgs s)
         (union-set (mget :pending (cdr (car s))) (fn-pending-mssgs (cdr s))))
      (:prove :hints (("Goal" :use ((:instance remove-union-set-options
                                               (x (mget :pending (cdr (car
                                                                       s))))
                                               (y (fn-pending-mssgs (cdr
                                                                     s))))))))
      :bash)))

  (local
   (property prop=fn-pending-mssgs-forward-help-fn (s :s-fn nbrs :lop m :mssg)
     (v (== (fn-pending-mssgs (forward-help-fn s nbrs m))
            (insert-unique m (fn-pending-mssgs s)))
        (== (fn-pending-mssgs (forward-help-fn s nbrs m))
            (fn-pending-mssgs s)))
     :instructions
     (:pro 
      :induct :bash :pro
      (:claim (or (== (fn-pending-mssgs (forward-help-fn (cdr s) nbrs m))
                      (insert-unique m (fn-pending-mssgs (cdr s))))
                  (== (fn-pending-mssgs (forward-help-fn (cdr s) nbrs m))
                      (fn-pending-mssgs (cdr s)))))

      (:claim (== (fn-pending-mssgs (forward-help-fn s nbrs m))
                  (union-set (mget :pending (cdr (car (forward-help-fn s nbrs m))))
                             (fn-pending-mssgs (cdr (forward-help-fn s nbrs m)))))
              :hints (("Goal" :use ((:instance h0 (s (forward-help-fn s nbrs
                                                                      m)))))))

      (:claim (consp (forward-help-fn s nbrs m))
              :hints (("Goal" :in-theory (enable forward-help-fn))))
      (:claim (== (fn-pending-mssgs (cdr (forward-help-fn s nbrs m)))
                  (fn-pending-mssgs (forward-help-fn (cdr s) nbrs m)))
              :hints (("Goal" :use ((:instance prop=forward-help-fn-cdr)))))
      
      (= (fn-pending-mssgs (forward-help-fn s nbrs m))
         (union-set (mget :pending (cdr (car (forward-help-fn s nbrs m))))
                    (fn-pending-mssgs (cdr (forward-help-fn s nbrs m)))))

      (= (fn-pending-mssgs (cdr (forward-help-fn s nbrs m)))
         (fn-pending-mssgs (forward-help-fn (cdr s) nbrs m)))

      (:claim (v (== (mget :pending (cdr (car (forward-help-fn s nbrs m))))
                     (mget :pending (cdr (car s))))
                 (== (mget :pending (cdr (car (forward-help-fn s nbrs m))))
                     (cons m (mget :pending (cdr (car s))))))
              :hints (("Goal" :use ((:instance prop=in-m-forward-help-fn3)))))
      :bash
      :pro
      (= (fn-pending-mssgs s) nil)
      (= (forward-help-fn s nbrs m) nil
         :hints (("Goal" :in-theory (enable forward-help-fn))))
      :s
      )))

  (property prop=fn-pending-mssgs-forward-fn (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s))))
     (v (== (fn-pending-mssgs (forward-fn p m s))
            (remove-equal m (fn-pending-mssgs s)))
        (== (fn-pending-mssgs (forward-fn p m s))
            (fn-pending-mssgs s)))
     :instructions
     (:pro
      (= (forward-fn p m s)
         (forward-help-fn (update-forwarder-fn p m s)
                          (mget (mget :tp m)
                                (mget :nsubs (mget p s)))
                          m))
      (:claim (v (== (fn-pending-mssgs (forward-help-fn (update-forwarder-fn p
                                                                             m s)
                                                        (mget (mget :tp m)
                                                              (mget :nsubs (mget p s)))
                                                        m))
                     (insert-unique m (fn-pending-mssgs (update-forwarder-fn p m s))))
                 (== (fn-pending-mssgs (forward-help-fn (update-forwarder-fn p
                                                                             m s)
                                                        (mget (mget :tp m)
                                                              (mget :nsubs (mget p s)))
                                                        m))
                     (fn-pending-mssgs (update-forwarder-fn p m s))))
              :hints (("Goal" :use ((:instance
                                     prop=fn-pending-mssgs-forward-help-fn
                                     (s (update-forwarder-fn p m s))
                                     (nbrs (mget (mget :tp m)
                                                 (mget :nsubs (mget p
                                                                    s)))))))))

      (:claim (v (== (fn-pending-mssgs (update-forwarder-fn p m s))
                     (remove-equal m (fn-pending-mssgs s)))
                 (== (fn-pending-mssgs (update-forwarder-fn p m s))
                     (fn-pending-mssgs s)))
              :hints (("Goal" :use ((:instance prop=fn-pending-mssgs-update-forwarder-fn)))))
    
      (:casesplit (== (fn-pending-mssgs (forward-help-fn (update-forwarder-fn p
                                                                              m s)
                                                         (mget (mget :tp m)
                                                               (mget :nsubs (mget p s)))
                                                         m))
                      (fn-pending-mssgs (update-forwarder-fn p m s))))
      (= (fn-pending-mssgs (forward-help-fn (update-forwarder-fn p m s)
                                            (mget (mget :tp m)
                                                  (mget :nsubs (mget p s)))
                                            m))
         (fn-pending-mssgs (update-forwarder-fn p m s)))

      (:casesplit (equal (fn-pending-mssgs (update-forwarder-fn p m s))
                         (fn-pending-mssgs s)))
      :s
      (:claim (== (fn-pending-mssgs (update-forwarder-fn p m s))
                  (remove-equal m (fn-pending-mssgs s))))
      :s
      (:claim (== (fn-pending-mssgs (forward-help-fn (update-forwarder-fn p
                                                                             m s)
                                                        (mget (mget :tp m)
                                                              (mget :nsubs (mget p s)))
                                                        m))
                  (insert-unique m (fn-pending-mssgs (update-forwarder-fn p m
                                                                          s)))))
      (= (fn-pending-mssgs (forward-help-fn (update-forwarder-fn p
                                                                             m s)
                                                        (mget (mget :tp m)
                                                              (mget :nsubs (mget p s)))
                                                        m))
         (insert-unique m (fn-pending-mssgs (update-forwarder-fn p m
                                                                 s))))

      (:casesplit (equal (fn-pending-mssgs (update-forwarder-fn p m s))
                         (fn-pending-mssgs s)))
      (= (fn-pending-mssgs (update-forwarder-fn p m s))
         (fn-pending-mssgs s))
      (:claim (in m (fn-pending-mssgs s))
              :hints (("Goal" :use ((:instance prop=in-p-fn-pending)))))
      (= (insert-unique m (fn-pending-mssgs s))
         (fn-pending-mssgs s))
      :s

      (:claim (== (fn-pending-mssgs (update-forwarder-fn p m s))
                  (remove-equal m (fn-pending-mssgs s))))
      (= (fn-pending-mssgs (update-forwarder-fn p m s))
         (remove-equal m (fn-pending-mssgs s)))
      (:claim (in m (fn-pending-mssgs s))
              :hints (("Goal" :use ((:instance prop=in-p-fn-pending)))))
      (:claim (== (fn-pending-mssgs s)
                  (union-set (mget :pending (cdr (car s)))
                             (fn-pending-mssgs (cdr s)))))
      (:claim (orderedp (union-set (mget :pending (cdr (car s)))
                                   (fn-pending-mssgs (cdr s)))))
      (:claim (orderedp (fn-pending-mssgs s)))
      (= (insert-unique m (remove-equal m (fn-pending-mssgs s)))
         (union-set (mget :pending (cdr (car s)))
                    (fn-pending-mssgs (cdr s)))
         :hints (("Goal" :use ((:instance insert-unique-remove-ordered3
                                          (r m)
                                          (x (fn-pending-mssgs s)))))))
      :s))
     )
  

(property prop=fn-pending-mssgs-mset-pending (s :s-fn p :peer m :mssg)
  :check-contracts? nil
  :h (mget p s)
  (equal (fn-pending-mssgs
          (mset p
                (mset :pending
                      (cons m (mget :pending (mget p s)))
                      (mget p s))
                s))
         (insert-unique m (fn-pending-mssgs s)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory
                                     s-fnp))))

(property prop=not-mget (p :peer s :s-fn)
  :h (! (mget p s))
  (! (mget p (cdr s)))
  :hints (("Goal" :in-theory (enable s-fnp acl2::maximal-records-theory))))

(property prop=not-mget2 (p :peer s :s-fn)
  :h (! (mget p s))
  (!= p (car (car s)))
  :hints (("Goal" :in-theory (enable s-fnp acl2::maximal-records-theory))))

(property prop=s-fn-mset2 (p :peer pst :ps-fn s :s-fn)
  :h (^ (! (mget p s))
        (! (<< p (car (car s))))
        (s-fnp (mset p pst (cdr s))))
  (s-fnp (cons (car s) (mset p pst (cdr s))))
  :hints (("Goal" :in-theory (enable lexorder alphorder
                                     acl2::maximal-records-theory))))

(property prop=nat<<nil (p :nat)
  (<< p nil)
  :hints (("Goal" :in-theory (enable lexorder alphorder
                                     acl2::maximal-records-theory))))



(property prop=fn-pending-mssgs-mset-pending-new (p :peer pst :ps-fn s :s-fn)
  :h (^ (! (mget p s))
        (== (mget :pending pst)
            nil))
  (== (fn-pending-mssgs (mset p pst s))
      (fn-pending-mssgs s))
  :instructions
  (:pro :induct :bash :pro
        (:claim (! (mget p (cdr s))) :hints (("Goal" :use (prop=not-mget))))
        (:claim (== (fn-pending-mssgs (mset p pst (cdr s)))
                    (fn-pending-mssgs (cdr s))))
        (:dv 1 1)
        (:casesplit (<< p (car (car s))))
        :r :s :up :r :s (:r union-set) :s
        (:claim (== (isort-set (fn-pending-mssgs s))  (fn-pending-mssgs s)))
        (:equiv (isort-set (fn-pending-mssgs s)) (fn-pending-mssgs s))
        :top :s (:r 2) :s :bash
        (:claim (!= p (car (car s))) :hints (("Goal" :use (prop=not-mget2))))
        :r :s :up :r :s :top
        (:dv 2) (:r fn-pending-mssgs) :s :top :s
        (:claim (s-fnp (cons (car s) (mset p pst (cdr s)))))
        :s :pro

        (:dv 1 1) :r :s :up :r :s :up
        (:dv 2) :r :s :bash))

(property prop=fn-pending-mssgs-mset-subs (s :s-fn p :peer topics :lot)
          :check-contracts? nil
          :h (mget p s)
          (equal (fn-pending-mssgs
                  (mset p
                        (mset :subs
                              topics
                              (mget p s))
                        s))
                 (fn-pending-mssgs s))
          :hints (("Goal" :in-theory (enable acl2::maximal-records-theory
                                             s-fnp))))
          
                                             
(property prop=fn-pending-mssgs-mset-subs2 (s :s-fn p :peer subs topics :lot
          nbrs :lop m :mssg)
          :check-contracts? nil
          :h (mget p s)
          (equal (fn-pending-mssgs 
                  (set-subs-sfn nbrs topics p (mset p
                                                    (mset :subs
                                                          subs
                                                          (mget p s))
                                                    s)))
                 (fn-pending-mssgs s)))


(property prop=union-nil (ms :lom)
  (== (union-equal ms nil)
      ms))

(property union-eq-x (x y :lom)
  (=> (not (union-equal x y))
      (^ (endp x)
         (endp y))))

(property prop=pending-mssgs-nil-cdr (s :s-fn)
  :h (== (fn-pending-mssgs s) nil)
  (^ (endp (mget :pending (cdar s)))
     (endp (fn-pending-mssgs (cdr s))))
  :hints (("Goal" :use ((:instance union-set-eq-x (x (mget :pending
                                                           (cdar s)))
                                   (y (fn-pending-mssgs (cdr s))))))))

(property prop=lomp-car (xs ys :lom)
  :h (set-difference-equal xs ys)
  (mssgp (car (set-difference-equal xs ys))))


(encapsulate ()
  (local
   (in-theory (enable leave-fn)))
  (local
   (property prop=isort-set-fn-pending-mssgs (s :s-fn)
     (== (isort-set (fn-pending-mssgs s))
         (fn-pending-mssgs s))))

  (local
   (property prop=pdg-mssgs-leave-fn-union-set (p :peer w :s-fn)
     :h (mget p w)
     (equal (union-set (mget :pending (mget p w))
                       (fn-pending-mssgs (leave-fn p w)))
            (fn-pending-mssgs w))
     :instructions
     (:pro :induct :bash
           :pro
           (:casesplit (!= (car (car w)) p))
           (:claim (== (mget p w)
                       (mget p (cdr w)))
                   :hints (("Goal" :in-theory (enable
                                               acl2::maximal-records-theory))))
           (:equiv (mget p w)
                   (mget p (cdr w)))
           (= (leave-fn p w)
              (cons (car w) (leave-fn p (cdr w))))
           (:claim (s-fnp (cons (car w) (leave-fn p (cdr w))))
                   :hints (("Goal" :in-theory (enable
                                               acl2::maximal-records-theory))))
           
           (= (fn-pending-mssgs (cons (car w)
                                      (leave-fn p (cdr w))))
              (union-set (mget :pending (cdar w))
                         (fn-pending-mssgs (leave-fn p (cdr w)))))
           (:claim (== (isort-set (fn-pending-mssgs (leave-fn p (cdr w))))
                       (fn-pending-mssgs (leave-fn p (cdr w)))))
           
           (= (union-set (mget :pending (mget p (cdr w)))
                         (union-set (mget :pending (cdr (car w)))
                                    (fn-pending-mssgs (leave-fn p (cdr w)))))
              (union-set (mget :pending (cdr (car w)))
                         (union-set (mget :pending (mget p (cdr w)))
                                    (fn-pending-mssgs (leave-fn p (cdr w)))))
              :hints (("Goal" :use ((:instance prop=union-set-order
                                               (x (mget :pending (mget p (cdr
                                                                          w))))
                                               (y (mget :pending (cdr (car w))))
                                               (z (fn-pending-mssgs (leave-fn p
                                                                              (cdr
                                                                               w)))))))))
           (:claim (mget p (cdr w)))
           (:claim (equal (union-set (mget :pending (mget p (cdr w)))
                                     (fn-pending-mssgs (leave-fn p (cdr w))))
                          (fn-pending-mssgs (cdr w))))
           :prove :prove :bash)))

   (property prop=pdg-mssgs-leave-fn-nequal (p :peer w :s-fn)
     :h (^ (mget p w)
           (subsetp-equal
            (mget :pending (mget p w))
            (fn-pending-mssgs (leave-fn p w))))
     (== (fn-pending-mssgs (leave-fn p w))
         (fn-pending-mssgs w))
     :instructions
     (:pro
      (:claim (== (isort-set (fn-pending-mssgs (leave-fn p w)))
                  (fn-pending-mssgs (leave-fn p w))))

      (:claim (== (union-set (mget :pending (mget p w))
                             (fn-pending-mssgs (leave-fn p w)))
                  (fn-pending-mssgs (leave-fn p w)))
              :hints (("Goal" :use ((:instance prop=subsetp-equal-isort-set
                                               (y (fn-pending-mssgs (leave-fn p w)))
                                               (x (mget :pending
                                                        (mget p w))))))))
      (:claim (equal (union-set (mget :pending (mget p w))
                                (fn-pending-mssgs (leave-fn p w)))
                     (fn-pending-mssgs w))
              :hints (("Goal" :use ((:instance prop=pdg-mssgs-leave-fn-union-set)))))
      :s))

  (local
   (property prop=mssg-car-in-help (xs ys :lom)
     :h (set-difference-equal xs ys)
     (in (car (set-difference-equal xs ys)) xs)))

  (local
   (property prop=mssg-car-in (p :peer w :s-fn)
     :h (^ (mget p w)
           (set-difference-equal
            (mget :pending (mget p w))
            (fn-pending-mssgs (leave-fn p w))))
     (in (car (set-difference-equal
               (mget :pending (mget p w))
               (fn-pending-mssgs (leave-fn p w))))
         (mget :pending (mget p w)))))

  (property prop=get-message-leave-fn-nequal (p :peer w :s-fn)
    :h (^ (mget p w)
          (!= (fn-pending-mssgs (leave-fn p w))
              (fn-pending-mssgs w)))
    (in (car (set-difference-equal
              (mget :pending (mget p w))
              (fn-pending-mssgs (leave-fn p w))))
        (mget :pending (mget p w)))
    :instructions
    (:pro
     (:claim (! (subsetp-equal
                 (mget :pending (mget p w))
                 (fn-pending-mssgs (leave-fn p w)))))
     (:claim (set-difference-equal
              (mget :pending (mget p w))
              (fn-pending-mssgs (leave-fn p w))))
     
     :prove))


  (property prop=message-leave-fn-nequal-pending (p :peer w :s-fn)
    :h (^ (mget p w)
          (!= (fn-pending-mssgs (leave-fn p w))
              (fn-pending-mssgs w)))
    (in (car (set-difference-equal
              (mget :pending (mget p w))
              (fn-pending-mssgs (leave-fn p w))))
        (fn-pending-mssgs w))
    :instructions
    (:pro
     (:claim (in (car (set-difference-equal
              (mget :pending (mget p w))
              (fn-pending-mssgs (leave-fn p w))))
                 (mget :pending (mget p w)))
             :hints (("Goal" :use ((:instance
                                    prop=get-message-leave-fn-nequal)))))
     (:claim (lomp (mget :pending (mget p w)))
             :hints (("Goal" :in-theory (enable ps-fnp))))
     (:claim (lomp (fn-pending-mssgs (leave-fn p w)))
             :hints (("Goal" :in-theory (enable fn-pending-mssgs))))
     (:claim (set-difference-equal (mget :pending (mget p w))
                                   (fn-pending-mssgs (leave-fn p w)))
             :hints (("Goal" :use ((:instance prop=set-diff-nil-subset
                                              (xs (mget :pending (mget p w)))
                                              (ys (fn-pending-mssgs
                                                   (leave-fn p w))))))))
     (:prove :hints (("Goal" :use ((:instance prop=in-p-fn-pending
                                              (m (car (set-difference-equal
                                                       (mget :pending (mget p w))
                                                       (fn-pending-mssgs
                                                        (leave-fn p w)))))
                                              (s w)))))))))







