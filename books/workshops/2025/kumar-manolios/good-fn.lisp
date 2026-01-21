(in-package "ACL2S")
(include-book "f2b-commit")

(definec pending-!in-seen-ps-fn (st :ps-fn ms :lom) :bool
  (match ms
    (() t)
    ((m . rs) (^ (! (in m (mget :seen st)))
                 (pending-!in-seen-ps-fn st rs)))))

(property prop=pending-!in-seen-ps-fn (st :ps-fn m :mssg ms :lom)
  :h (^ (in m ms)
        (pending-!in-seen-ps-fn st ms))
  (! (in m (mget :seen st)))
  :hints (("Goal" :in-theory (enable ps-fnp))))

(property prop=pending-!in-seen-ps-fn-set-pending (st :ps-fn m :mssg
                                                         ms ns :lom)
  :h (^ (! (in m (mget :seen st)))
        (pending-!in-seen-ps-fn st ms))
  (pending-!in-seen-ps-fn (mset :pending ns st)
                             (cons m ms)))

(definec pending-!in-seen-s-fn (s :s-fn) :bool
  (match s
    (() t)
    (((& . pst) . rst)
     (^ (pending-!in-seen-ps-fn pst (mget :pending pst))
        (pending-!in-seen-s-fn rst)))))

(propertyd prop=pending-!in-seen-s-fn (s :s-fn p :peer m :mssg)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (pending-!in-seen-s-fn s))
  (! (in m (mget :seen (mget p s))))
  :hints (("Goal" :in-theory
           (enable acl2::maximal-records-theory))))

(in-theory (enable new-fn-mssgp produce-fn produce-fn-pre
                   acl2::maximal-records-theory subscribe-fn
                   unsubscribe-fn set-subs-sfn leave-fn
                   join-fn ordered-seenp))

(property prop=mset-ordered-seenp (p :peer pst :ps-fn s :s-fn)
  :h (^ (orderedp (mget :seen pst))
        (ordered-seenp s))
  (ordered-seenp (mset p pst s)))

(propertyd prop=ordered-add-pending-psfn (p :peer s :s-fn m :mssg)
  :h (^ (ordered-seenp s)
        (mget p s))
  (orderedp (mget :seen (add-pending-psfn m (mget p s))))
  :instructions
  (:pro
   (:claim (orderedp (mget :seen (mget p s))))
   (:claim (== (mget :seen (add-pending-psfn m (mget p s)))
               (mget :seen (mget p s)))
           :hints (("Goal" :use ((:instance
                                  prop=add-pending-psfn-seen
                                  (pst (mget p s)))))))
   :prove))
  

(property prop=ordered-seenp-s-fn-produce (s :s-fn m :mssg)
  :h (^ (ordered-seenp s)
        (produce-fn-pre m s))
  (ordered-seenp (produce-fn m s))
  :instructions
  (:pro
   (:claim (mget (mget :or m) s))
   (= (produce-fn m s)
      (mset (mget :or m)
            (add-pending-psfn m
                              (mget (mget :or m) s))
            s))
   (:claim (ps-fnp (add-pending-psfn m (mget (mget :or m) s))))
   (:claim (orderedp (mget :seen (add-pending-psfn m (mget (mget :or m) s))))
           :hints (("Goal" :use ((:instance
                                  prop=ordered-add-pending-psfn
                                  (p (mget :or m)))))))
   (:prove :hints (("Goal" :use ((:instance
                                  prop=mset-ordered-seenp
                                  (p (mget :or m))
                                  (pst (add-pending-psfn m (mget (mget :or m) s))))))))))



(encapsulate ()
  (local
   (in-theory (enable forward-help-fn
                      forward-fn)))

  (local
   (property prop=ordered-seenp-forward-help
     (nbrs :lop m :mssg s :s-fn)
     :h (ordered-seenp s)
     (ordered-seenp (forward-help-fn s nbrs m))
     :hints (("Goal" :use ((:instance prop=add-pending-psfn-seen
                                      (pst (cdar s))))))))

  (local
   (property prop=ordered-forwarder-new-pst (pst :ps-fn m :mssg)
     :h (orderedp (mget :seen pst))
     (orderedp (mget :seen (forwarder-new-pst pst m)))
     :hints (("Goal" :in-theory (enable forwarder-new-pst)))))

  (local
   (property prop=ordered-seenp-update-forwarder
     (p :peer m :mssg s :s-fn)
     :h (^ (mget p s)
           (ordered-seenp s))
     (ordered-seenp (update-forwarder-fn p m s))
     :hints (("Goal" :use ((:instance prop=update-forwarder-seen1)
                           (:instance prop=update-forwarder-seen2))))))

  (property prop=ordered-seenp-forward-fn (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s)))
          (ordered-seenp s))
    (ordered-seenp (forward-fn p m s))))



(encapsulate ()
  (local
   (in-theory (enable leave-fn
                      join-fn
                      subscribe-fn
                      unsubscribe-fn)))
   
   (local
    (property prop=orderedp-ps-fn-new-joinee-st
      (pubs subs :lot nbrs :lop ms :lom s :s-fn)
      (orderedp
       (mget :seen
             (new-joinee-st-fn pubs subs nbrs s)))
      :hints (("Goal" :in-theory (enable ps-fnp
                                         orderedp)))))
   (local
    (property prop=ordered-set-subs-psfn (nbrs :lop topics :lot
                                               n p :peer pst :ps-fn)
     :h (orderedp (mget :seen pst))
     (orderedp (mget :seen (set-subs-psfn nbrs topics n p pst)))
     :hints (("Goal" :in-theory (enable set-subs-psfn)))))
    

   (local
    (property prop=ordered-seenp-set-nsubs-sfn (nbrs :lop topics :lot
                                                     p :peer s :s-fn)
      :h (ordered-seenp s)
      (ordered-seenp
       (set-subs-sfn nbrs topics p s))
      :instructions
      (:pro :induct :bash
            :pro
            (:claim (ordered-seenp (cdr s)))
            (:claim (ordered-seenp
                     (set-subs-sfn nbrs topics p (cdr s))))
            (:claim (== (set-subs-sfn nbrs topics p s)
                        (cons (cons (car (car s))
                                    (set-subs-psfn nbrs topics (car (car s))
                                                   p (cdr (car s))))
                              (set-subs-sfn nbrs topics p (cdr s))))
                    :hints (("Goal" :in-theory (enable set-subs-sfn))))
            (:claim (s-fnp (cons (cons (car (car s))
                                    (set-subs-psfn nbrs topics (car (car s))
                                                   p (cdr (car s))))
                                 (set-subs-sfn nbrs topics p (cdr s)))))
            (:r ordered-seenp) :s
            (:equiv (set-subs-sfn nbrs topics p s)
                        (cons (cons (car (car s))
                                    (set-subs-psfn nbrs topics (car (car s))
                                                   p (cdr (car s))))
                              (set-subs-sfn nbrs topics p (cdr s))))
            (= (cdr (car (cons (cons (car (car s))
                                     (set-subs-psfn nbrs topics (car (car s))
                                                    p (cdr (car s))))
                               (set-subs-sfn nbrs topics p (cdr s)))))
               (set-subs-psfn nbrs topics (car (car s))
                              p (cdr (car s))))
            (:prove :hints (("Goal" :use ((:instance
                                           prop=ordered-set-subs-psfn
                                           (p (car (car s)))
                                           (pst (cdr (car s))))))))
            (:prove :hints (("Goal" :in-theory (enable set-subs-sfn)))))))
    

   (property prop=ordered-seenp-subscribe (s :s-fn p :peer topics :lot)
    :h (^ (mget p s)
          (ordered-seenp s))
    (ordered-seenp (subscribe-fn p topics s))
    :instructions
    (:pro
     (= (subscribe-fn p topics s)
        (set-subs-sfn (ps-fn-nbrs (mget p s))
                      topics
                      p
                      (mset p 
                            (mset :subs (union-equal (mget :subs (mget p s))
                                                     topics)
                                  (mget p s))
                            s)))
     (:claim (orderedp (mget :seen (mget p s))))
     (:claim (== (mget :seen (mget p s))
                 (mget :seen (mset :subs
                                   (union-equal (mget :subs (mget p s))
                                                topics)
                                   (mget p s)))))
     (:claim (orderedp (mget :seen (mset :subs
                                   (union-equal (mget :subs (mget p s))
                                                topics)
                                   (mget p s)))))
     (:claim (ordered-seenp
              (mset p
                    (mset :subs
                          (union-equal (mget :subs (mget p s))
                                       topics)
                          (mget p s))
                    s))
              :hints (("Goal" :use ((:instance
                                     prop=mset-ordered-seenp
                                     (pst (mset :subs
                                                (union-equal (mget :subs (mget p s))
                                                             topics)
                                                (mget p s))))))))

     (:prove :hints (("Goal" :use ((:instance
                                    prop=ordered-seenp-set-nsubs-sfn
                                    (s (mset p
                                             (mset :subs
                                                   (union-equal (mget :subs (mget p s))
                                                                topics)
                                                   (mget p s))
                                             s)))))))))

   (property prop=ordered-seenp-unsubscribe (s :s-fn p :peer topics :lot)
    :h (^ (mget p s)
          (ordered-seenp s))
    (ordered-seenp (unsubscribe-fn p topics s))
    :instructions
    (:pro
     (= (unsubscribe-fn p topics s)
        (set-subs-sfn (ps-fn-nbrs (mget p s))
                      topics
                      p
                      (mset p 
                            (mset :subs (set-difference-equal (mget :subs (mget p s))
                                                              topics)
                                  (mget p s))
                            s)))
     (:claim (orderedp (mget :seen (mget p s))))
     (:claim (== (mget :seen (mget p s))
                 (mget :seen (mset :subs
                                   (set-difference-equal (mget :subs (mget p s))
                                                topics)
                                   (mget p s)))))
     (:claim (orderedp (mget :seen (mset :subs
                                   (set-difference-equal (mget :subs (mget p s))
                                                topics)
                                   (mget p s)))))
     (:claim (ordered-seenp
              (mset p
                    (mset :subs
                          (set-difference-equal (mget :subs (mget p s))
                                                topics)
                          (mget p s))
                    s))
              :hints (("Goal" :use ((:instance
                                     prop=mset-ordered-seenp
                                     (pst (mset :subs
                                                (set-difference-equal (mget :subs (mget p s))
                                                                      topics)
                                                (mget p s))))))))

     (:prove :hints (("Goal" :use ((:instance
                                    prop=ordered-seenp-set-nsubs-sfn
                                    (s (mset p
                                             (mset :subs
                                                   (set-difference-equal (mget :subs (mget p s))
                                                                         topics)
                                                   (mget p s))
                                             s)))))))))

   (property prop=ordered-seenp-join
     (p :peer pubs subs :lot nbrs :lop s :s-fn)
     :h (^ (! (mget p s))
           (! (in p nbrs))
           (ordered-seenp s))
     (ordered-seenp (join-fn p pubs subs nbrs s))
     :instructions
     (:pro
      (= (join-fn p pubs subs nbrs s)
         (set-subs-sfn nbrs
                       subs
                       p
                       (mset p
                             (new-joinee-st-fn pubs subs nbrs s)
                             s)))
     (:claim (orderedp
              (mget :seen
                    (new-joinee-st-fn pubs subs nbrs s)))
             :hints (("Goal" :use ((:instance
                                    prop=orderedp-ps-fn-new-joinee-st)))))
     (:claim (ordered-seenp (mset p
                                  (new-joinee-st-fn pubs subs nbrs s)
                                  s))
             :hints (("Goal" :use ((:instance
                                    prop=mset-ordered-seenp
                                    (pst (new-joinee-st-fn
                                          pubs subs nbrs s)))))))
     (:prove :hints
             (("Goal" :use ((:instance
                             prop=ordered-seenp-set-nsubs-sfn
                             (s (mset p
                                      (new-joinee-st-fn pubs subs nbrs s)
                                      s)))))))))

   (property prop=ordered-seenp-s-fn-leave (s :s-fn p :peer)
     :h (^ (mget p s)
           (ordered-seenp s))
     (ordered-seenp (leave-fn p s))))

(in-theory (disable ordered-seenp))


(definec p!in-nsubs-ps-fn-help (p :peer nsubs :topic-lop-map) :bool
  (match nsubs
    (() t)
    (((& . ps) . rst)
     (^ (! (in p ps))
        (p!in-nsubs-ps-fn-help p rst)))))

(definec p!in-nsubs-ps-fn (p :peer st :ps-fn) :bool
  :body-contracts-hints (("Goal" :in-theory (enable ps-fnp)))
  (p!in-nsubs-ps-fn-help p (mget :nsubs st)))


(encapsulate ()
  (local
   (property prop=p!in-nsubs-ps-fn-help (p :peer tp :topic nsubs :topic-lop-map)
     :check-contracts? nil
     :h (p!in-nsubs-ps-fn-help p nsubs)
     (! (in p (mget tp nsubs)))))
  
  (property prop=p!in-nsubs-ps-fn (p :peer tp :topic st :ps-fn)
     :check-contracts? nil
     :h (p!in-nsubs-ps-fn p st)
     (! (in p (mget tp (mget :nsubs st))))))


(definec p!in-nsubs-s-fn (s :s-fn) :bool
  (match s
    (() t)
    (((p . pst) . rst)
     (^ (p!in-nsubs-ps-fn p pst)
        (p!in-nsubs-s-fn rst)))))

(propertyd prop=p!in-nsubs-s-fn (p :peer tp :topic s :s-fn)
  :check-contracts? nil
  :h (^ (mget p s)
        (p!in-nsubs-s-fn s))
  (! (in p (mget tp (mget :nsubs (mget p s))))))


(propertyd prop=p!in-nsubs-s-fn-produce (s :s-fn m :mssg)
  :check-contracts? nil
  :h (^ (p!in-nsubs-s-fn s)
        (produce-fn-pre m s))
  (p!in-nsubs-s-fn (produce-fn m s))
  :instructions
  (:pro (:dv 1) (:r produce-fn) :s :top
        :induct :pro
        (:claim (produce-fn-pre m (cdr s)))
        (:claim (p!in-nsubs-s-fn (cdr s)))
        (:claim (p!in-nsubs-s-fn (mset (mget :or m)
                                       (add-pending-psfn m (mget (mget :or m) (cdr s)))
                                       (cdr s))))
        (= (mset (mget :or m)
                 (add-pending-psfn m (mget (mget :or m) s))
                 s)
           (cons (car s)
                 (mset (mget :or m)
                       (add-pending-psfn m (mget (mget :or m) s))
                       (cdr s))))
        (= (mget (mget :or m) s)
           (mget (mget :or m) (cdr s)))
        (:claim (s-fnp (cons (car s)
                             (mset (mget :or m)
                                   (add-pending-psfn m (mget (mget :or m) (cdr s)))
                                   (cdr s)))))
        (= (^ (p!in-nsubs-ps-fn (caar s) (cdar s))
              (p!in-nsubs-s-fn (mset (mget :or m)
                                     (add-pending-psfn m (mget (mget :or m) (cdr s)))
                                     (cdr s)))))
        (:claim (p!in-nsubs-ps-fn (car (car s))
                                  (cdr (car s))))
        :s

        :pro
        (= (mget :or m) (caar s))
        (= (mget (car (car s)) s) (cdar s))
        (:claim (add-pending-psfn m (cdr (car s))))
        (= (add-pending-psfn m (cdar s))
           (mset :pending
                 (cons m (mget :pending (cdar s)))
                 (cdr (car s)))
           :hints (("Goal" :in-theory (enable add-pending-psfn))))
         (:dv 1) :r :s :s :up
         (= (mget :or m) (caar s))
         (:claim (p!in-nsubs-s-fn (cdr s)))
         (:claim (p!in-nsubs-ps-fn (car (car s))
                                   (cdr (car s))))
         :prove :bash :bash))


(encapsulate ()
  (local
   (property prop=p!in-nsubs-ps-fn-set-subs-help0
     (tp :topic topics :lot n p :peer acc :topic-lop-map ps :lop)
     :h (^ (p!in-nsubs-ps-fn-help n acc)
           (! (in n ps))
           (!= p n))
     (p!in-nsubs-ps-fn-help n
                            (mset tp ps acc))))

  (local
   (property prop=p!in-nsubs-ps-fn-set-subs-help1
     (tp :topic topics :lot n p :peer acc :topic-lop-map ps :lop)
     :h (^ (p!in-nsubs-ps-fn-help n acc)
           (! (in n ps))
           (!= p n))
     (p!in-nsubs-ps-fn-help n
                            (mset tp
                                  (union-equal (list p) ps)
                                  acc))))

  (local
   (property prop=p!in-nsubs-ps-fn-set-subs-help2
     (tp :topic topics :lot n p :peer acc :topic-lop-map ps :lop)
     :h (^ (p!in-nsubs-ps-fn-help n acc)
           (! (in n ps))
           (!= p n))
     (p!in-nsubs-ps-fn-help n
                            (mset tp
                                  (remove-equal p ps)
                                  acc))
     :instructions
     (:pro
      (:claim (! (in n (remove-equal p ps))))
      (:prove :hints (("Goal" :use ((:instance
                                     prop=p!in-nsubs-ps-fn-set-subs-help0
                                     (ps (remove-equal p ps))))))))))

  (local
   (property prop=p!in-nsubs-ps-fn-set-subs
     (topics :lot n p :peer nsubs acc :topic-lop-map)
     :h (^ (p!in-nsubs-ps-fn-help n nsubs)
           (p!in-nsubs-ps-fn-help n acc)
           (!= p n))
     (p!in-nsubs-ps-fn-help n (set-subs topics p nsubs acc))
     :instructions
     (:pro (:induct (set-subs topics p nsubs acc))
           :bash
           
           :pro
           (:dv 2) :r :s
           (:claim (p!in-nsubs-ps-fn-help n (cdr nsubs)))
           (:claim (p!in-nsubs-ps-fn-help
                    n
                    (set-subs topics p (cdr nsubs)
                              (if (in (car (car nsubs)) topics)
                                  (mset (car (car nsubs))
                                        (union-equal (list p) (cdr (car nsubs)))
                                        acc)
                                (mset (car (car nsubs))
                                      (remove-equal p (cdr (car nsubs)))
                                      acc)))))
           :top :bash

           :pro
           (= (set-subs topics p nsubs acc)
              acc
              :hints (("Goal" :in-theory (enable set-subs))))
           :prove)))

  (local
   (property prop=p!in-nsubs-ps-fn-set-nsubs (p n :peer st :ps-fn
                                                nbrs :lop topics :lot)
     :h (^ (p!in-nsubs-ps-fn n st)
           (! (in p nbrs)))
     (p!in-nsubs-ps-fn n (set-subs-psfn nbrs topics n p st))
     :instructions
     (:pro
      (= (set-subs-psfn nbrs topics n p st)
         (if (in n nbrs)
             (mset :nsubs (set-subs topics p (mget :nsubs st) '()) st)
           st)
         :hints (("Goal" :in-theory (enable set-subs-psfn))))
      (:casesplit (in n nbrs))
      :s

      (:claim (p!in-nsubs-ps-fn-help n nil))
      (:claim (p!in-nsubs-ps-fn-help n (mget :nsubs st)))
      (:claim (!= p n))
      (:claim (p!in-nsubs-ps-fn-help n (set-subs topics p (mget :nsubs st)
                                                 nil)))
      :prove
      :s)))

   (property prop=p!in-nsubs-s-fn-set-subs (nbrs :lop topics :lot p :peer s :s-fn)
     :h (^ (p!in-nsubs-s-fn s)
           (! (in p nbrs)))
     (p!in-nsubs-s-fn (set-subs-sfn nbrs topics p s))
     :instructions
     (:pro
      :induct :bash
      :pro
      (:claim (p!in-nsubs-s-fn (cdr s)))
      (:claim (p!in-nsubs-s-fn (set-subs-sfn nbrs topics p (cdr s))))
      (:dv 1) :r :s :up :r :s :prove
      (= (cons (cons (car (car s))
                     (set-subs-psfn nbrs topics (car (car s))
                                    p (cdr (car s))))
               (set-subs-sfn nbrs topics p (cdr s)))
         (set-subs-sfn nbrs topics p s)
         :hints (("Goal" :in-theory (enable set-subs-sfn))))
      :s :prove))

  (local
   (property not-in-union-equal (x y :tl p :all)
     (== (^ (! (in p x))
            (! (in p y)))
         (! (in p (union-equal x y))))))

  (local
   (property prop=p!in-nsubs-ps-fn-nbrs-help (p :peer nsubs :topic-lop-map acc :lop)
     :h (^ (! (in p acc))
           (p!in-nsubs-ps-fn-help p nsubs))
     (! (in p (ps-fn-nbrs-help nsubs acc)))
     :instructions
     (:pro :induct :bash
           :pro
           (:claim (p!in-nsubs-ps-fn-help p (cdr nsubs)))
           (:claim (! (in p (cdr (car nsubs)))))
           (:claim (! (in p (union-equal (cdr (car nsubs)) acc)))
                   :hints (("Goal" :use ((:instance not-in-union-equal
                                                    (x (cdr (car nsubs)))
                                                    (y acc))))))
           (:claim (not (in p
                            (ps-fn-nbrs-help (cdr nsubs)
                                             (union-equal (cdr (car nsubs)) acc)))))
           (:dv 1 2) :r :s :top :s

           :pro
           (= (ps-fn-nbrs-help nsubs acc)
              acc
              :hints (("Goal" :in-theory (enable ps-fn-nbrs-help))))
           :s)))

  (local
   (property prop=p!in-nsubs-ps-fn-nbrs (p :peer st :ps-fn)
     :h (p!in-nsubs-ps-fn p st)
     (! (in p (ps-fn-nbrs st)))
     :hints (("Goal" :in-theory (enable ps-fn-nbrs)))))

  (local
   (property prop=p!in-nsubs-s-fn-mset (p :peer ts :lot s :s-fn)
     :h (^ (mget p s)
           (p!in-nsubs-s-fn s))
     (p!in-nsubs-s-fn (mset p
                            (mset :subs ts (mget p s))
                            s))))
  
  (propertyd prop=p!in-nsubs-s-fn-subscribe (p :peer topics :lot s :s-fn)
     :h (^ (mget p s)
           (p!in-nsubs-s-fn s))
     (p!in-nsubs-s-fn (subscribe-fn p topics s))
     :instructions
     (:pro
      (= (subscribe-fn p topics s)
         (set-subs-sfn (ps-fn-nbrs (mget p s))
                       topics
                       p
                       (mset p 
                             (mset :subs (union-equal (mget :subs (mget p s))
                                                      topics)
                                   (mget p s))
                             s))
         :hints (("Goal" :in-theory (enable subscribe-fn))))

      (:claim (! (in p (ps-fn-nbrs (mget p s)))))
      (:claim (p!in-nsubs-s-fn (mset p
                                     (mset :subs
                                           (union-equal (mget :subs (mget p s))
                                                        topics)
                                           (mget p s))
                                     s)))
      :prove))


  (propertyd prop=p!in-nsubs-s-fn-unsubscribe (p :peer topics :lot s :s-fn)
    :h (^ (mget p s)
          (p!in-nsubs-s-fn s))
    (p!in-nsubs-s-fn (unsubscribe-fn p topics s))
    :instructions
    (:pro
     (= (unsubscribe-fn p topics s)
        (set-subs-sfn (ps-fn-nbrs (mget p s))
                      topics
                      p
                      (mset p 
                            (mset :subs (set-difference-equal
                                         (mget :subs (mget p s))
                                         topics)
                                  (mget p s))
                            s))
        :hints (("Goal" :in-theory (enable unsubscribe-fn))))

     (:claim (! (in p (ps-fn-nbrs (mget p s)))))
     (:claim (p!in-nsubs-s-fn (mset p
                                    (mset :subs
                                          (set-difference-equal
                                           (mget :subs (mget p s))
                                           topics)
                                          (mget p s))
                                    s)))
     :prove))

  (local
   (property prop=p!in-nsubs-ps-fn-calc-nsubs-fn
     (p :peer nbrs :lop s :s-fn acc :topic-lop-map)
     :h (^ (p!in-nsubs-ps-fn-help p acc)
           (! (in p nbrs)))
     (p!in-nsubs-ps-fn-help p (calc-nsubs-fn nbrs s acc))
     :instructions
     (:pro
      :induct :bash
      :pro
      (:claim (p!in-nsubs-ps-fn-help p nil))
      (:claim (!= p (car nbrs)))
      (:claim (p!in-nsubs-ps-fn-help p
                                     (set-subs (mget :subs
                                                     (mget (car nbrs)
                                                           s))
                                               (car nbrs)
                                               acc nil))
              :hints (("Goal" :use ((:instance prop=p!in-nsubs-ps-fn-set-subs
                                               (n p)
                                               (p (car nbrs))
                                               (nsubs acc)
                                               (acc nil))))))
      (:claim (p!in-nsubs-ps-fn-help
               p
               (calc-nsubs-fn (cdr nbrs)
                              s
                              (set-subs (mget :subs (mget (car nbrs) s))
                                        (car nbrs)
                                        acc nil))))
      (:dv 2) :r :s :top :s
      :pro
      (:claim (p!in-nsubs-ps-fn-help p (calc-nsubs-fn
                                        (cdr nbrs) s acc)))
      (:dv 2) :r :s :top :s
      :pro
      (= (calc-nsubs-fn nbrs s acc)
         acc
         :hints (("Goal" :in-theory (enable calc-nsubs-fn))))
      :s)))
  
  
  (local
   (property prop=p!in-nsubs-ps-fn-new-joinee-st
     (p :peer pubs subs :lot nbrs :lop s :s-fn)
     :h (! (in p nbrs))
     (p!in-nsubs-ps-fn p (new-joinee-st-fn pubs subs nbrs s))
     :instructions
     (:pro
      (:dv 2) (:r 2) :s :top
      :r :s
      (:casesplit (calc-nsubs-fn nbrs s nil)) :s
      (:claim (p!in-nsubs-ps-fn-help p nil))
      (:prove :hints
              (("Goal" :use ((:instance
                              prop=p!in-nsubs-ps-fn-calc-nsubs-fn
                              (acc nil))))))
      :s
      (:claim (p!in-nsubs-ps-fn-help p nil)) :s :s
      (:dv 1)
      (= (new-joinee-st-fn pubs subs nbrs s))
      :top :s)))

  (local
   (property prop=p!in-nsubs-s-fn-mset-pst (p :peer st :ps-fn s :s-fn)
     :h (^ (p!in-nsubs-ps-fn p st)
           (p!in-nsubs-s-fn s))
     (p!in-nsubs-s-fn (mset p st s))))


  (propertyd prop=p!in-nsubs-s-fn-join
    (p :peer pubs subs :lot nbrs :lop s :s-fn)
    :h (^ (! (mget p s))
          (! (in p nbrs))
          (p!in-nsubs-s-fn s))
    (p!in-nsubs-s-fn (join-fn p pubs subs nbrs s))
    :instructions
    (:pro
     (= (join-fn p pubs subs nbrs s)
        (set-subs-sfn nbrs
                      subs
                      p
                      (mset p
                            (new-joinee-st-fn pubs subs nbrs s)
                            s)))
     (:claim (p!in-nsubs-ps-fn p (new-joinee-st-fn pubs subs nbrs s))
             :hints (("Goal"
                      :use ((:instance
                             prop=p!in-nsubs-ps-fn-new-joinee-st)))))
     (:claim (p!in-nsubs-s-fn (mset p
                                    (new-joinee-st-fn
                                     pubs subs nbrs s)
                                    s))
             :hints (("Goal" :use ((:instance
                                    prop=p!in-nsubs-s-fn-mset-pst
                                    (st (new-joinee-st-fn
                                         pubs subs nbrs s)))))))
     
     (:prove :hints (("Goal" :use ((:instance prop=p!in-nsubs-s-fn-set-subs
                                              (topics subs)
                                              (s (mset p (new-joinee-st-fn pubs subs nbrs s)
                                                       s))))))))))



(property prop=p!in-nsubs-s-fn-leave (p :peer s :s-fn)
  :h (^ (mget p s)
        (p!in-nsubs-s-fn s))
  (p!in-nsubs-s-fn (leave-fn p s))
  :instructions
  (:pro :induct :bash
        :pro
        (:claim (p!in-nsubs-s-fn (cdr s)))
        (:claim (p!in-nsubs-s-fn (leave-fn p (cdr s))))
        (:dv 1) (:r 2) :s :top
        (:casesplit (equal (car (car s)) p)) :s
        :s :r :s :bash
        (= (cons (car s) (leave-fn p (cdr s)))
           (leave-fn p s))
        :s :bash :bash))


(encapsulate ()
  (local
   (property prop=p!in-nsubs-s-fn-forwarder-new-pst (p :peer m :mssg st :ps-fn)
     :h (p!in-nsubs-ps-fn p st)
     (p!in-nsubs-ps-fn p (forwarder-new-pst st m))
     :instructions
     (:pro
      (:dv 2) (:r forwarder-new-pst) :s :top
      (:r p!in-nsubs-ps-fn)
      (:claim (ps-fnp (mset :pending
                            (remove-equal m (mget :pending st))
                            (mset :seen (insert-unique m (mget :seen st))
                                  st))))
      :s :bash)))

  (local
   (property prop=p!in-nsubs-s-fn-update-forwarder
     (p :peer m :mssg s :s-fn)
     :h (^ (mget p s)
           (in m (mget :pending (mget p s)))
           (p!in-nsubs-s-fn s))
     (p!in-nsubs-s-fn (update-forwarder-fn p m s))
     :instructions
     (:pro :induct :bash
           :pro
           (:claim (mget p (cdr s)))
           (:claim (in m (mget :pending (mget p (cdr s)))))
           (:claim (p!in-nsubs-s-fn (cdr s)))
           (:claim (p!in-nsubs-s-fn (update-forwarder-fn p m (cdr s))))
           (:dv 1) (:r update-forwarder-fn) :s :up
           (:casesplit (equal (car (car s)) p)) :s :bash
           :s :r :s :bash :prove
           :pro
           (:dv 1) (:r update-forwarder-fn)
           :s :up :bash :bash)))

  (local
   (property prop=p!in-nsubs-s-fn-forward-help (m :mssg nbrs :lop s :s-fn)
     :h (p!in-nsubs-s-fn s)
     (p!in-nsubs-s-fn (forward-help-fn s nbrs m))
     :instructions
     (:pro
      :induct :pro :bash
      :pro
      (:claim (p!in-nsubs-s-fn (cdr s)))
      (:claim (p!in-nsubs-s-fn (forward-help-fn (cdr s) nbrs m)))
      (:dv 1) (:r forward-help-fn) :s :up

      (:casesplit (in (car (car s)) nbrs)) :s
      :r :s
      (:claim (ps-fnp (add-pending-psfn m (cdr (car s)))))
      (:claim (s-fnp (cons (cons (car (car s))
                                 (add-pending-psfn m (cdr (car s))))
                           (forward-help-fn (cdr s) nbrs m)))
              :hints (("Goal" :in-theory (enable forward-help-fn))))
      
      (= (^ (p!in-nsubs-ps-fn (caar s) (add-pending-psfn m (cdr (car s))))
            (p!in-nsubs-s-fn (forward-help-fn (cdr s) nbrs m))))
      (:claim (== (mget :nsubs (add-pending-psfn m (cdr (car s))))
                  (mget :nsubs (cdr (car s))))
              :hints (("Goal" :in-theory (enable add-pending-psfn))))
      :s :bash

      (= (cons (cons (car (car s))
                     (add-pending-psfn m (cdr (car s))))
               (forward-help-fn (cdr s) nbrs m))
         (forward-help-fn s nbrs m)
         :hints (("Goal" :in-theory (enable forward-help-fn))))
      :s :s
      (:claim (s-fnp (cons (car s)
                           (forward-help-fn (cdr s) nbrs m)))
              :hints (("Goal" :in-theory (enable forward-help-fn))))
      (= (^ (p!in-nsubs-ps-fn (caar s) (cdr (car s)))
            (p!in-nsubs-s-fn (forward-help-fn (cdr s) nbrs m))))
      :bash :s
      :pro
      (:prove :hints (("Goal" :in-theory (enable forward-help-fn)))))))

  (propertyd prop=p!in-nsubs-s-fn-forward (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s)))
          (p!in-nsubs-s-fn s))
    (p!in-nsubs-s-fn (forward-fn p m s))
    :instructions
    (:pro
     
     (= (forward-fn p m s)
        (forward-help-fn (update-forwarder-fn p m s)
                         (mget (mssg-tp m)
                               (mget :nsubs (mget p s)))
                         m)
        :hints (("Goal" :in-theory (enable forward-fn))))

     (:claim (p!in-nsubs-s-fn (update-forwarder-fn p m s)))

     (:prove :hints (("Goal"
                      :use ((:instance prop=p!in-nsubs-s-fn-forward-help
                                       (s (update-forwarder-fn p m s))
                                       (nbrs (mget (mssg-tp m)
                                                   (mget :nsubs (mget p s))))))))))))


  
(definec good-s-fnp (s :s-fn) :bool
  (^ (p!in-nsubs-s-fn s)
     (ordered-seenp s)))


(in-theory (disable new-fn-mssgp produce-fn
                    produce-fn-pre
                    subscribe-fn
                    unsubscribe-fn p!in-nsubs-ps-fn-help
                    set-subs-sfn p!in-nsubs-ps-fn
                    leave-fn p!in-nsubs-s-fn
                    ordered-seenp join-fn
                    acl2::maximal-records-theory))


(property prop=good-s-fn2 (p :peer tp :topic s :s-fn)
  :check-contracts? nil
  :h (^ (mget p s)
        (good-s-fnp s))
  (! (in p (mget tp (mget :nsubs (mget p s)))))
  :hints (("Goal" :use ((:instance prop=p!in-nsubs-s-fn)))))

(property prop=good-s-fn3 (p :peer s :s-fn)
  :h (^ (mget p s)
        (good-s-fnp s))
  (orderedp (mget :seen (mget p s)))
  :hints (("Goal" :in-theory (enable ordered-seenp
                                     acl2::maximal-records-theory))))


(property prop=good-s-fn-produce (s :s-fn m :mssg)
  :check-contracts? nil
  :h (^ (good-s-fnp s)
        (produce-fn-pre m s))
  (good-s-fnp (produce-fn m s))
  :hints (("Goal" :use ((:instance prop=p!in-nsubs-s-fn-produce)
                        (:instance prop=ordered-seenp-s-fn-produce)))))


(property prop=good-s-fn-forward (p :peer m :mssg s :s-fn)
  :check-contracts? nil
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (good-s-fnp s))
  (good-s-fnp (forward-fn p m s))
  :hints (("Goal" :use ((:instance prop=p!in-nsubs-s-fn-forward)
                        (:instance prop=ordered-seenp-forward-fn)))))

(property prop=good-s-fn-subscribe (s :s-fn p :peer topics :lot)
  :h (^ (mget p s)
        (good-s-fnp s))
  (good-s-fnp (subscribe-fn p topics s))
  :hints (("Goal" :use ((:instance prop=p!in-nsubs-s-fn-subscribe)
                        (:instance prop=ordered-seenp-subscribe)))))

(property prop=good-s-fn-unsubscribe (s :s-fn p :peer topics :lot)
  :h (^ (mget p s)
        (good-s-fnp s))
  (good-s-fnp (unsubscribe-fn p topics s))
  :hints (("Goal" :use ((:instance prop=p!in-nsubs-s-fn-unsubscribe)
                        (:instance prop=ordered-seenp-unsubscribe)))))

(property prop=good-s-fn-join (p :peer pubs subs :lot nbrs :lop s :s-fn)
  :h (^ (! (mget p s))
        (! (in p nbrs))
        (good-s-fnp s))
  (good-s-fnp (join-fn p pubs subs nbrs s))
  :instructions
  (:pro
   (:claim (^ (p!in-nsubs-s-fn s)
              (ordered-seenp s)))
           
   (:claim (ordered-seenp (join-fn p pubs subs nbrs s))
           :hints (("Goal" :use ((:instance prop=ordered-seenp-join)))))
   (:claim (p!in-nsubs-s-fn (join-fn p pubs subs nbrs s))
           :hints (("Goal" :use ((:instance prop=p!in-nsubs-s-fn-join)))))
   :bash))

(in-theory (disable good-s-fnp new-fn-mssgp produce-fn produce-fn-pre
                   acl2::maximal-records-theory subscribe-fn
                   unsubscribe-fn set-subs-sfn leave-fn
                   join-fn ordered-seenp))
