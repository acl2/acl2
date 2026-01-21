(in-package "ACL2S")
(include-book "bn-trx")
(include-book "fn-trx")

(definecd f2b-st (ps :ps-fn ms :lom) :ps-bn
  (ps-bn (mget :pubs ps)
         (mget :subs ps)
         (set-difference-equal (mget :seen ps) ms)))

(property prop=f2b-st-check (ps :ps-fn ms :lom)
  (^ (== (mget :pubs (f2b-st ps ms))
         (mget :pubs ps))
     (== (mget :subs (f2b-st ps ms))
         (mget :subs ps))
     (== (mget :seen (f2b-st ps ms))
         (set-difference-equal (mget :seen ps) ms)))
  :hints (("Goal" :in-theory (enable f2b-st ps-fnp ps-bnp))))

(property prop=f2b-st-check2 (ps :ps-fn)
  (^ (== (mget :pubs (f2b-st ps '()))
         (mget :pubs ps))
     (== (mget :subs (f2b-st ps '()))
         (mget :subs ps))
     (== (mget :seen (f2b-st ps '()))
         (mget :seen ps))))

(property prop=f2b-st-set-subs-psfn (nbrs :lop subs :lot n p :peer pst :ps-fn ms :lom)
  (== (f2b-st (set-subs-psfn nbrs subs n p pst) ms)
      (f2b-st pst ms))
  :hints (("Goal" :in-theory (enable f2b-st set-subs-psfn))))

(property prop=f2b-st-ignore-pending-mset (p :peer s :s-fn ms ls :lom pst :ps-fn)
          (== (f2b-st (mset :pending ms pst) ls)
              (f2b-st pst ls))
          :hints (("Goal" :in-theory (enable f2b-st))))

(property prop=f2b-st-add-pending (m :mssg pst :ps-fn ms :lom)
  (== (f2b-st (add-pending-psfn m pst) ms)
      (f2b-st pst ms))
  :hints (("Goal" :in-theory (enable f2b-st add-pending-psfn))))

(property prop=f2b-st-forwarder (m :mssg pst :ps-fn ms :lom)
  :h (in m ms)
  (equal (f2b-st (forwarder-new-pst pst m) ms)
         (f2b-st pst ms))
  :hints (("Goal" :in-theory (enable f2b-st forwarder-new-pst))))

;; We now define our refinement map f2b
(definec f2b-help (s :s-fn ms :lom) :s-bn
  :function-contract-hints (("Goal" :in-theory (enable
                                                f2b-st-contract
                                                acl2::maximal-records-theory)))
  (if (endp s)
      '()
    (cons `(,(caar s) . ,(f2b-st (cdar s) ms))
          (f2b-help (cdr s) ms))))

(property f2b-st-new-pending-mssg (s :s-fn m :mssg ms :lom)
  :h (^ (consp s)
        (new-fn-mssgp m s))
  (== (f2b-st (cdr (car s)) (insert-unique m ms))
      (f2b-st (cdr (car s)) ms))
  :hints (("Goal" :in-theory (enable new-fn-mssgp f2b-st ps-bnp)
           :use ((:instance insert-unique-diff-in (x (mget :seen (cdr (car s))))
                            (y ms))))))

(property f2b-help-new-pending-mssg (s :s-fn m :mssg ms :lom)
  :h (new-fn-mssgp m s)
  (== (f2b-help s (insert-unique m ms))
      (f2b-help s ms))
  :hints (("Goal" :in-theory (enable new-fn-mssgp
                                     acl2::maximal-records-theory))))

(definec f2b (s :s-fn) :s-bn
  (f2b-help s (fn-pending-mssgs s)))

(property prop=f2b-help-mset (s :s-fn p :peer pst :ps-fn ms :lom)
  (== (f2b-help (mset p pst s) ms)
      (mset p (f2b-st pst ms) (f2b-help s ms)))
  :hints (("Goal" :in-theory (enable acl2::maximal-records-theory))))

(property prop=f2b-mset (s :s-fn p :peer pst :ps-fn)
  :h (== (fn-pending-mssgs (mset p pst s))
         (fn-pending-mssgs s))
  (== (f2b (mset p pst s))
      (mset p (f2b-st pst (fn-pending-mssgs s)) (f2b s))))
                      

;; mget traversal properties
(encapsulate ()
  (local
   (in-theory (enable acl2::maximal-records-theory)))

  (property prop=f2b-st-f2b-mget (s :s-fn p :peer ms :lom)
            :h (mget p s)
            (== (mget p (f2b-help s ms))
                (f2b-st (mget p s) ms))
            :hints (("Goal" :in-theory (enable ps-bnp))))
  
  (property prop=f2b-car (s :s-fn)
            (== (caar (f2b s))
                (caar s)))

  (property prop=f2b-cdar (s :s-fn)
    :h (consp s)
    (== (cdar (f2b s))
        (f2b-st (cdar s)
                (fn-pending-mssgs s)))))


(encapsulate ()
   (property prop=f2b-help-set-subs-sfn
     (nbrs :lop subs :lot p :peer s :s-fn ms :lom)
     (== (f2b-help (set-subs-sfn nbrs subs p s) ms)
         (f2b-help s ms))
     :instructions
     (:induct :pro :bash
              (:dv 1 1 1) :r :top :s
              :bash
              (:dv 1 1 1 1) :r :top :s
              :bash :r :s :bash
              :pro
              (:dv 1 1) :r :top :s))

  (property prop=f2b-set-subs-sfn (s :s-fn p :peer nbrs :lop subs :lot )
    (== (f2b (set-subs-sfn nbrs subs p s))
        (f2b s)))

  (local
   (in-theory (enable acl2::maximal-records-theory)))
  
  (property prop=mget-f2b-pdg-irrelevance (p :peer s :s-fn ms ns :lom)
    :h (mget p (f2b-help s ms))
    (mget p (f2b-help s ns)))

  (property prop=mget-f2b=>mget (s :s-fn p :peer)
    :h (mget p (f2b s))
    (mget p s)
    :instructions
    (:pro :induct :pro
          (:claim (mget p (cdr (f2b s))))
          (:claim (mget p (f2b-help (cdr s)
                                    (fn-pending-mssgs s))))
          (:claim (mget p (f2b-help (cdr s) (fn-pending-mssgs (cdr s)))))
          (:claim (mget p (f2b (cdr s))))
          (:claim (mget p (cdr s)))
          (:r 2) :s :pro :bash
          :pro (:claim nil) :s)))

(property prop=f2b-help-cdr (s :s-fn x :lom)
  (== (cdr (f2b-help s x))
      (f2b-help (cdr s) x)))

(property prop=mget=>mget-f2b (s :s-fn p :peer)
  :h (mget p s)
  (mget p (f2b s)))

(propertyd prop=mget-f2b=mget (s :s-fn p :peer)
  (iff (mget p s)
       (mget p (f2b s))))

(propertyd prop=not-mget=not-mget-f2b (s :s-fn p :peer)
          (== (! (mget p s))
              (! (mget p (f2b s)))))



;;===== BROADCAST-BN HYPS =========                          

(encapsulate ()
  (local
   (in-theory (enable new-fn-mssgp new-bn-mssgp)))

  (local
   (property prop=in-member (x :tl m :all)
     (iff (in m x)
          (member-equal m x))))
     
  (property prop=in-fn-pending=>new-bn-mssgp-help (s :s-fn m :mssg ms :lom)
    :h (in m ms)
    (new-bn-mssgp m (f2b-help s ms))
    :instructions
    (:pro  
     :induct :pro
     (:claim (consp (f2b-help s ms)))
     (:claim (new-bn-mssgp m (f2b-help (cdr s) ms)))
     (:r new-bn-mssgp) :s
     (:dv 2 2 1 1) :r :s :up :up :s :top
     (:claim (member-equal m ms)) :bash
     :pro :bash))
  
  (local
   (in-theory (disable prop=in-member)))
   
  (property prop=in-fn-pending=>new-bn-mssgp (s :s-fn m :mssg)
    :h (in m (fn-pending-mssgs s))
    (new-bn-mssgp m (f2b s)))

  (local
   (property h10 (w :s-fn x y :lom m :mssg)
     :h (! (in m x))
     (== (new-bn-mssgp m (f2b-help w (union-set x y)))
         (new-bn-mssgp m (f2b-help w y)))
     :instructions
     (:pro
      (:induct (f2b-help w y)) :pro
      (:casesplit (consp (f2b-help w (union-set x y))))
      (:dv 1) (:r 3) :s
      (= (cdr (f2b-help w (union-set x y)))
         (f2b-help (cdr w) (union-set x y)))
      (:claim (equal (new-bn-mssgp m (f2b-help (cdr w) (union-set x y)))
                     (new-bn-mssgp m (f2b-help (cdr w) y))))
      (= (new-bn-mssgp m (f2b-help (cdr w) (union-set x y)))
         (new-bn-mssgp m (f2b-help (cdr w) y)))

      (= (cdr (car (f2b-help w (union-set x y))))
         (f2b-st (cdr (car w)) (union-set x y)))
      (= (mget :seen (f2b-st (cdr (car w))(union-set x y)))
         (set-difference-equal (mget :seen (cdr (car w)))
                               (union-set x y))
         :hints (("Goal" :use ((:instance prop=f2b-st-check
                                          (ps (cdr (car w)))
                                          (ms (union-set x y)))))))
      (:claim (not (in m x)))
      (:dv 1) :r
      (= (in m (set-difference-equal (mget :seen (cdr (car w)))
                                     (union-set x y)))
         (in m (mget :seen (cdr (car (f2b-help w y)))))
         :hints (("Goal" :use ((:instance prop=in-set-difference-union2
                                          (z (mget :seen (cdr (car w)))))))))
      :top
      (:claim (consp (f2b-help w y)))
      (:dv 2) (:r 2) :s :top :s
      :bash :bash :bash)))

  (propertyd prop=f2b-cons (w :s-fn)
    :h w
    (f2b w))

  (propertyd prop=new-fn-mssgp-def (w :s-fn m :mssg)
    (== (new-fn-mssgp m w)
        (^ (! (in m (mget :seen (cdr (car w)))))
           (! (in m (mget :pending (cdr (car w)))))
           (new-fn-mssgp m (cdr w))))
    :hints (("Goal" :in-theory (enable new-fn-mssgp))))

  (propertyd prop=demorgan (a b c :all)
    (=> (not (and (not a) (not b) c))
        (or a b (not c))))

  (propertyd prop=!new-fn-mssgp-def (w :s-fn m :mssg)
    (=> (! (new-fn-mssgp m w))
        (or (in m (mget :seen (cdr (car w))))
            (in m (mget :pending (cdr (car w))))
            (not (new-fn-mssgp m (cdr w)))))
    :instructions
    (:pro
     (:claim (! (^ (nin m (mget :seen (cdr (car w))))
                   (nin m (mget :pending (cdr (car w))))
                   (new-fn-mssgp m (cdr w))))
             :hints (("Goal" :use ((:instance prop=new-fn-mssgp-def)))))
     (:claim (or (in m (mget :seen (cdr (car w))))
                 (in m (mget :pending (cdr (car w))))
                 (not (new-fn-mssgp m (cdr w))))
             :hints (("Goal" :use
                      ((:instance prop=demorgan
                                  (a (in m (mget :seen (cdr (car
                                                                       w)))))
                                  (b (in m (mget :pending (cdr (car
                                                                          w)))))
                                  (c (new-fn-mssgp m (cdr w))))))))
     (:demote 5) :s))
  
  (property prop=new-bn-mssgp=>in-fn-pending (w :s-fn m :mssg)
    :h (^ (new-bn-mssgp m (f2b w))
          (! (new-fn-mssgp m w)))
    (in m (fn-pending-mssgs w))
    :instructions
    (:pro
     :induct :bash :pro
     (:claim (or (in m (mget :seen (cdr (car w))))
                 (in m (mget :pending (cdr (car w))))
                 (not (new-fn-mssgp m (cdr w))))
     :hints (("Goal" :use ((:instance prop=!new-fn-mssgp-def)))))
    
    (:casesplit (in m (mget :pending (cdr (car w)))))
    (:claim (in m (mget :pending (cdr (car w)))))
    (= (fn-pending-mssgs w)
       (union-set (mget :pending (cdr (car w)))
                  (fn-pending-mssgs (cdr w)))
       :hints (("Goal" :use ((:instance fn-pending-mssgs-definition-rule
                                        (s w))))))
    (:claim (tlp (mget :pending (cdr (car w)))))
    (:prove :hints (("Goal" :use ((:instance in-union
                                             (x (mget :pending (cdr (car w))))
                                             (y (fn-pending-mssgs (cdr
                                                                   w))))))))

     (:casesplit (in m (mget :seen (cdr (car w)))))
     (:claim w)
     (:claim (f2b w)
             :hints (("Goal" :use ((:instance prop=f2b-cons)))))

     (:demote 7)
     (:dv 1) (:r new-bn-mssgp) :s
     (= (f2b-help w (fn-pending-mssgs w)) (f2b w)
        :hints (("Goal" :use ((:instance f2b-definition-rule (s w))))))
     (= (cdr (car (f2b w)))
        (f2b-st (cdr (car w)) (fn-pending-mssgs w))
        :hints (("Goal" :use ((:instance prop=f2b-cdar (s w))))))
     (:claim (ps-fnp (cdr (car w))))
     (= (f2b-st (cdr (car w))
                (fn-pending-mssgs w))
        (ps-bn (mget :pubs (cdr (car w)))
               (mget :subs (cdr (car w)))
               (set-difference-equal (mget :seen (cdr (car w)))
                                     (fn-pending-mssgs w)))
        :hints (("Goal" :use ((:instance f2b-st-definition-rule
                                         (ps (cdr (car w)))
                                         (ms (fn-pending-mssgs w)))))))
     :s :top :pro
     
     (:prove :hints (("Goal" :use ((:instance in-diff1
                                              (x (mget :seen (cdr (car w))))
                                              (y (fn-pending-mssgs w)))))))

     (:claim (not (new-fn-mssgp m (cdr w))))
     (:claim (== (f2b (cdr w))
                 (f2b-help (cdr w) (fn-pending-mssgs (cdr w))))
             :hints (("Goal" :use ((:instance f2b-definition-rule
                                              (s (cdr w)))))))
     (:demote 7) (:dv 1)
     (= (f2b w)
        (f2b-help w (fn-pending-mssgs w))
        :hints (("Goal" :use ((:instance f2b-definition-rule (s w))))))
     
     (= (fn-pending-mssgs w)
        (union-set (mget :pending (cdr (car w)))
                   (fn-pending-mssgs (cdr w)))
        :hints (("Goal" :use ((:instance fn-pending-mssgs-definition-rule
                                         (s w))))))
     :top
     (:claim (ps-fnp (cdr (car w))))
     (:claim (lomp (mget :pending (cdr (car w)))))
     (= (new-bn-mssgp m
                       (f2b-help w
                                 (union-set (mget :pending (cdr (car w)))
                                            (fn-pending-mssgs (cdr w)))))
        (new-bn-mssgp m (f2b-help w (fn-pending-mssgs (cdr w))))
        :hints (("Goal" :use ((:instance h10
                                         (x (mget :pending (cdr (car w))))
                                         (y (fn-pending-mssgs (cdr w))))))))
     (:dv 1) (:r new-bn-mssgp) :s :top :pro
     (:claim (in m (fn-pending-mssgs (cdr w))))
     (:claim (in m (union-set (fn-pending-mssgs (cdr w))
                              (mget :pending (cdr (car w)))))
             :hints (("Goal" :in-theory (disable prop=in-member in-union)
                      :use ((:instance in-union
                                       (x (fn-pending-mssgs (cdr w)))
                                       (y (mget :pending (cdr (car w)))))))))
     (= (fn-pending-mssgs w)
        (union-set (mget :pending (cdr (car w)))
                   (fn-pending-mssgs (cdr w)))
        :hints (("Goal" :use ((:instance fn-pending-mssgs-definition-rule
                                         (s w))))))
     (= (union-set (mget :pending (cdr (car w)))
                   (fn-pending-mssgs (cdr w)))
        (union-set (fn-pending-mssgs (cdr w))
                   (mget :pending (cdr (car w))))
        :hints (("Goal" :use ((:instance union-set-symm
                                         (x (mget :pending (cdr (car w))))
                                         (y (fn-pending-mssgs (cdr w))))))))
     :s :bash))
    
  
  (property prop=new-mssg-fn-pending-mssgs (s :s-fn m :mssg)
    :h (new-fn-mssgp m s)
    (! (in m (fn-pending-mssgs s)))
    :instructions
    (:pro
     :induct :bash :pro
     (:claim (not (in m (mget :pending (cdr (car s))))))
     (:claim (not (in m (fn-pending-mssgs (cdr s)))))
     (:claim (not (in m (union-set (mget :pending (cdr (car s)))
                                   (fn-pending-mssgs (cdr s)))))
             :hints (("Goal" :use ((:instance not-in-union
                                              (x (mget :pending (cdr (car s))))
                                              (y (fn-pending-mssgs (cdr s))))))))
     
     (:dv 1 2) (:r 2) :s :top :s
     :pro :bash))

  (local
   (property prop=new-bn-mssgp-cdr (m :mssg s :s-fn)
     :h (^ (! (in m (mget :pending (cdr (car s)))))
           (new-bn-mssgp m (f2b-help (cdr s) (fn-pending-mssgs (cdr s)))))
     (new-bn-mssgp m (f2b-help (cdr s) (fn-pending-mssgs s)))
     :instructions
     (:pro
      (:claim (new-bn-mssgp m (f2b-help (cdr s)
                                        (union-set (mget :pending (cdr (car s)))
                                                   (fn-pending-mssgs (cdr s)))))
              :hints (("Goal" :use ((:instance h10 (w (cdr s))
                                               (x (mget :pending (cdr (car s))))
                                               (y (fn-pending-mssgs (cdr
                                                                     s))))))))
      (:demote 5) (:dv 1 2 2)
      (= (fn-pending-mssgs s))
      :top :s)))
  
  (property prop=f2b-broadcast-help (s :s-fn m :mssg)
    :h (new-fn-mssgp m s)
    (new-bn-mssgp m (f2b s))
    :instructions
    (:pro
     :induct :bash :pro
     (:claim (^ (nin m (mget :seen (cdar s)))
                (nin m (mget :pending (cdar s)))
                (new-fn-mssgp m (cdr s))))
     :s :pro
     (:claim (^ (nin m (mget :seen (cdar s)))
                (nin m (mget :pending (cdar s)))
                (new-fn-mssgp m (cdr s))))
     :s :pro
     (:claim (new-bn-mssgp m (f2b (cdr s))))
     (:r new-bn-mssgp) :s
     (:claim (consp (f2b-help s (fn-pending-mssgs s))))
     (:claim (! (in m (mget :seen (cdr (car s))))))
     (:claim (! (in m (mget :seen
                            (cdar (f2b-help s (fn-pending-mssgs s)))))))
     (:claim (nin m (mget :seen
                          (cdar (f2b-help s (fn-pending-mssgs s))))))
     :s
     (:claim (new-bn-mssgp m (f2b-help (cdr s) (fn-pending-mssgs (cdr s)))))
     (:claim (! (in m (mget :pending (cdr (car s))))))
     (:claim (new-bn-mssgp m (f2b-help (cdr s) (fn-pending-mssgs s)))
             :hints (("Goal" :use ((:instance prop=new-bn-mssgp-cdr)))))
             
     :s :pro :bash)))

(property prop=f2b-broadcast-hyps (s :s-fn m :mssg)
  :h (^ (mget (mget :or m) s)
        (in (mget :tp m)
            (mget :pubs (mget (mget :or m) s))))
  (^ (mget (mget :or m) (f2b s))
     (in (mget :tp m)
         (mget :pubs (mget (mget :or m) (f2b s)))))
  :instructions
  (:pro
   (:claim (mget (mget :or m) (f2b s)))
   :s))
           
(propertyd prop=f2b-produce-hyps (s :s-fn m :mssg)
  :h (^ (mget (mget :or m) (f2b s))
        (in (mget :tp m)
            (mget :pubs (mget (mget :or m) (f2b s)))))
  (^ (mget (mget :or m) s)
     (in (mget :tp m)
         (mget :pubs (mget (mget :or m) s))))
  :hints (("Goal" :in-theory (enable prop=mget-f2b=mget))))


;;===== PRODUCE - F2B =========                          

(property prop=f2b-produce-fn (s :s-fn m :mssg)
  :check-contracts? nil
  :h (^ (mget (mget :or m) s)
        (new-fn-mssgp m s)
        (in (mget :tp m)
            (mget :pubs (mget (mget :or m) s))))
  (== (f2b (produce-fn m s))
      (f2b s))
  :instructions
  (:pro
   (:dv 1 1)
   (:r 2) :s :up (:r 2) :s
   (:claim (! (v (in m (mget :pending (mget (mget :or m) s)))
                 (in m (mget :seen (mget (mget :or m) s)))))
           :hints (("Goal" :use ((:instance new-mssg=>not-seen-peer
                                            (p (mget :or m)))))))                  

   (:claim (== (add-pending-psfn m (mget (mget :or m) s))
               (mset :pending
                     (cons m (mget :pending (mget (mget :or m) s)))
                     (mget (mget :or m) s)))
           :hints (("Goal" :in-theory (enable add-pending-psfn))))
   
   (= (add-pending-psfn m (mget (mget :or m) s))
      (mset :pending
            (cons m (mget :pending (mget (mget :or m) s)))
            (mget (mget :or m) s)))
      
   
   (:claim (== (fn-pending-mssgs
                (mset (mget :or m)
                      (mset :pending
                            (cons m (mget :pending (mget (mget :or m) s)))
                            (mget (mget :or m) s))
                      s))
               (insert-unique m (fn-pending-mssgs s)))
           :hints (("Goal" :use ((:instance prop=fn-pending-mssgs-mset-pending
                                            (p (mget :or m)))))))
   
   (= (fn-pending-mssgs
       (mset (mget :or m)
             (mset :pending
                   (cons m (mget :pending (mget (mget :or m) s)))
                   (mget (mget :or m) s))
             s))
      (insert-unique m (fn-pending-mssgs s)))

   (:claim (== (f2b-st (mget (mget :or m) s)
                       (insert-unique m (fn-pending-mssgs s)))
               (mget (mget :or m) (f2b-help s (insert-unique m (fn-pending-mssgs s)))))
           :hints (("Goal" :use ((:instance prop=f2b-st-f2b-mget
                                            (p (mget :or m))
                                            (ms (insert-unique m
                                                               (fn-pending-mssgs s))))))))
   (= (f2b-st (mget (mget :or m) s)
              (insert-unique m (fn-pending-mssgs s)))
      (mget (mget :or m) (f2b-help s (insert-unique m (fn-pending-mssgs
                                                       s)))))

   :r :top :bash :bash))

;;---- SUBSCRIBE ------

(property prop=f2b-st-mset-subs (pst :ps-fn subs :lot ms :lom)
  (== (f2b-st (mset :subs subs pst) ms)
      (mset :subs subs (f2b-st pst ms)))
  :hints (("Goal" :in-theory (enable f2b-st))))

(property prop=f2b-subscribe-fn (s :s-fn p :peer topics :lot)
          :h (mget p s)
          (== (f2b (subscribe-fn p topics s))
              (subscribe-bn p topics (f2b s)))
          :instructions
          (:pro (:dv 1 1)
                (:rewrite subscribe-fn) :s :up
                (:rewrite prop=f2b-set-subs-sfn)
                (:rewrite prop=f2b-mset)
                (:dv 2) (:rewrite prop=f2b-st-mset-subs)
                (= (mget :subs (mget p s))
                   (mget :subs (mget p (f2b s))))
                :s
                :top (:dv 2)
                (:rewrite subscribe-bn) :s :top :s
                (:repeat :bash)))

;;---- UNSUBSCRIBE ------

(property prop=f2b-unsubscribe-fn (s :s-fn p :peer topics :lot)
          :h (mget p s)
          (== (f2b (unsubscribe-fn p topics s))
              (unsubscribe-bn p topics (f2b s)))
          :instructions
          (:pro (:dv 1 1)
                (:rewrite unsubscribe-fn) :s :up
                (:rewrite prop=f2b-set-subs-sfn)
                (:rewrite prop=f2b-mset)
                (:dv 2) (:rewrite prop=f2b-st-mset-subs)
                (= (mget :subs (mget p s))
                   (mget :subs (mget p (f2b s))))
                :s
                :top (:dv 2)
                (:rewrite unsubscribe-bn) :s :top :s
                (:repeat :bash)))

;;---- JOIN ------

(property prop=f2b-join-pending-mssgs (p :peer pubs subs :lot nbrs :lop s :s-fn)
  :h (^ (! (mget p s))
        (! (in p nbrs)))
  (== (fn-pending-mssgs (join-fn p pubs subs nbrs s))
      (fn-pending-mssgs s))
  :instructions
  (:pro
   (= (join-fn p pubs subs nbrs s)
      (set-subs-sfn nbrs
                subs
                p
                (mset p
                      (new-joinee-st-fn pubs subs nbrs s)
                      s))
      :hints (("Goal" :in-theory (enable join-fn))))
   (:dv 1)
   (:rewrite prop=pending-mssgs-set-topics-subscribe)
   (:rewrite prop=fn-pending-mssgs-mset-pending-new)
   :top :s :bash :bash))


(property prop=f2b-join-mset (p :peer pubs subs :lot nbrs :lop s :s-fn)
  :h (^ (! (mget p s))
        (! (in p nbrs)))
  (== (f2b (join-fn p pubs subs nbrs s))
      (mset p
            (f2b-st (new-joinee-st-fn pubs subs nbrs s)
                    (fn-pending-mssgs s))
            (f2b s)))
  :instructions
  (:pro
   (= (f2b (join-fn p pubs subs nbrs s))
      (f2b-help (join-fn p pubs subs nbrs s)
                (fn-pending-mssgs (join-fn p pubs subs nbrs s))))
   (= (fn-pending-mssgs (join-fn p pubs subs nbrs s))
      (fn-pending-mssgs s)
      :hints (("Goal" :use ((:instance prop=f2b-join-pending-mssgs)))))
   
   (= (join-fn p pubs subs nbrs s)
      (set-subs-sfn nbrs
                subs
                p
                (mset p
                      (new-joinee-st-fn pubs subs nbrs s)
                      s))
      :hints (("Goal" :in-theory (enable join-fn))))
   (:dv 1) (:rewrite prop=f2b-help-set-subs-sfn)
   (:rewrite prop=f2b-help-mset) :top
   :prove :bash))

(property prop=f2b-new-joinee-st-fn (pubs subs :lot nbrs :lop s :s-fn)
  (== (f2b-st (new-joinee-st-fn pubs subs nbrs s)
              (fn-pending-mssgs s))
      (ps-bn pubs subs '()))
  :instructions
  (:pro
   (:claim (ps-fnp (new-joinee-st-fn pubs subs nbrs s)))
   (:claim (== (new-joinee-st-fn pubs subs nbrs s)
               (ps-fn pubs subs (calc-nsubs-fn nbrs s '()) '() '())))
   (:demote 5)
   (:equiv (new-joinee-st-fn pubs subs nbrs s)
           (ps-fn pubs subs (calc-nsubs-fn nbrs s '()) '() '()))
   :pro
   (:prove :hints (("Goal" :in-theory (enable f2b-st ps-bnp)
                    :use ((:instance prop=f2b-st-check
                                     (ps (new-joinee-st-fn
                                          pubs subs nbrs s))
                                     (ms (fn-pending-mssgs s)))))))))
  
(property prop=f2b-join-fn (p :peer pubs subs :lot nbrs :lop s :s-fn)
  :h (^ (! (mget p s))
        (! (in p nbrs)))
  (== (f2b (join-fn p pubs subs nbrs s))
      (join-bn p pubs subs (f2b s)))
  :instructions
  (:pro
   (= (f2b (join-fn p pubs subs nbrs s))
      (mset p
            (f2b-st (new-joinee-st-fn pubs subs nbrs s)
                    (fn-pending-mssgs s))
            (f2b s))
      :hints (("Goal" :use ((:instance prop=f2b-join-mset)))))
   (:claim (! (mget p (f2b s))))
   (:claim (ps-fnp (new-joinee-st-fn pubs subs nbrs s)))
   (= (f2b-st (new-joinee-st-fn pubs subs nbrs s)
              (fn-pending-mssgs s))
      (ps-bn pubs subs '())
      :hints (("Goal" :use ((:instance prop=f2b-new-joinee-st-fn)))))
   (:prove :hints (("Goal" :in-theory (enable join-bn))))))

;;---- LEAVE ------

(property prop=leave-cdr (s :s-fn p :peer)
  :check-contracts? nil
  :h (^ (mget p (cdr s))
        (!= p (car (car s))))
  (== (cdr (leave-fn p s))
      (leave-fn p (cdr s)))
  :hints (("Goal" :in-theory (enable leave-fn
                                     acl2::maximal-records-theory))))

(encapsulate ()
  (local
   (in-theory (enable acl2::maximal-records-theory
                      leave-fn
                      leave-bn)))
  (local
   (in-theory (disable prop=mget-f2b=mget)))

  (property prop=f2b-leave-fn-help (s :s-fn p :peer ms :lom)
    :h (mget p s)
    (== (f2b-help (leave-fn p s) ms)
        (leave-bn p (f2b-help s ms)))
  
    :instructions
    (:pro (:induct (f2b-help s ms))
        :pro
        (:casesplit (!= (car (car s)) p))
        (:claim (mget p (cdr s)))
        (:claim (== (f2b-help (leave-fn p (cdr s)) ms)
                    (leave-bn p (f2b-help (cdr s) ms))))


        (= (leave-bn p (f2b-help s ms))
           (cons (cons (caar s) (f2b-st (cdar s) ms))
                 (leave-bn p (f2b-help (cdr s) ms))))
        (= (leave-bn p (f2b-help (cdr s) ms))
           (f2b-help (leave-fn p (cdr s)) ms))
        (= (leave-fn p (cdr s))
           (cdr (leave-fn p s)))
        (= (car (car s))
           (car (car (leave-fn p s))))
        (= (cdr (car s))
           (cdr (car (leave-fn p s))))
        (:claim (consp (leave-fn p s)))
        (:dv 1) (:r 2) :s :top
        :s


        (= (leave-fn p s)
           (cdr s))
        (= (f2b-help s ms)
           (cons (cons (caar s) (f2b-st (cdar s) ms))
                 (f2b-help (cdr s) ms)))
        (= (leave-bn p
                 (cons (cons (car (car s))
                             (f2b-st (cdr (car s)) ms))
                       (f2b-help (cdr s) ms)))
           (f2b-help (cdr s) ms))
           

        :bash
        ))

(property prop=f2b-leave-fn (s :s-fn p :peer)
  :h (^ (mget p s)
        ;; Condition 1 : Full Propagation (no pending messages lost)
        (== (fn-pending-mssgs (leave-fn p s))
            (fn-pending-mssgs s)))
  (== (f2b (leave-fn p s))
      (leave-bn p (f2b s)))
  :instructions
  (:pro
   (:dv 1) :r
   (:equiv (fn-pending-mssgs (leave-fn p s))
           (fn-pending-mssgs s))
   :top
   (:dv 2 2) :r :top
   (:claim (== (f2b-help (leave-fn p s) (fn-pending-mssgs s))
               (leave-bn p (f2b-help s (fn-pending-mssgs s))))
               :hints (("Goal" :use ((:instance prop=f2b-leave-fn-help
                                                (ms (fn-pending-mssgs s)))))))
   :s))
)

(property prop=f2b-join-bn (w :s-fn p :peer pubs subs :lot nbrs :lop)
  :h (^ (! (mget p (f2b w)))
        (! (in p nbrs)))
  (== (f2b (join-fn p pubs subs nbrs w))
      (join-bn p pubs subs (f2b w)))
  :hints (("Goal" :use ((:instance prop=f2b-join-fn
                                   (s w))))))

(propertyd prop=f2b-leave-bn (w :s-fn p :peer)
  :check-contracts? nil
  :h  (^ (mget p (f2b w))
         ;; Condition 1 : Full Propagation
         (== (fn-pending-mssgs (leave-fn p w))
             (fn-pending-mssgs w)))
  (== (leave-bn p (f2b w))
      (f2b (leave-fn p w)))
  :instructions
  (:pro
   (:claim (mget p w))
   (:prove :hints (("Goal" :use ((:instance
                                  prop=f2b-leave-fn (s w))))))))


(property prop=f2b-forward-fn-help (p :peer s :s-fn nbrs :lop m :mssg ms :lom)
  (== (f2b-help (forward-help-fn s nbrs m) ms)
      (f2b-help s ms))
  :instructions
  (:pro
   (:induct (forward-help-fn s nbrs m)) :bash
   :pro
   (:claim (== (f2b-help (forward-help-fn (cdr s) nbrs m)
                         ms)
               (f2b-help (cdr s) ms)))
   
   (:casesplit (in (car (car s)) nbrs))
   

   (:dv 1 1) :r :s :up :r :s (:dv 1 2) :r :top
   :bash :bash
   (:claim (== (forward-help-fn s nbrs m)
               (cons (cons (car (car s))
                           (add-pending-psfn m (cdr (car s))))
                     (forward-help-fn (cdr s) nbrs m)))
           :hints (("Goal" :in-theory (enable forward-help-fn))))
   (= (cons (cons (car (car s))
                           (add-pending-psfn m (cdr (car s))))
            (forward-help-fn (cdr s) nbrs m))
      (forward-help-fn s nbrs m))
   :bash
   
   
   (:dv 1 1) :r :s :up :r :s :top :bash
   (:claim (== (forward-help-fn s nbrs m)
               (cons (car s)
                     (forward-help-fn (cdr s) nbrs m)))
           :hints (("Goal" :in-theory (enable forward-help-fn))))
   (= (cons (car s)
            (forward-help-fn (cdr s) nbrs m))
      (forward-help-fn s nbrs m))
   :bash
   :pro
   (:dv 1 1) :r :s :up :r :s :top :bash :r))



(property prop=f2b-update-forwarder-fn (p :peer m :mssg s :s-fn ms :lom)
  :h (in m ms)
  (== (f2b-help (update-forwarder-fn p m s) ms)
      (f2b-help s ms))
  :instructions
  (:pro
   (:induct (update-forwarder-fn p m s)) :bash :pro
   (:claim (equal (f2b-help (update-forwarder-fn p m (cdr s))
                             ms)
                  (f2b-help (cdr s) ms)))
   
   (:casesplit (== (car (car s)) p))

   (:dv 1 1) (:r 2) :s :up :r :s (:dv 1 2) :r :top
   :bash :bash :bash
   (:claim (== (update-forwarder-fn p m s)
               (cons (car s)
                     (update-forwarder-fn p m (cdr s))))
           :hints (("Goal" :in-theory (enable update-forwarder-fn))))
   (= (update-forwarder-fn p m s)
      (cons (car s)
            (update-forwarder-fn p m (cdr s))))
   :bash
   (:dv 1) :r :s :top :s
   (= (cons (car s)
            (update-forwarder-fn p m (cdr s)))
      (update-forwarder-fn p m s))
   :s :pro
   (= (update-forwarder-fn p m s)
      (cons (cons p (forwarder-new-pst (cdr (car s)) m))
            (cdr s)))
   (:dv 1) :r :s
   (= (f2b-st (forwarder-new-pst (cdr (car s)) m) ms)
      (f2b-st (cdr (car s)) ms))
   :top
   (=  (cons (cons p (f2b-st (cdr (car s)) ms))
             (f2b-help (cdr s) ms))
       (f2b-help s ms))
   (= (cons (cons p (forwarder-new-pst (cdr (car s)) m))
            (cdr s))
      (update-forwarder-fn p m s))
   :s :bash))


(property prop=in-pending-p=>new-bn-mssgp (s :s-fn p :peer m :mssg)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s))))
  (new-bn-mssgp m (f2b s))
  :instructions
  (:pro 
   (:claim (in m (fn-pending-mssgs s))
           :hints (("Goal" :use ((:instance prop=in-p-fn-pending)))))
   :bash)
  :rule-classes :forward-chaining)

(property prop=forward-fn (p :peer m :mssg s :s-fn)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (== (fn-pending-mssgs (forward-fn p m s))
            (fn-pending-mssgs s)))
  (== (f2b (forward-fn p m s))
      (f2b s))
  :hints (("Goal" :in-theory (enable forward-fn f2b))))


(in-theory (disable prop=mget-f2b=mget f2b f2b-definition-rule
                    f2b-help f2b-help-definition-rule
                    fn-pending-mssgs fn-pending-mssgs-definition-rule))


(in-theory (disable f2b f2b-definition-rule forward-fn forward-fn-definition-rule
                    fn-pending-mssgs fn-pending-mssgs-definition-rule))



(property prop=f2b-helper-def (ms :lom s :s-fn)
  :check-contracts? nil
  :h s
  (== (f2b-help s ms)
      (cons (cons (caar s)
                  (f2b-st (cdar s) ms))
            (f2b-help (cdr s) ms)))
  :hints (("Goal" :in-theory (enable f2b-help))))

(propertyd prop=f2b-helper-caar (ms :lom s :s-fn)
  :check-contracts? nil
  :h s
  (equal (car (car (f2b-help s ms)))
         (car (car s)))
  :hints (("Goal" :use ((:instance prop=f2b-helper-def)))))


(propertyd prop=f2b-helper-cdar (ms :lom s :s-fn)
  :check-contracts? nil
  :h s
  (== (cdr (car (f2b-help s ms)))
      (f2b-st (cdr (car s)) ms))
  :hints (("Goal" :use ((:instance prop=f2b-helper-def)))))
  



(definec brd-receivers (m :mssg s :s-fn) :lop
  (match s
    (() ())
    (((p . pst) . rst)
     (if (in m (mget :seen pst))
         (cons p (brd-receivers m rst))
       (brd-receivers m rst)))))

(encapsulate ()
  (local
   (in-theory (enable acl2::maximal-records-theory)))
  
  (local
   (property prop=xx (s :s-fn)
     :h (^ s (cdr s))
     (<< (car (car s))
         (car (car (cdr s))))))

  (local
   (property prop=<<-transitive (a b c :all)
     :h (^ (<< a b) (<< b c))
     (<< a c)))
  
  (local
   (property prop=p-!in-brd-receivers (p :peer m :mssg s :s-fn)
     :h (<< p (car (car s)))
     (! (in p (brd-receivers m s)))
     :instructions
     (:pro :induct :bash
           :pro
           (:casesplit (endp (cdr s))) :bash
           
           (:claim (<< (car (car s))
                       (car (cadr s)))
                   :hints (("Goal" :use ((:instance
                                          prop=xx)))))
           (:claim (<< p (car (cadr s)))
                   :hints (("Goal" :use ((:instance prop=<<-transitive
                                                    (a p)
                                                    (b (car (car s)))
                                                    (c (car (cadr s))))))))
           (:claim (s-fnp (cdr s)))
           (:claim (not (in p (brd-receivers m (cdr s)))))
           (:dv 1 2) (:r brd-receivers) :s :top :s

           :pro
           (:casesplit (endp (cdr s))) :bash
           
           (:claim (<< (car (car s))
                       (car (cadr s)))
                   :hints (("Goal" :use ((:instance
                                          prop=xx)))))
           (:claim (<< p (car (cadr s)))
                   :hints (("Goal" :use ((:instance prop=<<-transitive
                                                    (a p)
                                                    (b (car (car s)))
                                                    (c (car (cadr s))))))))
           (:claim (s-fnp (cdr s)))
           (:claim (not (in p (brd-receivers m (cdr s)))))
           (:dv 1 2) (:r brd-receivers) :s :up (:r in) :s
           :bash)))

  (property prop=caars-!in-brd-receivers-cdrs (m :mssg s :s-fn)
    :h s
    (! (in (car (car s)) (brd-receivers m (cdr s))))
    :hints (("Goal" :use ((:instance prop=p-!in-brd-receivers
                                     (p (car (car s)))
                                     (s (cdr s)))))))


  (local
   (property prop=m-in-brd-receivers-help (m :mssg s :s-fn)
     :h s
     (!= (car (car s))
         (car (brd-receivers m (cdr s))))
     :instructions
     (:pro
      (:claim (! (in (car (car s)) (brd-receivers m (cdr s))))
              :hints (("Goal" :use ((:instance
                                     prop=caars-!in-brd-receivers-cdrs)))))
      (:demote 4) (:dv 1 1) (:r in) :s :top :bash)))

  (property prop=m-in-brd-receivers (m :mssg s :s-fn)
    :h s
    (==
     (== (car (car s))
         (car (brd-receivers m s)))
     (in m (mget :seen (cdar s))))
    :hints (("Goal"
             :use ((:instance prop=m-in-brd-receivers-help)))))

  (local
   (property prop=car-in-tl (xs :tl)
     :h xs
     (in (car xs) xs)))
  
  (propertyd prop=mget-car-brd-receivers (m :mssg s :s-fn)
    :h (brd-receivers m s)
    (mget (car (brd-receivers m s)) s)
    :instructions
    (:pro
     (:claim s)
     :induct :bash
     :pro
     (:claim (! (<< (car (brd-receivers m s))
                    (car (car s)))))
     (:casesplit (== (car (car s))
                     (car (brd-receivers m s))))
     (:claim (in m (mget :seen (cdar s)))
             :hints (("Goal" :use ((:instance
                                    prop=m-in-brd-receivers)))))
     (= (car (brd-receivers m s))
        (car (car s))
        :hints (("Goal" :in-theory (enable brd-receivers))))
     :prove :prove :pro
     (:claim (<< (car (brd-receivers m s))
                 (car (car s))))
     (:claim (! (in (car (brd-receivers m s))
                    (brd-receivers m s)))
             :hints (("Goal" :use ((:instance prop=p-!in-brd-receivers
                                              (p (car (brd-receivers m
                                                                     s))))))))
     (:claim (in (car (brd-receivers m s))
                 (brd-receivers m s))
             :hints (("Goal" :use ((:instance prop=car-in-tl
                                              (xs (brd-receivers m s)))))))
     (:claim nil)
     :prove)))


(property prop=brd-receivers-cdr1 (m :mssg s :s-fn)
  :h (^ s
        (== (car (car s))
            (car (brd-receivers m s))))
  (== (cdr (brd-receivers m s))
      (brd-receivers m (cdr s)))
  :instructions
  (:pro
   (:dv 1 1) (:r brd-receivers) :s
   (:claim (in m (mget :seen (cdr (car s))))
           :hints (("Goal" :use ((:instance
                                  prop=m-in-brd-receivers)))))
   :top :s))

 
(property prop=brd-receivers-cdr2 (m :mssg s :s-fn)
  :h (^ s
        (!= (car (car s))
            (car (brd-receivers m s))))
  (== (brd-receivers m s)
      (brd-receivers m (cdr s)))
  :instructions
  (:pro
   (:dv 1) (:r brd-receivers) :s
   (:claim (! (in m (mget :seen (cdr (car s)))))
           :hints (("Goal" :use ((:instance
                                  prop=m-in-brd-receivers)))))
   :top :s))

(encapsulate ()
  (local
   (in-theory (enable forward-help-fn)))
  
  (property prop=brd-receivers-forward-help-fn
    (p :peer s :s-fn nbrs :lop m :mssg)
    (== (brd-receivers m (forward-help-fn s nbrs m))
        (brd-receivers m s))
    :instructions
    (:pro :induct :bash
          :pro
          (:casesplit (in (car (car s)) nbrs))
          (:claim (== (forward-help-fn s nbrs m)
                      (cons (cons (car (car s))
                                  (add-pending-psfn m (cdr (car s))))
                            (forward-help-fn (cdr s) nbrs m))))
          (:claim (s-fnp (forward-help-fn s nbrs m)))
          (:demote 12)
          (:equiv (forward-help-fn s nbrs m)
                      (cons (cons (car (car s))
                                  (add-pending-psfn m (cdr (car s))))
                            (forward-help-fn (cdr s) nbrs m)))
          :pro

          (:claim (== (mget :seen (add-pending-psfn m (cdr (car s))))
                      (mget :seen (cdr (car s))))
                  :hints (("Goal" :use ((:instance prop=add-pending-psfn-seen
                                                   (pst (cdr (car s))))))))
          (:claim (! (in m (mget :seen (add-pending-psfn m (cdr (car s)))))))
          (= (brd-receivers m
                      (cons (cons (car (car s))
                                  (add-pending-psfn m (cdr (car s))))
                            (forward-help-fn (cdr s) nbrs m)))
             (brd-receivers m (forward-help-fn (cdr s) nbrs m)))
          (= (equal (brd-receivers m (forward-help-fn (cdr s) nbrs m))
                    (brd-receivers m (cdr s))))
          :prove

          (:claim (== (forward-help-fn s nbrs m)
                      (cons (car s)
                            (forward-help-fn (cdr s) nbrs m))))
          (:claim (s-fnp (forward-help-fn s nbrs m)))
          (:demote 12)
          (:equiv (forward-help-fn s nbrs m)
                  (cons (car s)
                        (forward-help-fn (cdr s) nbrs m)))
          :pro
          (= (brd-receivers m
                      (cons (car s)
                            (forward-help-fn (cdr s) nbrs m)))
             (brd-receivers m (forward-help-fn (cdr s) nbrs m)))
          (= (brd-receivers m (forward-help-fn (cdr s) nbrs m))
             (brd-receivers m (cdr s)))
          :prove

          :pro
          (:casesplit (in (car (car s)) nbrs))
          (:claim (== (forward-help-fn s nbrs m)
                      (cons (cons (car (car s))
                                  (add-pending-psfn m (cdr (car s))))
                            (forward-help-fn (cdr s) nbrs m))))
          (:claim (s-fnp (forward-help-fn s nbrs m)))
          (:demote 12)
          (:equiv (forward-help-fn s nbrs m)
                  (cons (cons (car (car s))
                              (add-pending-psfn m (cdr (car s))))
                        (forward-help-fn (cdr s) nbrs m)))
          :pro
          (= (brd-receivers m
                            (cons (cons (car (car s))
                                        (add-pending-psfn m (cdr (car s))))
                                  (forward-help-fn (cdr s) nbrs m)))
             (cons (car (car s))
                   (brd-receivers m (forward-help-fn (cdr s) nbrs m))))
          :prove

          (:claim (== (forward-help-fn s nbrs m)
                      (cons (car s)
                            (forward-help-fn (cdr s) nbrs m))))
          (:claim (s-fnp (forward-help-fn s nbrs m)))
          (:demote 12)
          (:equiv (forward-help-fn s nbrs m)
                  (cons (car s)
                        (forward-help-fn (cdr s) nbrs m)))
          :pro
          (= (brd-receivers m
                      (cons (car s)
                            (forward-help-fn (cdr s) nbrs m)))
             (cons (car (car s))
                   (brd-receivers m (forward-help-fn (cdr s) nbrs m))))
          (= (cons (car (car s))
                   (brd-receivers m (forward-help-fn (cdr s) nbrs m)))
             (brd-receivers m s))
          :s :bash)))


(property prop=mget-cdr-mget (p :peer s :s-fn)
  :h (mget p (cdr s))
  (mget p s)
  :hints (("Goal" :in-theory
           (e/d (acl2::maximal-records-theory)
                (prop=mget-f2b=mget)))))

(encapsulate ()
  (property in-set-diff (xs ys :tl)
    :h (set-difference-equal xs ys)
    (in (car (set-difference-equal xs ys)) xs))

  (property in-<<-orderedp (x :all xs :tl)
    :h (^ (orderedp xs)
          (in x (cdr xs)))
    (<< (car xs) x))
  
  (property orderedp-set-difference (xs ys :tl)
    :h (orderedp xs)
    (orderedp (set-difference-equal xs ys))
    :instructions
    (:pro :induct :pro
          (:claim (orderedp (cdr xs)))
          (:claim (orderedp (set-difference-equal (cdr xs) ys)))
          (:casesplit (member-equal (car xs) ys))
          :prove
          (= (set-difference-equal xs ys)
             (cons (car xs)
                   (set-difference-equal (cdr xs) ys)))
          (:casesplit (consp (set-difference-equal (cdr xs) ys)))
          (:claim (in
                   (car (set-difference-equal (cdr xs) ys))
                   (cdr xs)))
                                
          (:claim (<< (car xs) (car (set-difference-equal
                                     (cdr xs)
                                     ys))))
          :prove
          :prove
          :bash
          :bash)))

(property prop=f2b-st-broadcast (m :mssg ms :lom pst :ps-fn)
  :h (^ (in m (mget :seen pst))
        (! (in m ms))
        (orderedp (mget :seen pst)))
  (== (f2b-st pst ms)
      (mset :seen (insert-unique m
                                 (mget :seen
                                       (f2b-st pst ms)))
            (f2b-st pst ms)))
  :instructions
  (:pro
   (:dv 1) (:r f2b-st) :s
   (= (set-difference-equal (mget :seen pst) ms)
      (insert-unique m
                     (set-difference-equal (mget :seen pst)
                                           ms))
      :hints (("Goal" :use ((:instance in-diff1
                                       (x (mget :seen pst))
                                       (y ms))))))
   :top
   (:prove :hints (("Goal" :in-theory (enable f2b-st))))))
   


(definec ordered-seenp (s :s-fn) :boolean
  (match s
    (() t)
    (((& . pst) . rst)
     (^ (orderedp (mget :seen pst))
        (ordered-seenp rst)))))

(property prop=ordered-seenp-cdar (s :s-fn)
  :h (^ s
        (ordered-seenp s))
  (orderedp (mget :seen (cdar s))))

(property prop=ordered-seen-f2b-st (ms :lom pst :ps-fn)
  :h (orderedp (mget :seen pst))
  (orderedp (mget :seen (f2b-st pst ms)))
  :hints (("Goal" :in-theory (enable f2b-st))))


(property prop=f2b-st-forwarder2 (m :mssg pst :ps-fn ms :lom)
  :h (! (in m ms))
  (equal (f2b-st (forwarder-new-pst pst m) ms)
         (f2b-st (mset :seen
                       (insert-unique m (mget :seen pst))
                       pst)
                 ms))
  :hints (("Goal" :in-theory (enable f2b-st forwarder-new-pst))))

(encapsulate ()
  (in-theory (enable update-forwarder-fn))
  
  (property prop=brd-receivers-update-forwarder1 (p :peer m :mssg s :s-fn)
    :h (== p (car (car s)))
    (== (brd-receivers m (update-forwarder-fn p m s))
        (cons (car (car s))
              (brd-receivers m (cdr s))))
    :instructions
    (:pro
     (:claim (== (update-forwarder-fn p m s)
                 (cons (cons (car (car s))
                             (forwarder-new-pst (cdr (car s)) m))
                       (cdr s))))
     (:claim (s-fnp (update-forwarder-fn p m s)))
     (:demote 6)
     (:equiv (update-forwarder-fn p m s)
                 (cons (cons (car (car s))
                             (forwarder-new-pst (cdr (car s)) m))
                       (cdr s)))
     (:claim (in m (mget :seen (forwarder-new-pst (cdr (car s)) m)))
             :hints (("Goal" :in-theory (enable forwarder-new-pst))))
     :prove))

  (property prop=brd-receivers-update-forwarder2 (p :peer m :mssg s :s-fn)
    :h (^ s
          (!= p (car (car s)))
          (in m (mget :seen (cdr (car s)))))
    (== (brd-receivers m (update-forwarder-fn p m s))
        (cons (car (car s))
              (brd-receivers m (update-forwarder-fn p m (cdr s)))))
    :instructions
    (:pro
     (:claim (== (update-forwarder-fn p m s)
                 (cons (car s)
                       (update-forwarder-fn p m (cdr s)))))
     (:claim (s-fnp (update-forwarder-fn p m s)))
     (:demote 8)
     (:equiv (update-forwarder-fn p m s)
                 (cons (car s)
                       (update-forwarder-fn p m (cdr s))))
     :pro
     :prove))

  (property prop=brd-receivers-update-forwarder3 (p :peer m :mssg s :s-fn)
    :h (^ s
          (!= p (car (car s)))
          (! (in m (mget :seen (cdr (car s))))))
    (== (brd-receivers m (update-forwarder-fn p m s))
        (brd-receivers m (update-forwarder-fn p m (cdr s))))
    :instructions
    (:pro
     (:claim (== (update-forwarder-fn p m s)
                 (cons (car s)
                       (update-forwarder-fn p m (cdr s)))))
     (:claim (s-fnp (update-forwarder-fn p m s)))
     (:demote 8)
     (:equiv (update-forwarder-fn p m s)
             (cons (car s)
                   (update-forwarder-fn p m (cdr s))))
     :pro
     :prove)))


(encapsulate ()
  (local
   (in-theory (enable update-forwarder-fn
                      forwarder-new-pst)))

  (property prop=caar-update-forwarder (p :peer m :mssg s :s-fn)
    :h s
    (== (car (car (update-forwarder-fn p m s)))
        (car (car s))))
                      
  (property prop=update-forwarder-seen1 (p :peer m :mssg s :s-fn)
    :h (^ s
          (!= p (car (car s))))
    (== (mget :seen (cdr (car (update-forwarder-fn p m s))))
        (mget :seen (cdr (car s)))))

  (property prop=update-forwarder-seen2 (p :peer m :mssg s :s-fn)
    :h (^ s
          (orderedp (mget :seen (cdr (car s))))
          (== p (car (car s))))
    (== (mget :seen (cdr (car (update-forwarder-fn p m s))))
        (insert-unique m (mget :seen (cdr (car s))))))

  (property prop=update-forwarder-seen4 (p :peer m :mssg s :s-fn)
    :h (^ s
          (! (in m (mget :seen
                         (cdr (car (update-forwarder-fn p m s)))))))
    (! (in m (mget :seen (cdr (car s)))))))

(property prop=brd-receivers-update-forwarder-pcaars1 (p :peer m :mssg s :s-fn)
  :h (^ s
        (!= p (car (car s)))
        (! (equal (car (car s))
                  (car (brd-receivers m (update-forwarder-fn p m s))))))
  (== (brd-receivers m (update-forwarder-fn p m s))
      (brd-receivers m (update-forwarder-fn p m (cdr s))))
  :instructions
  (:pro
   (:claim (== (car (car s))
               (car (car (update-forwarder-fn p m s))))
           :hints (("Goal" :use ((:instance
                                  prop=caar-update-forwarder)))))
   (:claim (!= (car (car (update-forwarder-fn p m s)))
               (car (brd-receivers m (update-forwarder-fn p m s)))))
   (:claim (! (in m (mget :seen (cdr (car (update-forwarder-fn p m s))))))
           :hints (("Goal" :use ((:instance prop=m-in-brd-receivers
                                            (s (update-forwarder-fn p m s)))))))            
   (:claim (! (in m (mget :seen (cdr (car s)))))
           :hints (("Goal" :use ((:instance prop=update-forwarder-seen4)))))
   (:prove :hints (("Goal" :use ((:instance
                                  prop=brd-receivers-update-forwarder3)))))
   ))


(property prop=brd-receivers-update-forwarder-pcaars2 (p :peer m :mssg s :s-fn)
  :h (^ s
        (!= p (car (car s)))
        (equal (car (car s))
               (car (brd-receivers m (update-forwarder-fn p m s)))))
  (== (brd-receivers m (update-forwarder-fn p m s))
      (cons (car (car s))
            (brd-receivers m (update-forwarder-fn p m (cdr s)))))
  :instructions
  (:pro
   (:claim (== (car (car s))
               (car (car (update-forwarder-fn p m s))))
           :hints (("Goal" :use ((:instance
                                  prop=caar-update-forwarder)))))
   (:claim (== (car (car (update-forwarder-fn p m s)))
               (car (brd-receivers m (update-forwarder-fn p m s)))))
   (:claim (in m (mget :seen (cdr (car (update-forwarder-fn p m s)))))
           :hints (("Goal" :use ((:instance prop=m-in-brd-receivers
                                            (s (update-forwarder-fn p m
                                                                    s)))))))
   (:claim (== (mget :seen (cdr (car (update-forwarder-fn p m s))))
               (mget :seen (cdr (car s))))
           :hints (("Goal" :use ((:instance prop=update-forwarder-seen1)))))
           
   (:claim (in m (mget :seen (cdr (car s)))))
   (:prove :hints (("Goal" :use ((:instance
                                  prop=brd-receivers-update-forwarder2)))))))


(propertyd prop=car-brd-receivers-update-forwarder (p :peer m :mssg s :s-fn)
  :h (mget p s)
  (brd-receivers m (update-forwarder-fn p m s))
  :instructions
  (:pro :induct :bash
        (:claim (!= (car (car s)) p))
        (:casesplit (in m (mget :seen (cdr (car s)))))
        (:prove :hints (("Goal" :use ((:instance
                                       prop=brd-receivers-update-forwarder2)))))
        :pro
        (:claim (mget p (cdr s))
                :hints (("Goal" :in-theory (enable
                                            acl2::maximal-records-theory))))
        (:claim (brd-receivers m (update-forwarder-fn p m (cdr s))))
        (:prove :hints (("Goal" :use ((:instance
                                       prop=brd-receivers-update-forwarder3)))))
        :pro
        (:prove :hints (("Goal" :use ((:instance
                                       prop=brd-receivers-update-forwarder1)))))
        :pro
        (:prove :hints (("Goal" :in-theory (enable update-forwarder-fn
                                                   brd-receivers))))))


(property prop=set-diff-insert-!in (m :all xs ys :tl)
  :h (^ (orderedp xs)
        (! (in m ys)))
  (== (set-difference-equal (insert-unique m xs) ys)
      (insert-unique m (set-difference-equal xs ys))))

(encapsulate ()
  (local 
   (property prop=in->member (x :tl m :all)
     (=> (in m x)
         (member-equal m x))))
  (property member-equal-insert-unique (m :all x :tl)
    (member-equal m (insert-unique m x))))
  
  ;; see utils insert-unique-diff
(property insert-unique-diff2 (x y :tl m :all)
  :h (^ (orderedp x)
        (in m x))
  (== (set-difference-equal x (insert-unique m y))
      (remove-equal m (set-difference-equal x y))))

(property insert-unique-remove-same (x :tl m :all)
  :check-contracts? nil
  :h (orderedp x)
  (= (insert-unique m (remove-equal m x))
     (insert-unique m x)))
  
(property insert-diff-insert (x y :tl m :all)
  :h (orderedp x)
  (== (insert-unique m (set-difference-equal x (insert-unique m y)))
      (insert-unique m (set-difference-equal x y)))
  :instructions
  (:pro
   (:casesplit (! (member-equal m x)))
   (= (set-difference-equal x (insert-unique m y))
      (set-difference-equal x y)
      :hints (("Goal" :use ((:instance insert-unique-diff)))))

   (:claim (in m x))
   (= (set-difference-equal x (insert-unique m y))
      (remove-equal m (set-difference-equal x y))
      :hints (("Goal" :use ((:instance insert-unique-diff2)))))
   (:claim (orderedp (set-difference-equal x y)))
   (= (insert-unique m (remove-equal m (set-difference-equal x y)))
      (insert-unique m (set-difference-equal x y))
      :hints (("Goal" :use ((:instance insert-unique-remove-same
                                       (x (set-difference-equal x y)))))))

   ))


(property prop=f2b-st-broadcast2 (m :mssg ms :lom pst :ps-fn)
  :h (^ (! (in m ms))
        (orderedp (mget :seen pst)))
  (== (f2b-st (mset :seen
                    (insert-unique m (mget :seen pst))
                    pst)
              ms)
      (mset :seen
            (insert-unique m
                           (set-difference-equal (mget :seen pst)
                                                 ms))
            (f2b-st pst ms)))
  :instructions
  (:pro
   (:dv 1) (:r f2b-st) :s
   (:claim (ps-fnp (mset :seen
                         (insert-unique m (mget :seen pst))
                         pst)))
   (= (insert-unique m
                     (set-difference-equal (mget :seen pst)
                                           ms))
      (set-difference-equal (insert-unique m (mget :seen pst))
                                           ms)
      :hints (("Goal" :use ((:instance prop=set-diff-insert-!in
                                       (xs (mget :seen pst))
                                       (ys ms))))))
   :top
   (:prove :hints (("Goal" :in-theory (enable f2b-st))))))
  
  
(property prop=update-forwarder-<<p (p :peer m :mssg s :s-fn)
  :h (<< p (car (car s)))
  (== (update-forwarder-fn p m s) s)
      :hints (("Goal" :in-theory
               (enable acl2::maximal-records-theory))))

(property prop=s-fn-keys-order (s :s-fn)
  :h s
  (<< (car (car s))
      (car (car (cdr s))))
  :hints (("Goal" :in-theory
           (enable acl2::maximal-records-theory))))

(property prop=f2b-update-forwarder-fn2
  (p :peer m :mssg ms :lom s :s-fn)
  :h (^ (ordered-seenp s)
        (! (in m ms)))
  (== (f2b-help (update-forwarder-fn p m s) ms)
      (broadcast-partial-help m
                              (brd-receivers m (update-forwarder-fn p m s))
                              (f2b-help s ms)))
  :instructions
  (:pro
   :induct :pro
   (:claim s)
   (:casesplit (!= (car (car s)) p))
   (:claim (ordered-seenp (cdr s)))
   (:claim (s-fnp (cdr s)))
   (:claim (equal (f2b-help (update-forwarder-fn p m (cdr s)) ms)
                  (broadcast-partial-help
                   m (brd-receivers m (update-forwarder-fn p m (cdr s)))
                   (f2b-help (cdr s) ms))))

   (:claim (== (update-forwarder-fn p m s)
               (cons (car s)
                     (update-forwarder-fn p m (cdr s)))))
   (:claim (s-fnp (update-forwarder-fn p m s)))
   (:demote 16)
   (:equiv (update-forwarder-fn p m s)
           (cons (car s)
                 (update-forwarder-fn p m (cdr s))))
   :pro
   (:dv 1) (:r prop=f2b-helper-def)
   (= (car (car (cons (car s)
                      (update-forwarder-fn p m (cdr s)))))
      (car (car s)))
   (= (cdr (car (cons (car s)
                      (update-forwarder-fn p m (cdr s)))))
      (cdar s))
   (= (cdr (cons (car s)
                 (update-forwarder-fn p m (cdr s))))
      (update-forwarder-fn p m (cdr s)))
   (= (f2b-help (update-forwarder-fn p m (cdr s))
                ms)
      (broadcast-partial-help
                m
                (brd-receivers m (update-forwarder-fn p m (cdr s)))
                (f2b-help (cdr s) ms)))
 
   :top


   (:claim (== (f2b-help s ms)
               (cons (cons (caar s)
                           (f2b-st (cdar s) ms))
                     (f2b-help (cdr s) ms)))
           :hints (("Goal" :use ((:instance prop=f2b-helper-def)))))
   (:claim (s-bnp (f2b-help s ms)))
   (:demote 18)
   (:equiv (f2b-help s ms)
           (cons (cons (caar s)
                  (f2b-st (cdar s) ms))
                 (f2b-help (cdr s) ms)))
   :pro :s
   
   (:dv 2)
   (:r broadcast-partial-help) :s :top

   (:equiv (f2b-help s ms)
           (cons (cons (caar s)
                       (f2b-st (cdar s) ms))
                 (f2b-help (cdr s) ms)))
   (= (car (car (cons (cons (car (car s))
                               (f2b-st (cdr (car s)) ms))
                      (f2b-help (cdr s) ms))))
      (car (car s)))
   (= (cdr (car (cons (cons (car (car s))
                            (f2b-st (cdr (car s)) ms))
                      (f2b-help (cdr s) ms))))
      (f2b-st (cdr (car s)) ms))

   
   (:casesplit (== (car (car s))
                   (car (brd-receivers m (update-forwarder-fn p m s)))))
   
   (:claim (== (car (car s))
               (car (car (update-forwarder-fn p m s))))
           :hints (("Goal" :use ((:instance prop=caar-update-forwarder)))))

   (:claim (== (car (car (update-forwarder-fn p m s)))
               (car (brd-receivers m (update-forwarder-fn p m s)))))
   :s

   (:claim (orderedp (mget :seen (cdr (car s))))
           :hints (("Goal" :use ((:instance prop=ordered-seenp-cdar)))))
   (:claim (ps-fnp (cdr (car s))))
   (:claim (orderedp (mget :seen (f2b-st (cdr (car s)) ms)))
           :hints (("Goal" :use ((:instance prop=ordered-seen-f2b-st
                                            (pst (cdr (car s))))))))
   (:claim (in m (mget :seen (cdr (car (update-forwarder-fn p m s)))))
           :hints (("Goal" :use ((:instance prop=m-in-brd-receivers
                                            (s (update-forwarder-fn p m
                                                                    s)))))))
   (:demote 25)
   (= (mget :seen (cdr (car (update-forwarder-fn p m s))))
      (mget :seen (cdr (car s)))
      :hints (("Goal" :use ((:instance prop=update-forwarder-seen1)))))
   :pro
   
   (:dv 1)
   (:claim (orderedp (mget :seen (cdar s)))
           :hints (("Goal" :use ((:instance prop=ordered-seenp-cdar)))))
   
   (= (f2b-st (cdr (car s)) ms)
      (mset :seen
                  (insert-unique m
                                 (mget :seen (f2b-st (cdr (car s)) ms)))
                  (f2b-st (cdr (car s)) ms))
      :hints (("Goal" :use ((:instance prop=f2b-st-broadcast
                                       (pst (cdr (car s))))))))
   :top :s
   :s
   (= (f2b-help s ms)
      (cons (cons (car (car s))
                       (f2b-st (cdr (car s)) ms))
            (f2b-help (cdr s) ms)))
   (= (car (cons (cons (car (car s))
                             (f2b-st (cdr (car s)) ms))
                 (f2b-help (cdr s) ms)))
      (cons (car (car s))
            (f2b-st (cdr (car s)) ms)))

   
   :pro
   (:dv 1 1) (:r update-forwarder-fn) 
   (:claim (ps-fnp (cdr (car s))))
   :s :up (:r prop=f2b-helper-def) :s :top
   (:claim (ps-fnp (mset :seen
                         (insert-unique m (mget :seen (cdr (car s))))
                         (cdr (car s)))))
   
   (:claim (equal (f2b-help (update-forwarder-fn p m (cdr s))
                              ms)
                    (broadcast-partial-help
                         m
                         (brd-receivers m (update-forwarder-fn p m (cdr s)))
                         (f2b-help (cdr s) ms))))

  
   (= (brd-receivers m (update-forwarder-fn p m s))
      (cons (car (car s))
            (brd-receivers m (cdr s)))
      :hints (("Goal" :use ((:instance
                             prop=brd-receivers-update-forwarder1)))))

   (:dv 2) (:r broadcast-partial-help) :s :up :s

   (= (f2b-st (mset :seen
                    (insert-unique m (mget :seen (cdr (car s))))
                    (cdr (car s)))
              ms)
      (mset :seen
            (insert-unique m
                           (set-difference-equal (mget :seen (cdr (car s)))
                                                 ms))
            (f2b-st (cdr (car s)) ms))
      :hints (("Goal" :use ((:instance prop=f2b-st-broadcast2
                                       (pst (cdr (car s))))))))
   :s
   (:claim (<< (car (car s))
               (car (car (cdr s))))
           :hints (("Goal" :use ((:instance prop=s-fn-keys-order)))))
   
   (= (cdr s)
      (update-forwarder-fn p m (cdr s))
      :hints (("Goal" :use ((:instance prop=update-forwarder-<<p
                                       (p (car (car s)))
                                       (s (cdr s)))))))

   (:dv 2 3 1)
   (= (update-forwarder-fn p m (cdr s)) (cdr s)
      :hints (("Goal" :use ((:instance prop=update-forwarder-<<p
                                       (p (car (car s)))
                                       (s (cdr s)))))))
   
   :top :s :s :bash
   :pro
   (:prove :hints (("Goal" :in-theory (enable f2b-help
                                              broadcast-partial-help))))))
   
(in-theory (enable f2b-help))

(propertyd prop=f2b-help-cons (s :s-fn m :mssg ms :lom)
  :h s
  (^ (f2b-help s (insert-unique m ms))
     (equal (car (car s))
            (car (car (f2b-help s (insert-unique m ms)))))))

(in-theory (disable prop=f2b-helper-def))

(propertyd prop=in->member (x :tl m :all)
  (=> (in m x)
      (member-equal m x)))

(property prop=mset-seen-f2b-st (pst :ps-fn m :mssg ms :lom)
  (== (mset :seen
            (insert-unique m (mget :seen (f2b-st pst ms)))
            (f2b-st pst ms))
      (mset
       :0tag 'ps-bn
       (mset :pubs (mget :pubs pst)
             (mset :seen
                   (insert-unique m (set-difference-equal (mget :seen pst) ms))
                   (mset :subs (mget :subs pst)
                         nil)))))
  :hints (("Goal" :in-theory (enable f2b-st))))
  

(propertyd prop=!in->!member (x :tl m :all)
     (=> (! (in m x))
         (! (member-equal m x))))

(propertyd ordered-seenp-cdr (s :s-fn)
  :h (^ s (ordered-seenp s))
  (ordered-seenp (cdr s)))

(propertyd prop=cons-update-forwarder-fn (p :peer m :mssg s :s-fn)
  :h s
  (update-forwarder-fn p m s)
           :hints (("Goal" :in-theory (enable update-forwarder-fn))))

(property prop=broadcast-partial-help-f2b-insertm
  (p :peer m :mssg ms :lom s :s-fn)
  :h (^ (! (in m ms))
        (ordered-seenp s))
  (== (broadcast-partial-help m
                              (brd-receivers m (update-forwarder-fn p m s))
                              (f2b-help s (insert-unique m ms)))
      (broadcast-partial-help m
                              (brd-receivers m (update-forwarder-fn p m s))
                              (f2b-help s ms)))
  :instructions
  (:pro
   :induct :pro
   (:claim (lomp (insert-unique m ms)))
   (:claim (^ (f2b-help s (insert-unique m ms))
              (equal (car (car s))
                     (car (car (f2b-help s (insert-unique m ms))))))
           :hints (("Goal" :use ((:instance prop=f2b-help-cons)))))
   (:dv 1) (:r broadcast-partial-help)
   
   (:casesplit (== (car (car (f2b-help s (insert-unique m ms))))
                   (car (brd-receivers m (update-forwarder-fn p m s)))))

   :s
   (= (f2b-help s (insert-unique m ms))
      (cons (cons (caar s)
                  (f2b-st (cdar s) (insert-unique m ms)))
            (f2b-help (cdr s) (insert-unique m ms)))
      :hints (("Goal" :use ((:instance prop=f2b-helper-def
                                       (ms (insert-unique m ms)))))))
   :s
   (:claim (ordered-seenp (cdr s))
           :hints (("Goal" :use ((:instance ordered-seenp-cdr)))))
   (:claim (equal (broadcast-partial-help
                   m
                   (brd-receivers m (update-forwarder-fn p m (cdr s)))
                   (f2b-help (cdr s) (insert-unique m ms)))
                  (broadcast-partial-help
                   m
                   (brd-receivers m (update-forwarder-fn p m (cdr s)))
                   (f2b-help (cdr s) ms))))
   (:claim (== (car (car s))
               (car (car (update-forwarder-fn p m s))))
           :hints (("Goal" :use ((:instance prop=caar-update-forwarder)))))
   
   (:claim (== (car (car (update-forwarder-fn p m s)))
               (car (brd-receivers m (update-forwarder-fn p m s)))))

   (:claim (update-forwarder-fn p m s)
           :hints (("Goal" :use ((:instance prop=cons-update-forwarder-fn)))))
                                  
   (= (cdr (brd-receivers m (update-forwarder-fn p m s)))
      (brd-receivers m (cdr (update-forwarder-fn p m s)))
      :hints (("Goal" :use ((:instance prop=brd-receivers-cdr1
                                       (s (update-forwarder-fn p m s)))))))
   (= (cdr (update-forwarder-fn p m s))
      (update-forwarder-fn p m (cdr s))
      :hints (("Goal" :use ((:instance prop=update-forwarder-fn-cdr)))))
   
   (:equiv (broadcast-partial-help m
                                   (brd-receivers m (update-forwarder-fn p m (cdr s)))
                                   (f2b-help (cdr s)
                                             (insert-unique m ms)))
           (broadcast-partial-help m
            (brd-receivers m (update-forwarder-fn p m (cdr s)))
            (f2b-help (cdr s) ms)))
   (:claim (ps-fnp (cdr (car s))))
   (:claim (lomp (insert-unique m ms)))
   (= (mget :seen (f2b-st (cdr (car s))
                          (insert-unique m ms)))
      (set-difference-equal (mget :seen (cdr (car s)))
                            (insert-unique m ms))
      :hints (("Goal" :use ((:instance prop=f2b-st-check
                                       (ps (cdr (car s)))
                                       (ms (insert-unique m ms)))))))
   (:claim (orderedp (mget :seen (cdr (car s))))
           :hints (("Goal" :use ((:instance prop=ordered-seenp-cdar)))))
   (= (insert-unique m (set-difference-equal (mget :seen (cdr (car s)))
                                             (insert-unique m ms)))
      (insert-unique m (set-difference-equal
                        (mget :seen (cdr (car s)))
                        ms))
      :hints (("Goal" :use ((:instance insert-diff-insert
                                       (x (mget :seen (cdr (car s))))
                                       (y ms))))))
   (:claim (==  (car (car s))
                (car (brd-receivers m (update-forwarder-fn p m s)))))

   (= (set-difference-equal (mget :seen (cdr (car s))) ms)
      (mget :seen (f2b-st (cdr (car s)) ms))
      :hints (("Goal" :use ((:instance prop=f2b-st-check
                                       (ps (cdr (car s))))))))

   (:dv 1 2 3) (:r f2b-st) :s :up :s
   (:claim (== (mset :seen
                     (insert-unique m (mget :seen (f2b-st (cdr (car s)) ms)))
                     (f2b-st (cdr (car s)) ms))
               (mset
                :0tag 'ps-bn
                (mset :pubs (mget :pubs (cdr (car s)))
                      (mset :seen
                            (insert-unique m
                                           (set-difference-equal
                                            (mget :seen (cdr (car s)))
                                            ms))
                            (mset :subs (mget :subs (cdr (car s)))
                                  nil)))))
           :hints (("Goal" :use ((:instance prop=mset-seen-f2b-st
                                            (pst (cdr (car s))))))))
   :s :up :up

   (= (f2b-st (cdr (car s)) ms)
      (cdr (car (f2b-help s ms)))
      :hints (("Goal" :use ((:instance prop=f2b-helper-cdar)))))

   :up (:dv 2) (:r broadcast-partial-help)
   (:claim (== (f2b-help s ms)
               (cons (cons (caar s)
                  (f2b-st (cdar s) ms))
                     (f2b-help (cdr s) ms)))
           :hints (("Goal" :use ((:instance prop=f2b-helper-def)))))
   (:claim (f2b-help s ms))
   (:claim (consp (car (f2b-help s ms))))
   (:claim (equal (car (car (f2b-help s ms)))
                  (car (car s)))
           :hints (("Goal" :use ((:instance prop=f2b-helper-caar)))))
   :s :up :s
   (= (ps-fn-seen (cdr (car s)))
      (mget :seen (cdr (car s))))
   :s 
   (:claim (ordered-seenp (cdr s))
           :hints (("Goal" :use ((:instance ordered-seenp-cdr)))))
   (:claim (equal (broadcast-partial-help
                         m
                         (brd-receivers m (update-forwarder-fn p m (cdr s)))
                         (f2b-help (cdr s) (insert-unique m ms)))
                    (broadcast-partial-help
                         m
                         (brd-receivers m (update-forwarder-fn p m (cdr s)))
                         (f2b-help (cdr s) ms))))
   (:claim (!= (car (car s))
               (car (brd-receivers m (update-forwarder-fn p m s)))))
   (:claim (update-forwarder-fn p m s)
           :hints (("Goal" :use ((:instance prop=cons-update-forwarder-fn)))))
   (:claim (== (car (car s))
               (car (car (update-forwarder-fn p m s))))
           :hints (("Goal" :use ((:instance prop=caar-update-forwarder)))))
   (:claim (!= (car (car (update-forwarder-fn p m s)))
               (car (brd-receivers m (update-forwarder-fn p m s)))))
   (= (brd-receivers m (update-forwarder-fn p m s))
      (brd-receivers m (cdr (update-forwarder-fn p m s)))
      :hints (("Goal" :use ((:instance prop=brd-receivers-cdr2
                                       (s (update-forwarder-fn p m s)))))))
   (= (cdr (update-forwarder-fn p m s))
      (update-forwarder-fn p m (cdr s))
      :hints (("Goal" :use ((:instance prop=update-forwarder-fn-cdr)))))

   (:equiv (broadcast-partial-help
                         m
                         (brd-receivers m (update-forwarder-fn p m (cdr s)))
                         (f2b-help (cdr s) (insert-unique m ms)))
           (broadcast-partial-help
            m
            (brd-receivers m (update-forwarder-fn p m (cdr s)))
            (f2b-help (cdr s) ms)))

   :up (:dv 2) (:r broadcast-partial-help) :s
   
   (= (car (car (f2b-help s ms)))
      (car (car s))
      :hints (("Goal" :use ((:instance prop=f2b-helper-caar)))))

   (:claim (== (f2b-help s ms)
               (cons (cons (caar s)
                           (f2b-st (cdar s) ms))
                     (f2b-help (cdr s) ms)))
           :hints (("Goal" :use ((:instance prop=f2b-helper-def)))))
   (:claim (f2b-help s ms))
   (:claim (consp (car (f2b-help s ms))))
   
   (:claim (== (brd-receivers m (update-forwarder-fn p m s))
               (brd-receivers m (cdr (update-forwarder-fn p m s))))
           :hints (("Goal" :use ((:instance prop=brd-receivers-cdr2
                                            (s (update-forwarder-fn p m
                                                                    s)))))))
   (= (update-forwarder-fn p m (cdr s))
      (cdr (update-forwarder-fn p m s))
      :hints (("Goal" :use ((:instance prop=update-forwarder-fn-cdr)))))
   (:equiv (brd-receivers m (cdr (update-forwarder-fn p m s)))
           (brd-receivers m (update-forwarder-fn p m s)))
   :s :up :s
   (:equiv (f2b-help s ms)
           (cons (cons (car (car s))
                       (f2b-st (cdr (car s)) ms))
                 (f2b-help (cdr s) ms)))
   (= (car (cons (cons (car (car s))
                        (f2b-st (cdr (car s)) ms))
                 (f2b-help (cdr s) ms)))
      (cons (car (car s))
            (f2b-st (cdr (car s)) ms)))
   (= (cdr (car (f2b-help s (insert-unique m ms))))
      (f2b-st (cdr (car s)) (insert-unique m ms))
      :hints (("Goal" :use ((:instance prop=f2b-helper-cdar
                                       (ms (insert-unique m ms)))))))
   :s
   (:claim (ps-fnp (cdr (car s))))
   (:dv 2) (:r f2b-st) :s :up
   (:dv 1) (:r f2b-st) :s
   (:claim (! (in m (mget :seen (cdar (update-forwarder-fn p m s)))))
           :hints (("Goal" :use ((:instance prop=m-in-brd-receivers
                                            (s (update-forwarder-fn p m
                                                                    s)))))))
   (:claim (! (in m (mget :seen (cdr (car s)))))
           :hints (("Goal" :use ((:instance prop=update-forwarder-seen4)))))
   (:claim (! (member-equal m (mget :seen (cdr (car s)))))
           :hints (("Goal" :use ((:instance prop=!in->!member
                                            (x (mget :seen (cdr (car s)))))))))
   (= (set-difference-equal (mget :seen (cdr (car s)))
                            (insert-unique m ms))
      (set-difference-equal (mget :seen (cdr (car s))) ms)
      :hints (("Goal" :use ((:instance insert-unique-diff
                                       (x (mget :seen (cdr (car s))))
                                       (y ms))))))
   :up :s :pro
   (:prove :hints (("Goal" :in-theory (enable update-forwarder-fn
                                              broadcast-partial-help))))))

(in-theory (enable f2b fn-pending-mssgs))

(propertyd prop=forward-fn2-broadcast (p :peer m :mssg s :s-fn)
  :h (^ (mget p s)
        (in m (mget :pending (mget p s)))
        (ordered-seenp s)
        (!= (fn-pending-mssgs (forward-fn p m s))
            (fn-pending-mssgs s)))
  (== (f2b (forward-fn p m s))
      (broadcast-partial-help m
                              (brd-receivers m (forward-fn p m s))
                              (f2b s)))
  :instructions
  (:pro
   (= (f2b (forward-fn p m s))
      (f2b-help (forward-fn p m s)
                (fn-pending-mssgs (forward-fn p m s)))
      :hints (("Goal" :in-theory (enable f2b))))
   (:dv 1 1) (:r forward-fn) :s :up (:r prop=f2b-forward-fn-help)
   (:r prop=f2b-update-forwarder-fn2) :top
   (:dv 2 2 2) (:r forward-fn) :s :up (:r prop=brd-receivers-forward-help-fn)
   :top
   (:claim (v (== (fn-pending-mssgs (forward-fn p m s))
                  (remove-equal m (fn-pending-mssgs s)))
              (== (fn-pending-mssgs (forward-fn p m s))
                  (fn-pending-mssgs s)))
           :hints (("Goal" :use ((:instance
                                  prop=fn-pending-mssgs-forward-fn)))))
   (:claim (== (fn-pending-mssgs (forward-fn p m s))
               (remove-equal m (fn-pending-mssgs s))))
   (= (f2b s)
      (f2b-help s (fn-pending-mssgs s))
      :hints (("Goal" :in-theory (enable f2b))))

   (:claim (== (fn-pending-mssgs s)
               (union-set (mget :pending (cdr (car s)))
                          (fn-pending-mssgs (cdr s)))))
   (:claim (orderedp (union-set (mget :pending (cdr (car s)))
                                (fn-pending-mssgs (cdr s)))))
   (:claim (orderedp (fn-pending-mssgs s)))

   (:equiv (fn-pending-mssgs (forward-fn p m s))
           (remove-equal m (fn-pending-mssgs s)))

   (:claim (in m (fn-pending-mssgs s))
           :hints (("Goal" :use ((:instance
                                  prop=in-p-fn-pending)))))

   (:dv 2 3 2)
   (= (fn-pending-mssgs s)
      (insert-unique m (remove-equal m (fn-pending-mssgs s)))
      :hints (("Goal" :use ((:instance insert-unique-remove-ordered3
                                       (r m)
                                       (x (fn-pending-mssgs s)))))))
   :top

   (:claim (! (in m (remove-equal m (fn-pending-mssgs s)))))
   (:dv 2)
   (:r prop=broadcast-partial-help-f2b-insertm) :up :s :s :s :s
   (:claim (v (== (fn-pending-mssgs (forward-fn p m s))
                  (remove-equal m (fn-pending-mssgs s)))
              (== (fn-pending-mssgs (forward-fn p m s))
                  (fn-pending-mssgs s)))
           :hints (("Goal" :use ((:instance
                                  prop=fn-pending-mssgs-forward-fn)))))
   (:claim (== (fn-pending-mssgs (forward-fn p m s))
               (remove-equal m (fn-pending-mssgs s))))
   :prove :s :s))


(encapsulate ()
  (local
   (in-theory (enable update-forwarder-fn)))

  (local
   (property prop=update-forwarder-fn-neq (p :peer m :mssg s :s-fn)
     :h (^ s (!= p (car (car s))))
     (== (update-forwarder-fn p m s)
         (cons (car s) (update-forwarder-fn p m (cdr s))))
     :hints (("Goal" :in-theory (enable update-forwarder-fn)))))

  (local
   (property prop=mget-update-forwarder-fn (p x :peer m :mssg s :s-fn)
     :h (mget x (update-forwarder-fn p m s))
     (mget x s)
     :instructions
     (:pro :induct :bash
           :pro
           (:claim (! (equal (car (car s)) p)))
           (:claim (== (update-forwarder-fn p m s)
                       (cons (car s)
                             (update-forwarder-fn p m (cdr s))))
                   :hints (("Goal" :use ((:instance
                                          prop=update-forwarder-fn-neq)))))
           (:casesplit (== x (car (car s))))
           (:r mget) :s :bash
           

           (:demote 10)
           (:claim (== (update-forwarder-fn p m s)
                       (cons (car s)
                             (update-forwarder-fn p m (cdr s))))
                   :hints (("Goal" :use ((:instance
                                          prop=update-forwarder-fn-neq)))))
           (:equiv (update-forwarder-fn p m s)
                   (cons (car s)
                         (update-forwarder-fn p m (cdr s))))
           (:dv 1) (:r mget) :s :top :pro
           (:claim (mget x (cdr s)))
           (:r mget) :s

           :pro
           (:casesplit (== x (car (car s)))) :prove
           (:claim (== (car (car (update-forwarder-fn p m s)))
                       (car (car s))))
           (:demote 8)
           (:dv 1) (:r mget) :s :top :s
           :prove)))
  
  
  (propertyd prop=mget-car-brd-receivers-forward-fn (p :peer m :mssg s :s-fn)
    :h (^ (mget p s)
          (in m (mget :pending (mget p s))))
    (mget (car (brd-receivers m (forward-fn p m s))) s)
    :instructions
    (:pro
     (= (forward-fn p m s)
        (forward-help-fn (update-forwarder-fn p m s)
                         (mget (mget :tp m)
                               (mget :nsubs (mget p s)))
                         m)
        :hints (("Goal" :in-theory (enable forward-fn))))
     (:claim (lopp (mget (mget :tp m)
                         (mget :nsubs (mget p s)))))
     (:claim (s-fnp (update-forwarder-fn p m s)))
     (= (brd-receivers m (forward-help-fn (update-forwarder-fn p m s)
                                          (mget (mget :tp m)
                                                (mget :nsubs (mget p s)))
                                          m))
        (brd-receivers m (update-forwarder-fn p m s))
        :hints (("Goal" :use ((:instance prop=brd-receivers-forward-help-fn
                                         (s (update-forwarder-fn p m s))
                                         (nbrs (mget (mget :tp m)
                                                     (mget :nsubs
                                                           (mget p s)))))))))
     (:claim (brd-receivers m (update-forwarder-fn p m s))
             :hints (("Goal" :use ((:instance
                                    prop=car-brd-receivers-update-forwarder)))))
     (:claim (mget (car (brd-receivers m (update-forwarder-fn p m s)))
                   (update-forwarder-fn p m s))
             :hints (("Goal" :use ((:instance prop=mget-car-brd-receivers
                                              (s (update-forwarder-fn p m
                                                                      s)))))))
     (:prove :hints (("Goal" :use ((:instance
                                    prop=mget-update-forwarder-fn
                                    (x (car (brd-receivers m (update-forwarder-fn p m s))))))))))))

(in-theory (disable f2b f2b-definition-rule forward-fn forward-fn-definition-rule
                    f2b-help f2b-help-definition-rule
                    fn-pending-mssgs fn-pending-mssgs-definition-rule
                    prop=f2b-help-cons prop=f2b-helper-def
                    prop=broadcast-partial-help-f2b-insertm
                    prop=mset-seen-f2b-st prop=f2b-update-forwarder-fn2
                    prop=s-fn-keys-order prop=update-forwarder-<<p
                    prop=f2b-st-broadcast2 insert-diff-insert
                    insert-unique-remove-same insert-unique-diff2
                    prop=set-diff-insert-!in
                    prop=brd-receivers-update-forwarder-pcaars2
                    prop=brd-receivers-update-forwarder-pcaars1
                    prop=update-forwarder-seen4
                    prop=update-forwarder-seen2
                    prop=update-forwarder-seen1
                    prop=f2b-st-forwarder2
                    prop=brd-receivers-update-forwarder3 prop=ordered-seen-f2b-st
                    prop=brd-receivers-update-forwarder2 prop=ordered-seenp-cdar
                    prop=brd-receivers-update-forwarder1 prop=f2b-st-broadcast
                    orderedp-set-difference in-<<-orderedp in-set-diff
                    prop=mget-cdr-mget prop=brd-receivers-cdr2 prop=brd-receivers-cdr1
                    prop=brd-receivers-forward-help-fn prop=m-in-brd-receivers
                    prop=caars-!in-brd-receivers-cdrs brd-receivers))

