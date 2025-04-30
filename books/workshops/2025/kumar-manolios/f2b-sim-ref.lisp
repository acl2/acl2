(in-package "ACL2S")
(include-book "trx-rels")

;; -------------------------------------------------------
;; Proof of refinement : FloodNet refines BroadcastNet
;; ------------------------------------------------------- 

;; Combined states
(defdata borf (v s-bn s-fn))

(property bn->borf (x :s-bn)
  (borfp x))

(property fn->borf (x :s-fn)
  (borfp x))

(property f2b=>!s-fnp (x :s-fn)
  (=> x
      (! (s-fnp (f2b x))))
  :hints (("Goal" :in-theory
           (enable f2b f2b-help))))

(property x-s-sb-s-fn (x :s-bn :s-fn)
  (null x) 
  :rule-classes :forward-chaining)

;; Combined transition relation
(definec rel-> (s u :borf) :bool
  (v (^ (s-fnp s)
        (s-fnp u)
        (good-rel-step-fn s u))
     (^ (s-bnp s)
        (s-bnp u)
        (rel-step-bn s u))))

(property rel->fnfn (s u :s-fn)
  (== (rel-> s u)
      (^ (good-s-fnp s)
         (good-s-fnp u)
         (rel-step-fn s u))))

(property rel->bnbn (s u :s-bn) 
  (== (rel-> s u)
      (rel-step-bn s u)))


(definec rel-wf (x y :borf) :boolean
  (^ (s-fnp x)
     (s-bnp y)
     (good-s-fnp x)
     (== y (f2b x))))

;; B relation relating states
(definec rel-B (x y :borf) :boolean
  (v (rel-wf x y)
     (== x y)))

(property b-fnbn (s :s-fn w :s-bn)
  (== (rel-B s w)
      (^ (== (f2b s) w)
         (good-s-fnp s))))

(in-theory (disable borfp
                    rel-B
                    rel-B-definition-rule))


;; WFS 1
(property b-maps-f2b (s :s-fn)
  :h (good-s-fnp s)
  :b (rel-B s (f2b s)))


;; WFS 2
(definec L (s :borf) :borf
  (match s
    (:s-bn s)
    (:s-fn (f2b s))))

(property wfs2 (s w :borf)
  :h (rel-B s w)
  :b (== (L s)
         (L w))
  :hints (("Goal" :in-theory (enable rel-B))))

;; WFS 3 provables
(property wfs3-urel->v1-help1 (s u :s-fn)
  :h (rel-skip-fn s u)
  (rel-skip-bn (f2b s) (f2b u))
  :hints (("Goal" :in-theory (enable rel-skip-fn
                                     rel-skip-bn))))

(property wfs3-urel->v1-help2 (s u :s-fn)
  :h (rel-subscribe-fn s u)
  (rel-subscribe-bn (f2b s) (f2b u))
  :hints (("Goal" :in-theory (enable rel-subscribe-fn
                                     rel-subscribe-bn)
           :use ((:instance prop=f2b-subscribe-fn
                            (p (car (fn-topics-witness s u)))
                            (topics (cdr (fn-topics-witness s u))))))))

(property wfs3-urel->v1-help3 (s u :s-fn)
  :h (rel-unsubscribe-fn s u)
  (rel-unsubscribe-bn (f2b s) (f2b u))
  :hints (("Goal" :in-theory (enable rel-unsubscribe-fn
                                     rel-unsubscribe-bn)
           :use ((:instance prop=f2b-unsubscribe-fn
                            (p (car (fn-topics-witness u s)))
                            (topics (cdr (fn-topics-witness u s))))))))

(property wfs3-urel->v1-help4 (s u :s-fn)
  :h (rel-join-fn s u)
  (rel-join-bn (f2b s) (f2b u))
  :instructions
  (:pro (:r 2) :s
        (:claim (^ (fn-join-witness s u)
                   (! (mget (car (fn-join-witness s u)) (f2b s)))
                   (! (in (car (fn-join-witness s u))
                          (topic-lop-map->lop (mget :nsubs (cdr
                                                            (fn-join-witness s u))))))
                   (== u (join-fn (car (fn-join-witness s u))
                         (mget :pubs (cdr (fn-join-witness s u)))
                         (mget :subs (cdr (fn-join-witness s u)))
                         (topic-lop-map->lop
                          (mget :nsubs
                                (cdr (fn-join-witness s u))))
                         s)))
                :hints (("Goal" :in-theory (enable rel-join-fn))))
        
        (:claim (bn-join-witness (f2b s) (f2b u)))
        (:claim (not (mget (car (bn-join-witness (f2b s) (f2b u)))
                           (f2b s)))
                :hints (("Goal" :in-theory (enable rel-join-fn))))
        :s
        (:claim (not (mget (car (bn-join-witness (f2b s) (f2b u))) s)))
        (:claim (== (car (bn-join-witness (f2b s) (f2b u)))
                    (car (fn-join-witness s u))))
        (:claim (not (mget (car (fn-join-witness s u)) s)))
        (= (car (bn-join-witness (f2b s) (f2b u)))
           (car (fn-join-witness s u)))
        (:claim (== (cdr (fn-join-witness s u))
                    (mget (car (fn-join-witness s u)) u)))
        (= (mget :pubs (cdr (bn-join-witness (f2b s) (f2b u))))
           (mget :pubs (cdr (fn-join-witness s u)))
           :hints (("Goal" :use ((:instance
                                  prop=fn-join-witness-preserves-pubs-subs)))))
        (= (mget :subs (cdr (bn-join-witness (f2b s) (f2b u))))
           (mget :subs (cdr (fn-join-witness s u)))
           :hints (("Goal" :use ((:instance
                                  prop=fn-join-witness-preserves-pubs-subs)))))
        (:dv 1)
        (= u (join-fn (car (fn-join-witness s u))
                      (mget :pubs (cdr (fn-join-witness s u)))
                      (mget :subs (cdr (fn-join-witness s u)))
                      (topic-lop-map->lop (mget :nsubs (cdr (fn-join-witness s u))))
                      s))
        :top
        (:prove :hints (("Goal" :use
                         ((:instance prop=f2b-join-fn
                                     (p (car (fn-join-witness s u)))
                                     (pubs (mget :pubs (cdr (fn-join-witness s u))))
                                     (subs (mget :subs (cdr (fn-join-witness s u))))
                                     (nbrs (topic-lop-map->lop
                                            (mget :nsubs (cdr (fn-join-witness s u)))))
                          )))))))

(encapsulate ()
  (local
   (in-theory (enable leave-fn
                      fn-pending-mssgs
                      acl2::maximal-records-theory)))
  
  (property prop=leave-nil-pending (p :peer s :s-fn)
    :h (^ (mget p s)
          (endp (mget :pending (mget p s))))
    (== (fn-pending-mssgs (leave-fn p s))
        (fn-pending-mssgs s))
    :instructions
    (:pro (:induct (leave-fn p s)) :bash
          :pro
          (:claim (!= p (car (car s))))
          (:claim (== (mget p s)
                      (mget p (cdr s))))
          (:claim (== (fn-pending-mssgs (leave-fn p (cdr s)))
                      (fn-pending-mssgs (cdr s))))
          (:claim (== (leave-fn p s)
                      (cons (car s) (leave-fn p (cdr s)))))
          (:claim (s-fnp (leave-fn p s)))
          (:demote 14)
          (:equiv (leave-fn p s)
                  (cons (car s) (leave-fn p (cdr s))))
          :pro (:dv 1) (:r fn-pending-mssgs) :s :up
          (= (cdr (car (leave-fn p s)))
             (cdr (car s)))
          :prove

          (:claim (== p (car (car s))))
          :pro
          (= (leave-fn p s) (cdr s))
          :prove :bash)))
  
(property wfs3-urel->v1-help5 (s u :s-fn)
  :check-contracts? nil
  :h (rel-leave-fn s u)
  (rel-leave-bn (f2b s) (f2b u))
  :instructions
  (:pro
   (:rewrite rel-leave-bn)
   (:claim (^ (fn-join-witness u s)
              (mget (car (fn-join-witness u s)) s)
              (endp (mget :pending (mget (car (fn-join-witness u s)) s)))
              (== u (leave-fn (car (fn-join-witness u s)) s)))
           :hints (("Goal" :in-theory (enable rel-leave-fn))))
   (:claim (== (fn-pending-mssgs (leave-fn (car (fn-join-witness u s)) s))
               (fn-pending-mssgs s))
           :hints (("Goal" :use ((:instance
                                  prop=leave-nil-pending
                                  (p (car (fn-join-witness u s))))))))
   :s (:dv 1)
   (:equiv u (leave-fn (car (fn-join-witness u s)) s))
   :top
   (:prove :hints (("Goal" :use
                    ((:instance prop=f2b-leave-fn
                                (p (car (fn-join-witness u s))))))))))

(property wfs3-urel->v1-help60 (s u :s-fn ms :lom)
  :h (rel-produce-help-fn s u ms)
  (== (f2b u) (f2b s)))

(property wfs3-urel->v1-help6 (s u :s-fn)
  :h (rel-produce-fn s u)
  (rel-skip-bn (f2b s) (f2b u))
  :hints (("Goal" :in-theory (enable rel-produce-fn
                                     rel-skip-bn))))


(property wfs3-urel->v1-help70 (s u :s-fn ms :lom)
  :h (^ (rel-forward-help-fn s u ms)
        (good-s-fnp s)
        (== (fn-pending-mssgs s)
            (fn-pending-mssgs u)))
  (== (f2b u)
      (f2b s))
  :hints (("Goal" :in-theory (enable rel-forward-help-fn))))


(property wfs3-urel->v1-help7 (s u :s-fn)
  :h (^ (rel-forward-fn s u)
        (good-s-fnp s)
        (== (fn-pending-mssgs s)
            (fn-pending-mssgs u)))
  (rel-skip-bn (f2b s) (f2b u))
  :hints (("Goal" :in-theory (enable rel-forward-fn
                                     rel-skip-bn))))



(property prop=fn-pending!=fwd-pending=>!in-fwd-pending (s :s-fn m :mssg)
  :h (^ (in m (fn-pending-mssgs s))
        (!= (fn-pending-mssgs s)
            (fn-pending-mssgs (forward-fn (find-forwarder s m) m s))))
  (! (in m (fn-pending-mssgs (forward-fn (find-forwarder s m) m s))))
  :instructions
  (:pro 
   (:claim (^ (mget (find-forwarder s m) s)
              (in m (mget :pending (mget
                                    (find-forwarder s m)
                                    s)))))

   (:claim  (or (equal (fn-pending-mssgs (forward-fn (find-forwarder s m) m s))
                       (remove-equal m (fn-pending-mssgs s)))
                (equal (fn-pending-mssgs (forward-fn (find-forwarder s m) m s))
                       (fn-pending-mssgs s)))
                :hints (("Goal" :use ((:instance prop=fn-pending-mssgs-forward-fn
                                                 (p (find-forwarder s m)))))))
   :prove))



(property prop=set-diff-insert (m :mssg ms :lom)
  :h (! (in m ms))
  (car (set-difference-equal (insert-unique m ms) ms))
  :instructions
  (:pro
   (:claim (in m (set-difference-equal (insert-unique m ms) ms)))
   (:claim (set-difference-equal (insert-unique m ms) ms))
   :prove))



(definecd ordered-seen-s-bnp (s :s-bn) :bool
  (match s
    (() t)
    (((& . pst) . rst)
     (^ (orderedp (mget :seen pst))
        (ordered-seen-s-bnp rst)))))

(property prop=ordered-seen-s-bnp-cdar (s :s-bn)
  :h (^ s
        (ordered-seen-s-bnp s))
  (orderedp (mget :seen (cdar s)))
  :hints (("Goal" :in-theory (enable ordered-seen-s-bnp))))



(encapsulate ()
  (local
   (property prop=neq-seen-psbn (pst qst :ps-bn)
     :h (!= (mget :seen pst)
            (mget :seen qst))
     (!= pst qst)))

  (local
   (property prop=broadcast-partial-help-neq-car1 (m :mssg ps :lop s :s-bn)
     :h (^ s
           (! (in m (mget :seen (cdar s))))
           (== (car (car s)) (car ps)))
     (!= (car s) (car (broadcast-partial-help m ps s)))
     :instructions
     (:pro
      (:dv 1 2 1) (:r broadcast-partial-help) :s :up :s :top
      (= (car s)
         (cons (car ps)
               (cdar s)))
      (:claim (!= (mget :seen (cdr (car s)))
                  (mget :seen (mset :seen
                                    (insert-unique m (mget :seen (cdr (car s))))
                                    (cdr (car s))))))
      (:prove :hints (("Goal" :use ((:instance
                                     prop=neq-seen-psbn
                                     (pst (cdr (car s)))
                                     (qst (mset :seen
                                                (insert-unique m (mget :seen (cdr (car s))))
                                                (cdr (car s))))))))))))

  (local
   (property prop=broadcast-partial-help-neq-car2 (m :mssg ps :lop s :s-bn)
     :h (^ s
           (! (in m (mget :seen (cdar s))))
           (!= (car s) (car (broadcast-partial-help m ps s))))
     (== (car (car s)) (car ps))
     :hints (("Goal" :in-theory (enable broadcast-partial-help)))))

  (local
   (property prop=broadcast-partial-help-neq-car (m :mssg ps :lop s :s-bn)
     :h (^ s
           (! (in m (mget :seen (cdar s)))))
     (== (!= (car s) (car (broadcast-partial-help m ps s)))
         (== (car (car s)) (car ps)))
     :hints (("Goal" :use ((:instance prop=broadcast-partial-help-neq-car1)
                           (:instance prop=broadcast-partial-help-neq-car2))))))
  

  (local
   (in-theory (enable broadcast-partial-help)))

  (local
   (property prop=new-bn-mssgp-cdar (m :mssg s :s-bn)
     :h (^ s (new-bn-mssgp m s))
     (! (in m (mget :seen (cdar s))))
     :hints (("Goal" :in-theory (enable new-bn-mssgp)))))

  (local
   (property prop=mget-cdr-s-bn (p :peer s :s-bn )
     :h (^ (mget p s)
           (!= p (car (car s))))
     (mget p (cdr s))
     :hints (("Goal" :in-theory (enable acl2::maximal-records-theory)))))

  (local
   (property prop=broadcast-partial-help-cdr (m :mssg ps :lop s :s-bn)
     :h (^ s (!= (car (car s)) (car ps)))
     (== (cdr (broadcast-partial-help m ps s))
         (broadcast-partial-help m ps (cdr s)))
     :hints (("Goal" :in-theory (enable broadcast-partial-help)))))



  (property prop=br-mssg-witness-help2 (m :mssg ps :lop s :s-bn)
    :h (^ (ordered-seen-s-bnp s)
          (mget (car ps) s)
          (new-bn-mssgp m s))
    (== (br-mssg-witness s (broadcast-partial-help m ps s)) m)
    :instructions
    (:pro :induct :bash :pro
          (:dv 1) (:r br-mssg-witness) :s
          (:claim (! (in m (mget :seen (cdar s))))
                  :hints (("Goal" :use ((:instance prop=new-bn-mssgp-cdar)))))
          (:claim (== (car (car s)) (car ps))
                  :hints (("Goal" :use ((:instance
                                         prop=broadcast-partial-help-neq-car)))))
          (:dv 1 1 2 1 1)
          (:r broadcast-partial-help) :s :top :s
          (:claim (orderedp (mget :seen (cdr (car s)))))
          (:claim (! (in m (mget :seen (cdr (car s)))))
                  :hints (("Goal" :use ((:instance prop=new-bn-mssgp-cdar)))))
          (:claim (tlp (mget :seen (cdr (car s)))))
          (= (set-difference-equal (insert-unique m (mget :seen (cdr (car s))))
                                   (mget :seen (cdr (car s))))
             (insert-unique m (set-difference-equal (mget :seen (cdr (car s)))
                                                    (mget :seen (cdr (car s)))))
             :hints (("Goal" :use ((:instance
                                    prop=set-diff-insert-!in
                                    (xs (mget :seen (cdr (car s))))
                                    (ys (mget :seen (cdr (car s)))))))))
          :prove :pro
          (:claim (ps-bnp (cdr (car s))))
          (:prove :hints (("Goal" :in-theory (enable ps-bnp))))
          
          :pro
          (:claim (! (in m (mget :seen (cdar s))))
                  :hints (("Goal" :use ((:instance prop=new-bn-mssgp-cdar)))))
          (:claim (!= (car (car s)) (car ps))
                  :hints (("Goal" :use ((:instance
                                         prop=broadcast-partial-help-neq-car)))))
          (:claim (mget (car ps) (cdr s))
                  :hints (("Goal" :use ((:instance prop=mget-cdr-s-bn
                                                   (p (car ps)))))))
          (:claim (new-bn-mssgp m (cdr s))
                  :hints (("Goal" :in-theory (enable new-bn-mssgp))))
          (:claim (ordered-seen-s-bnp (cdr s))
                  :hints (("Goal" :in-theory (enable ordered-seen-s-bnp))))
          (:claim (equal (br-mssg-witness
                          (cdr s)
                          (broadcast-partial-help m
                                                  (if (equal (car (car s)) (car ps))
                                                      (cdr ps)
                                                    ps)
                                                  (cdr s)))
                         m))

          (:claim (== (broadcast-partial-help m ps s)
                      (cons (car s)
                            (broadcast-partial-help m ps (cdr s)))))
          (:claim (s-bnp (broadcast-partial-help m ps s)))
          (:demote 18)
          (:equiv (broadcast-partial-help m ps s)
                  (cons (car s)
                        (broadcast-partial-help m ps (cdr s))))
          :pro (:dv 1) (:r br-mssg-witness) :s :top :prove

          :pro
          (:prove :hints (("Goal" :in-theory (enable br-mssg-witness)))))))



(property prop=f2b-ordered-seenp-help (ms :lom s :s-fn)
  :h (ordered-seenp s)
  (ordered-seen-s-bnp (f2b-help s ms))
  :instructions
  (:pro :induct :pro
        (:claim (ordered-seenp (cdr s)))
        (:claim (ordered-seen-s-bnp
                 (f2b-help (cdr s) ms)))
        (:claim (== (f2b-help s ms)
                    (cons (cons (caar s)
                                (f2b-st (cdar s) ms))
                          (f2b-help (cdr s) ms)))
                :hints (("Goal" :use ((:instance
                                       prop=f2b-helper-def)))))
        (:claim (s-bnp (f2b-help s ms)))
        (:demote 10)
        (:equiv (f2b-help s ms)
                (cons (cons (caar s)
                            (f2b-st (cdar s) ms))
                      (f2b-help (cdr s) ms)))
        :pro
        (:r ordered-seen-s-bnp) :s
        (= (cdr (car (f2b-help s ms)))
           (f2b-st (cdr (car s)) ms))
        (= (mget :seen (f2b-st (cdr (car s)) ms))
           (set-difference-equal (mget :seen (cdr (car s))) ms))
        (:claim (orderedp (mget :seen (cdr (car s)))))
        (:prove :hints (("Goal" :use ((:instance
                                       orderedp-set-difference
                                       (xs (mget :seen (cdr (car s))))
                                       (ys ms))))))
        :pro
        (:prove :hints (("Goal" :in-theory (enable f2b-help))))))



(property prop=f2b-ordered-seenp (s :s-fn)
  :h (ordered-seenp s)
  (ordered-seen-s-bnp (f2b s))
  :hints (("Goal" :in-theory (enable f2b)
           :use ((:instance prop=f2b-ordered-seenp-help
                            (ms (fn-pending-mssgs s)))))))


(property rel-fwd-help-90 (ms :lom s u :s-fn)
  :check-contracts? nil
  :h (^ (rel-forward-help-fn s u ms)
        (good-s-fnp s))
  (v (rel-broadcast-partial-bn (f2b s) (f2b u))
     (== (f2b s) (f2b u)))
  :instructions
  (:pro (:induct (rel-forward-help-fn s u ms)) :bash
        :pro
        (:claim (rel-forward-help-fn s u (cdr ms)))
        (:claim (or (rel-broadcast-partial-bn (f2b s) (f2b u))
                    (equal (f2b s) (f2b u))))
        (:demote 12) :s

        :pro
        (:casesplit (== (fn-pending-mssgs s)
                        (fn-pending-mssgs u)))
        (:prove :hints (("Goal" :in-theory (enable rel-forward-help-fn))))
        
        
        (:claim (^ (mget (find-forwarder s (car ms)) s)
                   (in (car ms) (mget :pending (mget (find-forwarder s (car ms)) s)))
                   (! (new-fn-mssgp (car ms) s)))
                :hints (("Goal" :use ((:instance find-forwarder-contract
                                                 (m (car ms)))))))
        (:claim (! (in (car ms)
                       (fn-pending-mssgs
                        (forward-fn (find-forwarder s (car ms)) (car ms) s))))
                :hints (("Goal" :use ((:instance
                                       prop=fn-pending!=fwd-pending=>!in-fwd-pending
                                       (m (car ms)))))))

        (:claim (mget (car (brd-receivers (car ms)
                                          (forward-fn (find-forwarder s (car ms))
                                                      (car ms) s)))
                      s)
                :hints (("Goal" :use ((:instance
                                       prop=mget-car-brd-receivers-forward-fn
                                       (p (find-forwarder s (car ms)))
                                       (m (car ms)))))))
        (:claim (new-bn-mssgp (car ms) (f2b s))
                :hints (("Goal" :use ((:instance
                                       prop=in-fn-pending=>new-bn-mssgp
                                       (m (car ms)))))))
        (:claim (br-mssg-witness (f2b s)
                                 (broadcast-partial-help
                                  (car ms)
                                  (brd-receivers (car ms)
                                                 (forward-fn (find-forwarder s
                                                                             (car ms))
                                                             (car ms) s))
                                  (f2b s)))
                :hints (("Goal" :use
                         ((:instance prop=br-mssg-witness-help2
                                     (m (car ms))
                                     (ps (brd-receivers (car ms)
                                                        (forward-fn (find-forwarder s
                                                                                    (car ms))
                                                                    (car ms)
                                                                    s))))))))
        (:claim (ordered-seenp s))
        (:casesplit (== (f2b s) (f2b u))) :s :s
        
        (:r rel-broadcast-partial-bn) :s
        (:claim (== (f2b u)
                    (broadcast-partial-help (car ms)
                                            (brd-receivers (car ms)
                                                           (forward-fn
                                                            (find-forwarder s (car ms)) (car ms) s))
                                            (f2b s)))
                :hints (("Goal" :use ((:instance prop=forward-fn2-broadcast
                                                 (p (find-forwarder s (car ms)))
                                                 (m (car ms)))))))
        (:claim (br-mssg-witness (f2b s) (f2b u))) :s

        (:claim (ordered-seen-s-bnp (f2b s))
                :hints (("Goal" :use ((:instance prop=f2b-ordered-seenp)))))
        (:claim (mget (car (brd-receivers (car ms)
                              (forward-fn (find-forwarder s (car ms))
                                          (car ms)
                                          s)))
                      (f2b s))
                :hints (("Goal" :use ((:instance
                                       prop=mget=>mget-f2b
                                       (p (car (brd-receivers (car ms)
                                                              (forward-fn (find-forwarder s (car ms))
                                                                          (car ms)
                                                                          s)))))))))
        (:claim (== (br-mssg-witness
                     (f2b s)
                     (broadcast-partial-help
                      (car ms)
                      (brd-receivers (car ms)
                                     (forward-fn (find-forwarder s (car ms))
                                                 (car ms)
                                                 s))
                      (f2b s)))
                    (car ms))
                    :hints (("Goal" :use ((:instance
                                           prop=br-mssg-witness-help2
                                           (m (car ms))
                                           (ps (brd-receivers (car ms)
                                                              (forward-fn (find-forwarder s (car ms))
                                                                          (car ms)
                                                                          s)))
                                           (s (f2b s)))))))
        (:claim (== (br-mssg-witness (f2b s) (f2b u))
                    (car ms)))
        (:equiv (br-mssg-witness (f2b s) (f2b u))
                (car ms))
        :s

        (= (broadcast-partial (car ms)
                          (brd-receivers-bn (car ms) (f2b u))
                          (f2b s))
           (broadcast-partial-help (car ms)
                          (brd-receivers-bn (car ms) (f2b u))
                          (f2b s))
           :hints (("Goal" :in-theory (enable broadcast-partial))))
        (:dv 1)
        (:equiv (f2b u)
                (broadcast-partial-help
                (car ms)
                (brd-receivers (car ms)
                               (forward-fn (find-forwarder s (car ms))
                                           (car ms)
                                           s))
                (f2b s)))
        :up
        (:dv 2 2 2)
        (= (f2b u) (f2b-help u (fn-pending-mssgs u))
           :hints (("Goal" :in-theory (enable f2b))))
        :top
        (:equiv (forward-fn (find-forwarder s (car ms))
                                 (car ms)
                                 s)
                u)
        (:claim (! (in (car ms) (fn-pending-mssgs u))))
        
        (= (brd-receivers-bn (car ms) (f2b-help u (fn-pending-mssgs u)))
           (brd-receivers (car ms) u)
           :hints (("Goal" :use ((:instance prop=brd-receivers-bn-fn
                                            (m (car ms))
                                            (ms (fn-pending-mssgs u))
                                            (s u))))))
        :s :bash))



(property wfs3-urel->rel-fwd (s u :s-fn)
  :h (^ (good-s-fnp s)
        (rel-forward-fn s u))
  (v (rel-broadcast-partial-bn (f2b s) (f2b u))
     (rel-skip-bn (f2b s) (f2b u)))
  :instructions
  (:pro
   (:claim (rel-forward-help-fn s u (fn-pending-mssgs s))
           :hints (("Goal" :in-theory (enable rel-forward-fn))))
   (= (rel-skip-bn (f2b s) (f2b u))
      (== (f2b s) (f2b u))
      :hints (("Goal" :in-theory (enable rel-skip-bn))))
   (:claim (v (rel-broadcast-partial-bn (f2b s) (f2b u))
              (== (f2b s) (f2b u)))
           :hints (("Goal" :use ((:instance rel-fwd-help-90
                                            (ms (fn-pending-mssgs s)))))))
   (:demote 6) :s))


(definec exists-v1 (s u :s-fn) :s-bn
  :ic (good-s-fnp s)
  :body-contracts-hints (("Goal"
                          :in-theory (enable rel-skip-bn
                                             rel-broadcast-partial-bn)
                          :use ((:instance wfs3-urel->rel-fwd))))
  (cond
   ((rel-skip-fn s u) (f2b s))
   ((^ (rel-forward-fn s u)
       (!= (f2b s) (f2b u)))
    (broadcast-partial (br-mssg-witness (f2b s) (f2b u))
                       (brd-receivers-bn
                        (br-mssg-witness (f2b s) (f2b u))
                        (f2b u))
                       (f2b s)))
   (t (f2b u))))


(property wfs3-uBv1-help (s u :s-fn)
  :check-contracts? nil
  :h (good-rel-step-fn s u)
  (rel-b u (exists-v1 s u))
  :instructions
  (:pro (:claim (^ (good-s-fnp s)
                   (good-s-fnp u)
                   (rel-step-fn s u)))
        (:rewrite b-fnbn)
        (:casesplit (rel-skip-fn s u))
        (= u s :hints (("Goal" :in-theory
                        (enable rel-skip-fn))))
        :s
        (:casesplit (rel-forward-fn s u))
        (:casesplit (!= (f2b s) (f2b u)))
        (= (exists-v1 s u)
           (broadcast-partial (br-mssg-witness (f2b s) (f2b u))
                              (brd-receivers-bn (br-mssg-witness (f2b s) (f2b u))
                                                (f2b u))
                              (f2b s)))
        (:claim (rel-broadcast-partial-bn (f2b s) (f2b u))
                :hints (("Goal" :in-theory (enable rel-skip-bn)
                         :use ((:instance wfs3-urel->rel-fwd)))))
        (:prove :hints (("Goal" :in-theory
                         (enable rel-broadcast-partial-bn))))

        (= (exists-v1 s u) (f2b s)) :s

        (:casesplit (rel-subscribe-fn s u)) :s
        (:casesplit (rel-unsubscribe-fn s u)) :s
        (:casesplit (rel-join-fn s u)) :s
        (:casesplit (rel-leave-fn s u)) :s :s))


(property wfs3-urel->v1-help (s u :s-fn)
  :h (^ (good-s-fnp s)
        (rel-step-fn s u))
  (rel-step-bn (f2b s) (exists-v1 s u))
  :instructions
  (:pro (:casesplit (rel-skip-fn s u)) 
        (:prove :hints (("Goal" :in-theory (enable rel-skip-fn
                                                   rel-skip-bn))))
        (:casesplit (rel-forward-fn s u))
        (:casesplit (! (rel-skip-bn (f2b s) (f2b u))))
        (:dv 2) (:r exists-v1) :s :top
        (:claim (rel-broadcast-partial-bn (f2b s) (f2b u))
                :hints (("Goal" :use ((:instance wfs3-urel->rel-fwd)))))
        (:claim (!= (f2b s) (f2b u))
                :hints (("Goal" :in-theory (enable rel-skip-bn))))
        :s
        (:prove :hints (("Goal" :in-theory
                         (enable rel-broadcast-partial-bn))))
        (:prove :hints (("Goal" :in-theory (enable rel-skip-bn))))
        (:casesplit (rel-subscribe-fn s u)) 
        (:prove :hints (("Goal" :use ((:instance wfs3-urel->v1-help2)))))
        (:casesplit (rel-unsubscribe-fn s u)) 
        (:prove :hints (("Goal" :use ((:instance wfs3-urel->v1-help3)))))
        (:casesplit (rel-join-fn s u)) 
        (:prove :hints (("Goal" :use ((:instance wfs3-urel->v1-help4)))))
        (:casesplit (rel-leave-fn s u))
        (:prove :hints (("Goal" :use ((:instance wfs3-urel->v1-help5)))))
        (:casesplit (rel-produce-fn s u))
        (:prove :hints (("Goal" :in-theory (enable rel-step-fn rel-skip-bn))))
        :prove))



(propertyd wfs3-1 (s u :s-fn w :s-bn)
  :h (^ (rel-B s w)
        (rel-> s u))
  (^ (rel-> w (exists-v1 s u))
     (rel-B u (exists-v1 s u)))
  :instructions
  (:pro
   (= w (f2b s))
   (:claim (good-rel-step-fn s u))
   (= (rel-> (f2b s)
             (exists-v1 s u))
      (rel-step-bn (f2b s) (exists-v1 s u))
      :hints (("Goal" :in-theory (disable exists-v1-definition-rule))))
   (:claim (good-s-fnp s))
   (:claim (rel-step-bn (f2b s) (exists-v1 s u))
           :hints (("Goal" :use ((:instance wfs3-urel->v1-help)))))
   (:claim (rel-B u (exists-v1 s u))
           :hints (("Goal" :use ((:instance wfs3-uBv1-help)))))
   :s))



(in-theory (e/d (rel->) (exists-v1 rel-B)))


(property prop=rel-B-nil (s w :borf)
  :h (^ (null s)
        (rel-B s w))
  (endp w)
  :hints  (("Goal" :in-theory (enable rel-B f2b f2b-help))))

(property prop=rel-B-cons (s w :borf)
  :h (^ (not (null s))
        (rel-B s w))
  (consp w)
  :hints (("Goal" :in-theory (enable rel-B f2b f2b-help))))

(property prop=empty-rel-step-borf (u :borf)
  :check-contracts? nil
  :h (^ u (rel-> nil u))
  (v (rel-join-bn nil u)
     (rel-join-fn nil u))
  :instructions
  (:pro
   (:casesplit (s-bnp u))
   (:prove :hints (("Goal" :in-theory (enable rel-skip-bn)
                    :use ((:instance prop=empty-rel-step-bn
                                     (s nil))))))
   (:prove :hints (("Goal" :in-theory (enable rel-skip-fn)
                    :use ((:instance prop=empty-rel-step-fn)))))
   ))


(definec exists-nil-v (u :borf) :borf
  :function-contract-hints (("Goal"
                             :instructions
                             (:pro
                              (:claim (borfp (exists-v1 nil u)))
                              (:claim (v (rel-join-bn nil u)
                                         (rel-join-fn nil u))
                                      :hints (("Goal"
                                               :use ((:instance prop=empty-rel-step-borf)))))
                              :prove)))
  :ic (^ u (rel-> nil u))
  (match u
    (:s-fn (exists-v1 nil u))
    (:s-bn u)))

(definec exists-cons-v (s u w :borf) :borf
  :ic (^ s
         (rel-B s w)
         (rel-> s u))
  (cond
   ((^ (s-bnp s) (s-bnp w)) u)
   ((^ (s-fnp s) (s-bnp w)) (exists-v1 s u))
   ((^ (s-fnp s) (s-fnp w)) u)))

;; Witness function producing state v
(definec exists-v (s u w :borf) :borf
  :function-contract-hints (("Goal" :in-theory
                             (disable exists-nil-v-definition-rule
                                      exists-cons-v-definition-rule)))
  :ic (^ (rel-B s w)
         (rel-> s u))
  (if (null s)
      (if (null u)
          nil
        (exists-nil-v u))
    (exists-cons-v s u w)))


(property prop=cons-s-exists-v (s u w :borf)
  :h (^ s
        (rel-B s w)
        (rel-> s u))
  (== (exists-v s u w)
      (exists-cons-v s u w))
  :instructions
  (:pro
   (:dv 1) (:r 2) :s :up (:dv 2) :s :up :s))



(property wfs3-nil (s u w :borf)
  :check-contracts? nil
  :h (^ (rel-B s w)
        (rel-> s u)
        (null s))
  (^ (rel-> w (exists-v s u w))
     (rel-B u (exists-v s u w)))
  :instructions
  (:pro
   
   (:claim (== w nil)
           :hints (("Goal" :use ((:instance prop=rel-B-nil)))))
      
   (:casesplit (null u))
   (= u nil)
   (= (exists-v s nil w) nil)
   (:prove :hints (("Goal" :use ((:instance
                                  wfs3-1 (s nil) (w nil))))))

   (:casesplit (s-fnp u))
   (= (exists-v s u w)
      (exists-v1 nil u))
   (:prove :hints (("Goal" :use ((:instance
                                  wfs3-1 (s nil) (w nil))))))

   (:claim (s-bnp u))
   (= (exists-v s u w) u)
   (= w s)
   (:claim (rel-b u u)
           :hints (("Goal" :in-theory (enable rel-b))))
   :prove))


(property wfs3-help (s u w :borf)
  :h (^ (rel-B s w)
        (rel-> s u))
  (^ (rel-> w (exists-v s u w))
     (rel-B u (exists-v s u w)))
  :instructions
  (:pro
   (:casesplit (null s))
   (:prove :hints (("Goal" :use ((:instance wfs3-nil)))))

   (:claim s)
   (:claim (consp w)
           :hints (("Goal" :use ((:instance
                                  prop=rel-B-cons)))))
   (= (exists-v s u w)
      (exists-cons-v s u w)
      :hints (("Goal" :use ((:instance
                             prop=cons-s-exists-v)))))

   (:casesplit (s-bnp w))
   (:casesplit (s-bnp s))
   (= (exists-cons-v s u w) u)
   (= w s :hints (("Goal" :in-theory (enable rel-b))))
   (:claim (rel-b u u)
           :hints (("Goal" :in-theory (enable rel-b))))
   :s

   (:claim (s-fnp s))
   (= (exists-cons-v s u w) (exists-v1 s u)
      :hints (("Goal" :in-theory (enable exists-cons-v))))
   (:claim (s-fnp u))
   (:prove :hints (("Goal" :use ((:instance wfs3-1)))))

   (:claim (s-fnp w))
   (:claim (== w s) :hints
           (("Goal" :in-theory (enable rel-b))))
   (:demote 10) (:equiv w s) :pro
   (:claim (s-fnp w))
   (= (exists-cons-v s u s) u)
   (:claim (rel-b u u)
           :hints (("Goal" :in-theory (enable rel-b))))
   :s))

;; WFS3
(defun-sk exists-v-wfs (s u w)
  (exists (v)
    (^ (rel-> w v)
       (rel-B u v))))

(property wfs3 (s w u :borf)
  :check-contracts? nil
  :h (^ (rel-B s w)
        (rel-> s u))
  :b (exists-v-wfs s u w)
  :hints (("Goal" :use ((:instance wfs3-help)
                        (:instance exists-v-wfs-suff
                                   (v (exists-v s u w)))))))
