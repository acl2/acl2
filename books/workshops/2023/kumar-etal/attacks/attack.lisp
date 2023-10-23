(in-package "ACL2S")
(include-book "../higher-order")
(include-book "../utils")

(include-book "../network")
(include-book "../utilities")
(include-book "../graphs")


;; Event emission
;; I need skip-proofs because I can't prove:
;; (thm (=> (natp n) (symbolp (nth-symbol n))))
(skip-proofs
 (definecd emit-meshmsgdeliveries-peer-topic
   (p1 :peer p2 :peer top :topic n :nat) :loev
   (match n
     (0 '())
     (& (let ((pld (payload-type (nth-symbol n) (nth-pid-type n) top p1)))
          (app (list (list p1 'SND p2 'PAYLOAD pld)
                     (list p2 'RCV p1 'PAYLOAD pld))
               (emit-meshmsgdeliveries-peer-topic p1 p2 top (1- n))))))))

(definecd emit-meshmsgdeliveries-peer-topics
  (p1 :peer p2 :peer ts :lot n :nat) :loev
  (match ts
    (() '())
    ((top . rst) (append (emit-meshmsgdeliveries-peer-topic p1 p2 top n)
                         (emit-meshmsgdeliveries-peer-topics p1 p2 rst n)))))

(property remove-topic (top :topic ts :lot)
          (lotp (remove-equal top ts)))

(skip-proofs
;; emit attack events from p1 to p2, in the attacked topic top
(definecd emit-evnts (p1 :peer p2 :peer ts ats :lot n m elapsed :nat)
  :loev
  :function-contract-hints (("Goal" :in-theory (enable hbm-evntp evntp loevp)))
  (app (emit-meshmsgdeliveries-peer-topics p1 p2 (set-difference-equal ts ats) n)
       (emit-meshmsgdeliveries-peer-topics p1 p2 ats m)
       `((,p2 HBM ,elapsed)))))

(skip-proofs
;; emit attack events from p1 to p2, in the attacked topic top
(definecd emit-evnts-ticks (p1 :peer p2 :peer ts ats :lot n m elapsed
                               ticks :nat)
  :loev
  (app (emit-evnts p1 p2 ts ats n m elapsed)
       (if (<= (- ticks elapsed) 0)
           nil
         (emit-evnts-ticks p1 p2 ts ats n m elapsed (- ticks elapsed))))))

(check= 95 (len (emit-evnts-ticks 'A 'V (topics) '(SUB1 SUB2 SUB3) 3 1 20
                                  100)))


(skip-proofs
;; emit attack events from p1 to p2, in the attacked topic top
(definecd emit-evnts-eclipse (pats :lop pats2 :lop p2 :peer ts ats :lot n m elapsed
                               ticks :nat)
  :loev
  (match pats
    (() (app `((,p2 HBM ,elapsed))
             (emit-evnts-eclipse pats2 pats2 p2 ts ats n m elapsed (- ticks elapsed))))
    ((p . rst) (app (emit-meshmsgdeliveries-peer-topics p p2 (set-difference-equal ts ats) n)
                    (emit-meshmsgdeliveries-peer-topics p p2 ats m)
                    (if (<= (- ticks elapsed) 0)
                        nil
                      (emit-evnts-eclipse rst pats2 p2 ts ats n m elapsed ticks)))))))


(skip-proofs
;; emit attack events from p1 to p2, in the attacked topic top
(definecd emit-evnts-part (pats :lop pvis :lop pvis2 :lop ts ats :lot n m elapsed
                               ticks :nat)
  :loev
  (match pvis
    (() (emit-evnts-part pats pvis2 pvis2 ts ats n m elapsed (- ticks elapsed)))
    ((p . rst) (app (emit-evnts-eclipse pats pats p ts ats n m elapsed ticks)
                    (if (<= (- ticks elapsed) 0)
                        nil
                      (emit-evnts-part pats rst pvis2 ts ats n m elapsed (1+ elapsed))))))))


(definec construct-mesh (ps :lop ts :lot acc :topic-lop-map) :topic-lop-map
  (match ts
    (() acc)
    ((top . rst)
     (construct-mesh ps rst (mset top ps acc)))))

(skip-proofs
(definec min-mesh-msgs-for-pos-scores (twpm :twp mm :nat) :nat
  (match twpm
    (() mm)
    (((& . (& . params)) . rst)
     (let ((m (params-meshMessageDeliveriesThreshold params)))
       (if (> m mm)
           (min-mesh-msgs-for-pos-scores rst m)
         (min-mesh-msgs-for-pos-scores rst mm)))))))

(definec max-hbm-interval (twpm :twp hbmint :non-neg-rational) :non-neg-rational
  (match twpm
    (() hbmint)
    (((& . (& . params)) . rst)
     (let ((h (params-hbmInterval params)))
       (if (> h hbmint)
           (max-hbm-interval rst h)
         (max-hbm-interval rst hbmint))))))

(definec max-activationwindow (twpm :twp a :non-neg-rational) :non-neg-rational
  (match twpm
    (() a)
    (((& . (& . params)) . rst)
     (let ((aw (params-activationWindow params)))
       (if (> aw a)
           (max-hbm-interval rst aw)
         (max-hbm-interval rst a))))))

(skip-proofs
(definec initialize-group-of-meshpeers (ps :lop mps :lop ts :lot d :nat) :group
  :skip-tests t
  (match ps
    (() '())
    ((p . rst)
     (let ((pmesh (construct-mesh (grab d (remove-equal p (app ps mps))) ts nil)))
       (mset p (peer-state (update-topic-mesh
                            (update-nbr-topicsubs
                             (new-nbr-topic-state)
                             pmesh)
                            pmesh)
                           (new-msgs-state)
                           '()
                           '()
                           '())
             (initialize-group-of-meshpeers rst mps ts d)))))))

(check= t (groupp (initialize-group-of-meshpeers '(A V) '(A V)
                                                 '(AGG BLOCKS SUB1 SUB2 SUB3)
                                                 8)))

(defdata lob (listof boolean))
(defdata lops (listof peer-state))

;; attacker peer p
(definec scorePropViolation (ps :peer-state p :peer ts :lot twpm :twp) :boolean
  :skip-tests t
  :skip-body-contractsp t
  (match ts
    (() (> (lookup-score p (calc-nbr-scores-map (peer-state-nbr-tctrs ps)
                                              (peer-state-nbr-gctrs ps)
                                              twpm))
           0))
     ((top . rst) (^ (< (calcScoreTopic (lookup-tctrs p top (peer-state-nbr-tctrs ps))
                                        (mget top twpm))
                        0)
                     (scorePropViolation ps p rst twpm)))))

(definecd update-group-peer-edge (p1 :peer p2 :peer grp :group ts :lot) :group
  ;; update sub and mesh for each topic, for peer p1 
  (b* ((ps (lookup-state p1 grp))
       (nts (peer-state-nts ps))
       (psub (nbr-topic-state-nbr-topicsubs nts))
       (psubp (reduce* add-peer-subs psub ts p2))
       (pmesh (nbr-topic-state-topic-mesh nts))
       (pmeshp (reduce* add-peer-subs pmesh ts p2))
       (nts1 (update-nbr-topicsubs nts psubp))
       (nts2 (update-topic-mesh nts1 pmeshp)))
    (mset p1
          (mset :nts
                nts2
                ps)
          grp)))

(create-reduce* (lambda (e grp ts)
                  (update-group-peer-edge (cdr e)
                                          (car e)
                                          (update-group-peer-edge (car e)
                                                                  (cdr e)
                                                                  grp
                                                                  ts)
                                          ts))
                groupp
                graphp
                (:name graph->group)
                (:fixed-vars ((lotp ts))))

(check= t
        (groupp
         (update-group-peer-edge 'p1 'p3
                                 (initialize-group-of-meshpeers '(P1 P2 P100)
                                                                '(P1 P2 P100)
                                                                '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                                2)
                                 '(BLOCKS AGG SUB1 SUB2 SUB3))))

(check= t
        (groupp
         (reduce* graph->group 
                  (initialize-group-of-meshpeers '()
                                                 '()
                                                 (topics)
                                                 ;; degree is whatever decided
                                                 ;; by graph, so let it be 100
                                                 100)
                  '((p1 . p3) (p3 . p5))
                  (topics))))



;; Optimized version of run-network, which only records violations
(skip-proofs
(definecd eth-attack-violations (gr :group evnts evnts2 :loev p1 :peer p2 :peer ts
                                    :lot j :nat twpm :twp s :nat acc :lob) :lob
    :ic (is-valid-twp twpm)
    :skip-tests t
    :body-contracts-strictp nil
    (cond
     ((= 100000 j) (cons j (reverse acc)))
     ((endp evnts) (eth-attack-violations gr evnts2 evnts2 p1 p2 ts j twpm s
                                          acc))
     (t (b* (((mv k s) (defdata::genrandom-seed
                         (1- (expt 2 31))
                         (mod s (expt 2 31))))
             (actor (caar evnts))
             (actor-state (lookup-state actor gr))
             (ev (car evnts))
             ((res4 next-actor-state &) (transition actor actor-state ev
                                                      twpm k))
             (newgrp (mset actor next-actor-state gr)))
          (eth-attack-violations
           newgrp
           ;;mix generated events with remaining events
           (cdr evnts)
           evnts2
           p1 ;; attacker
           p2 ;; victim
           ts
           (1+ j)
           twpm
           s
           (if (hbm-evntp ev)
               (cons (scorePropViolation (mget p2 gr) p1 ts twpm) acc)
             acc)))))
    )
)



(definecd pldcache-topic-rcvd (ts :lot mc :mcache) :boolean
  (match mc
    (() nil)
    (((pld . &) . rst) (v (in (payload-type-top pld) ts)
                          (pldcache-topic-rcvd ts rst)))))


;; attacker peer p
(definec eclipseViolation (ps :peer-state ats :lot) :boolean
  :skip-tests t
  :skip-body-contractsp t
  (b* ((mc (msgs-state-pld-cache (peer-state-mst ps))))
    (^ (> (len mc) 0)
       (! (pldcache-topic-rcvd ats mc)))))
       
                                             


;; Optimized version of run-network, which only records violations
(skip-proofs
(definecd eclipse-attack-violations (gr :group evnts evnts2 :loev pats :lop ats :lot
                                        p2 :peer j :nat twpm :twp s :nat acc :lob) :lob
    :ic (is-valid-twp twpm)
    :skip-tests t
    :body-contracts-strictp nil
    (cond
     ((= 100000 j) (cons j (reverse acc)))
     ((endp evnts) (eclipse-attack-violations gr evnts2 evnts2 pats ats p2 j twpm
                                              s acc))
      (t (b* (((mv k s) (defdata::genrandom-seed
                       (1- (expt 2 31))
                       (mod s (expt 2 31))))
           (actor (caar evnts))
           (actor-state (lookup-state actor gr))
           (ev (car evnts))
           ((when (^ (in (car ev) pats)
                     (equal 'RCV (second ev))
                     (equal 'PAYLOAD (fourth ev))
                     (in (payload-type-top (fifth ev)) ats)))
            (eclipse-attack-violations gr (cdr evnts) evnts2 pats ats p2
                                       (1+ j) twpm s acc))
           ((res4 next-actor-state &) (transition actor actor-state ev
                                                    twpm k))
           (newgrp (mset actor next-actor-state gr)))
              (eclipse-attack-violations
               newgrp
               ;;mix generated events with remaining events
               (cdr evnts)
               evnts2
               pats ;; eclipse attackers
               ats ;; ecli
               p2 ;; victim
               (1+ j)
               twpm
               s
               (if (hbm-evntp ev)
                   (cons (eclipseViolation (mget p2 gr) ats) acc)
                 acc)))))
    )
)
