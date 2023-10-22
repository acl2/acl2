(in-package "ACL2S")
(include-book "higher-order")
(include-book "utils")

(def-const *few-seconds* 5)
(def-const *two-minutes* 120)

(include-book "network")
(include-book "utilities")
(include-book "graphs")

;Uncomment line 30 : '(BLOCKS AGG SUB1 SUB2 SUB3)) in scoring.lisp

;; ------------------ Eth2.0 Case Study (github.com/silesiacoin/prysm-spike) ------------------------------

;; Refer to https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;          beacon-chain/p2p/gossip_scoring_params.go
;;
;; d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f
;;
;;
;; GossipSub is my private version forked off of be065ce0510e81d820a2cdb9762e63fd012122ba
;; Libp2p is my private version forked off of 4400328a581babd9a196e1ddffbe996ae7b3b59

;;    IPColocationFactorThreshold = 10
;;    BehaviourPenaltyThreshold   = 6
;;    BehaviourPenaltyDecay       = 10 epochs
;;    DecayInterval               = 1 slot duration
;;    DecayToZero                 = 0.01
;;    RetainScore                 = 100 epoch durations

(defconst *decayToZero* 1/100)

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     shared/params/config.go#L123

(defconst *seconds-per-slot* 1) ;; ARBITRARY 
(defconst *one-epoch-duration* 1) ;; ARBITRARY 

(defconst *aggregateWeight* (/ 1 2)) ;; weight for aggregate topic, see #L100
(defconst *beaconBlockWeight* (/ 8 10)) ;; weight for beacon topic, see #L77

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/gossip_scoring_params.go#L154
(defconst *slot-duration* (* *seconds-per-slot* 1))

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;    shared/params/config.go#L48
(defconst *slots-per-epoch* 10) ;; ARBITRARY 
(defconst *blocks-per-epoch* *slots-per-epoch*) ;; #L75
(defconst *decay-epoch* 5) ;; #L74

;; In line number comments, if I write BC, I am referring to:
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/pubsub.go

;; If I write SERV, I am referring to:
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/service.go

;; In all other cases, as indicated previously, I am referring to gossip_scoring_params.go.

;; I assume all times are given in units of 1 second ...

(defconst *enable-larger-gossip-history* 'nil)

(defconst *hbmInterval* (/ 700 1000))

(defconst *topicCap* (+ 32 (/ 72 100)))

(defconst *comm-count-per-slot* 10) ;; ARBITRARY - refer to #L173 ... they have not decided yet!
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     shared/params/config.go#L123
(defconst *target-aggregators-per-committee* 5) ;; ARBITRARY
(defconst *aggregators-per-slot* (* *comm-count-per-slot* *target-aggregators-per-committee*)) ;; #L1871
(defconst *agg-per-epoch* (* *aggregators-per-slot* *slots-per-epoch*))
(defconst *attestationTotalWeight* 1) ;; #L23
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;; shared/params/network_config.go#L40
(defconst *AttestationSubnetCount* 3)         ;; ARBITRARY 
(defconst *MinGenesisActiveValidatorCount* 300) ;; ARBITRARY -----------------|
;; -------> but currently needs to be divisible by 50 x attestationSubnetCount.

(defconst *subnet-topicWeight* (/ *attestationTotalWeight* *AttestationSubnetCount*)) ;; #L121
(defconst *activeValidators* *MinGenesisActiveValidatorCount*) ;; #L169
(defconst *subnet-subnetWeight* (/ *activeValidators* *AttestationSubnetCount*)) ;; #L122
(defconst *subnet-minimumWeight* (/ *subnet-subnetWeight* 50)) ;; #L123
(defconst *subnet-numsPerSlot* (/ *subnet-subnetWeight* *slots-per-epoch*)) ;; #L124
(defconst *subnet-comsPerSlot* *comm-count-per-slot*) ;; #L125
(defconst *subnet-exceedsThreshold*
  (>= *subnet-comsPerSlot*
      (* 2 (/ *AttestationSubnetCount* *slots-per-epoch*)))) ;; #L126
(defconst *subnet-firstDecay* (if *subnet-exceedsThreshold* 4 1)) ;; #L127, 130
(defconst *subnet-meshDecay* (if *subnet-exceedsThreshold* 16 4)) ;; #L128, 131

(defconst *eth-default-block-weights*
  (weights (/ 324 10000)  ;; w_1  = time in mesh weight                (#L78)
           1              ;; w_2  = first message deliveries weight    (#L81)
           (/ -717 1000)  ;; w_3  = mesh message deliveries weight     (#L84)
           (/ -717 1000)  ;; w_3b = mesh failure penalty weight        (#L90)
           (- -140 (/ 4475 10000)) ;; w_4  = invalid messages weight   (#L92)
           1       ;; w_5  = application-specific score weight         (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-block-weights*))

(defconst *eth-default-agg-weights*
  (weights (/ 324 10000) ;; w_1  = time in mesh weight              (#L101)
           (/ 128 1000)  ;; w_2  = first message deliveries weight  (#L104)
           (/ -64 1000)  ;; w_3  = mesh message deliveries weight   (#L107)
           (/ -64 1000)  ;; w_3b = mesh failure penalty weight      (#L113)
           (- -140 (/ 4475 10000)) ;; w_4 = invalid messages weight (#L115)
           1             ;; w_5 = application-specific score weight    (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-agg-weights*))

(defconst *eth-default-agg-subnet-weights*
  (weights (/ 324 10000) ;; w_1 = time in mesh weight                  (#L134)
           (/ 955 1000)  ;; w_2 = first message deliveries weight      (#L138)
           (- -37 (/ 55 100)) ;; w_3  = mesh message deliveries weight (#L141)
           (- -37 (/ 55 100)) ;; w_3b = mesh failure penalty weight    (#L147)
           -4544              ;; w_4 = invalid messages weight 
           1       ;; w_5  = application-specific score weight         (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-agg-subnet-weights*))

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L162
(definecd scoreDecay(x :non-neg-rational) :non-neg-rational
  (b* (((when (= x 0)) 0)
       (numOfTimes (/ x *slot-duration*)))
    (expt *decayToZero* (floor 1 numOfTimes))))

;; Currently failing ...
(defconst *eth-default-block-params*
  (params 4               ;; activationWindow    : #L89 aka MeshMessageDeliveriesActivation
	  *slot-duration* ;; meshTimeQuantum     : #L79
	  23              ;; p2cap               : #L83 aka FirstMessageDeliveriesCap
	  300             ;; timeQuantaInMeshCap : #L80
	  (* *blocks-per-epoch*
	     *decay-epoch*) ;; meshMessageDeliveriesCap : #L86
	  ;; meshMessageDeliveriesThreshold             : #L87
	  (/ (* *blocks-per-epoch* *decay-epoch*) 10)
	  *topicCap*        ;; topiccap          : #L39 (global)
	  -16000            ;; greyListThreshold : #L33 (global)
	  8                 ;; d                 : BC #L120
	  6                 ;; dlow              : BC #L119
	  12                ;; dhigh             : default in gossipsub.go
	  6                 ;; dlazy             : default in gossipsub.go
	  *hbmInterval* ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60 ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval*) ;; seenTTL       : BC #L124
	  ;; https://github.com/silesiacoin/prysm-spike/blob/
	  ;; d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L35
	  5 ;; opportunisticGraftThreshold
	  ;; Let scoreDecay(x) = decayToZero^(1/(x/oneSlotDuration)).  Then, starting at:
	  ;;
	  ;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
	  ;;     beacon-chain/p2p/gossip_scoring_params.go#L73
	  ;;
	  *beaconBlockWeight*
	  ;; MeshMessageDeliveriesDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  (scoreDecay (* *decay-epoch* *one-epoch-duration*))
	  ;; FirstMessageDeliveriesDecay = scoreDecay(20 * oneEpochDuration)
	  (scoreDecay (* 20 *one-epoch-duration*)) 
	  (scoreDecay (* 10 *one-epoch-duration*)) ;; behaviourPenaltyDecay
	  ;;  MeshFailurePenaltyDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  (scoreDecay (* *decay-epoch* *one-epoch-duration*))
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 * oneEpochDuration)
	  (scoreDecay (* 50 *one-epoch-duration*))
	  *decayToZero* ;; decayToZero
	  *slot-duration* ;; decayInterval
	  ))

(check= t (paramsp *eth-default-block-params*))

(defconst *eth-default-aggregate-params*
  (params (* 32 *slot-duration*) ;; activationWindow               : #L112
	  *slot-duration*        ;; meshTimeQuantum                : #L102
	  179                    ;; p2cap                          : #L106
	  300                    ;; timeQuantaInMeshCap            : #L103
	  *agg-per-epoch*        ;; meshMessageDeliveriesCap       : #L109
	  (/ *agg-per-epoch* 50) ;; meshMessageDeliveriesThreshold : #L110
	  *topicCap*             ;; topicCap,          see above (global)
	  -16000                 ;; greyListThreshold, see above (global)
	  8                      ;; d                                   : BC #L120
	  6                      ;; dlow                                : BC #L119
	  12                     ;; dhigh                               : default in gossipsub.go
	  6                      ;; dlazy                               : default in gossipsub.go
	  *hbmInterval*          ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60                     ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
          ;; TODO : clarify gossipfactor
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval*) ;; seenTTL : BC #L124
	  5 ;; opportunisticGraftThreshold
	  *aggregateWeight* ;; topicWeight = aggregateWeight       #L100
	  (scoreDecay *one-epoch-duration*) ;; MeshMessageDeliveriesDecay  = scoreDecay(1 epoch) #L108
	  (scoreDecay *one-epoch-duration*) ;; FirstMessageDeliveriesDecay = scoreDecay(1 epoch) #L105
	  (scoreDecay (* 10 *one-epoch-duration*)) ;; behaviourPenaltyDecay
	  (scoreDecay *one-epoch-duration*) ;; MeshFailurePenaltyDecay     = scoreDecay(1 epoch) #L114
	  (scoreDecay (* 50 *one-epoch-duration*)) ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs) #L116
	  *decayToZero*
	  *slot-duration*
	  ))

(check= t (paramsp *eth-default-aggregate-params*))

(defconst *eth-default-aggregate-subnet-params*
  (params (* 17 *slot-duration*) ;; activationWindow               : #L146
	  *subnet-numsPerSlot*   ;; meshTimeQuantum                : #L136
	  24                     ;; p2cap                          : #L140
	  300                    ;; timeQuantaInMeshCap            : #L137
	  *subnet-subnetWeight*  ;; meshMessageDeliveriesCap       : #L143
	  *subnet-minimumWeight* ;; meshMessageDeliveriesThreshold : #L144
	   *topicCap*             ;; topicCap,          see above (global)
	  -16000                 ;; greyListThreshold, see above (global)
	  8                      ;; d                                   : BC #L120
	  6                      ;; dlow                                : BC #L119
	  12                     ;; dhigh                               : default in gossipsub.go
	  6                      ;; dlazy                               : default in gossipsub.go
	  *hbmInterval*          ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60                     ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
          ;; TODO
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval*) ;; seenTTL : BC #L124
	  5 ;; OpportunisticGraftThreshold
	  ;; TODO: MeshMessageDeliveriesWindow   = 2 seconds                           #L145
	  *subnet-topicWeight*  ;; topicWeight   = *subnet-topicWeight*                      #L134
	  ;; MeshMessageDeliveriesDecay    = scoreDecay(*subnet-meshDecay* x 1 epoch)  #L142
	  (scoreDecay (* *subnet-meshDecay* *one-epoch-duration*))
	  ;; FirstMessageDeliveriesDecay   = scoreDecay(*subnet-firstDecay* x 1 epoch) #L139
	  (scoreDecay (* *subnet-firstDecay* *one-epoch-duration*))
	  (scoreDecay (* 10 *one-epoch-duration*)) ;; behaviourPenaltyDecay
	  ;; MeshFailurePenaltyDecay       = scoreDecay(*subnet-meshDecay* x 1 epoch)  #L148
	  (scoreDecay (* *subnet-meshDecay* *one-epoch-duration*))
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs)                     #L150
	  (scoreDecay (* 50 *one-epoch-duration*))
	  *decayToZero*
	  *slot-duration*
	  ))

(check= t (paramsp *eth-default-aggregate-subnet-params*))

(defconst *eth-twp*
  `((AGG . (,*eth-default-agg-weights* . ,*eth-default-aggregate-params*))
    (BLOCKS . (,*eth-default-block-weights* . ,*eth-default-block-params*))
	;; We can have 0 or more subnet aggregator topics.  For now, let's assume 3.
    (SUB1 . (,*eth-default-agg-subnet-weights* . ,*eth-default-aggregate-subnet-params*))
    (SUB2 . (,*eth-default-agg-subnet-weights* . ,*eth-default-aggregate-subnet-params*))
    (SUB3 . (,*eth-default-agg-subnet-weights* . ,*eth-default-aggregate-subnet-params*))))

(check= t (twpp *eth-twp*))

;; ---------------------- PROPERTIES ------------------------------



;;high values
(defdata lows (range integer (0 <= _ <= 1)))

;;low values
(defdata highs (range integer (300 < _ <= 400)))

(defdata-subtype lows nat)
(defdata-subtype highs nat)

;; setting badbehaviour as 0
(defun nth-bad-counters-custom (n)
  (tctrs 0 ;;setting invalid msg deliveries to 0, as penalty is too high
         (nth-lows (+ n 3)) 
         42
         (nth-lows (+ n 4))
         0))
;; for our scenario, meshfailurepenalty must be 0 since it is only incremented
;; when peer leaves.

;; keeping bad behaviors 0 as it drops score too much
(defun nth-good-counters-custom (n)
  (tctrs 0 (nth-highs (+ n 2)) (nth-highs (+ n 3)) (nth-highs (+ n 4)) 0))

(defun nth-counters-custom (n)
  (if (== 0 (mod n 4))
      (nth-bad-counters-custom n)
    (nth-good-counters-custom n)))

(property nth-pt-tctrs-mapp (n :nat)
          :proofs? nil
          (pt-tctrs-mapp (nth-pt-tctrs-map n)))

(defdata-attach tctrs :enumerator nth-counters-custom)


(set-ignore-ok t)
(defun nth-glb-counters-custom (n)
  (declare (irrelevant n))
  (gctrs 0 0 0))

(property nth-p-gctrs-mapp (n :nat)
          :proofs? nil
          (p-gctrs-mapp (nth-p-gctrs-map n)))

(defdata-attach gctrs :enumerator nth-glb-counters-custom)


;; Properties
;; ------------------------------------------------
;; Some interesting properties about ETH-2.0
;; ------------------------------------------------

(defthm eth-twp-valid
  (is-valid-twp *eth-twp*))

(ACL2S-DEFAULTS :SET TESTING-ENABLED t)

;;Property 1
(property (ptc :pt-tctrs-map pcm :p-gctrs-map p :peer top :topic)
          :debug? :all
	  :proofs? nil
          :check-contracts? nil
          :TESTING-TIMEOUT 600
	  :hyps  (^ (member-equal (cons p top) (acl2::alist-keys ptc))
                    (> (lookup-score p (calc-nbr-scores-map ptc pcm *eth-twp*)) 0))
          (> (calcScoreTopic (lookup-tctrs p top ptc) (mget top *eth-twp*))
             0))



;; ((top 'agg)
;;  (p 'p4)
;;  (pcm '((p3449 (:0tag . gctrs)
;;                (:apco . 0)
;;                (:bhvo . 0)
;;                (:ipco . 0))
;;         (p3450 (:0tag . gctrs)
;;                (:apco . 0)
;;                (:bhvo . 0)
;;                (:ipco . 0))
;;         (p3451 (:0tag . gctrs)
;;                (:apco . 0)
;;                (:bhvo . 0)
;;                (:ipco . 0))))
;;  (ptc '(((p4 . agg)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 0)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 1)
;;          (:meshtime . 42))
;;         ((p4 . blocks)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 324)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 330)
;;          (:meshtime . 377))
;;         ((p4 . sub1)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 371)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 377)
;;          (:meshtime . 324))
;;         ((p4 . sub2)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 318)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 324)
;;          (:meshtime . 371))
;;         ((p4 . sub3)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 0)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 1)
;;          (:meshtime . 42))
;;         ((p5 . agg)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 382)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 388)
;;          (:meshtime . 335))
;;         ((p5 . blocks)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 0)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 1)
;;          (:meshtime . 42))
;;         ((p5 . sub1)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 376)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 382)
;;          (:meshtime . 329))
;;         ((p5 . sub2)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 323)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 329)
;;          (:meshtime . 376))
;;         ((p5 . sub3)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 370)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 376)
;;          (:meshtime . 323))
;;         ((p6 . agg)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 352)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 358)
;;          (:meshtime . 305))
;;         ((p6 . blocks)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 399)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 305)
;;          (:meshtime . 352))
;;         ((p6 . sub1)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 346)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 352)
;;          (:meshtime . 399))
;;         ((p6 . sub2)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 0)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 1)
;;          (:meshtime . 42))
;;         ((p6 . sub3)
;;          (:0tag . tctrs)
;;          (:firstmessagedeliveries . 340)
;;          (:invalidmessagedeliveries . 0)
;;          (:meshfailurepenalty . 0)
;;          (:meshmessagedeliveries . 346)
;;          (:meshtime . 393)))))


;;counterexample to property 1
;; even with no app-specific score, we get positive overall score due to other
;; topic scores
(b* ((TOP 'BLOCKS)
     (P 'P1)
     (PCM `((P4 . ,(gctrs 0 0 0))
            (P5 . ,(gctrs 0 0 0))
            (P6 . ,(gctrs 0 0 0))))
     (PTC (nth-pt-tctrs-map 0)))
  (cons 
   (list
    (^ (member-equal (cons p top) (acl2::alist-keys ptc))
                    (> (lookup-score p (calc-nbr-scores-map ptc pcm *eth-twp*)) 0))

    (> (calcScoreTopic (lookup-tctrs p top ptc) (mget top *eth-twp*))
             0)
    
    (calcScoreTopic (lookup-tctrs p 'AGG ptc)
                    (mget 'AGG *ETH-TWP*))
    (calcScoreTopic (lookup-tctrs p 'BLOCKS ptc)
                    (mget 'BLOCKS *ETH-TWP*))
    (calcScoreTopic (lookup-tctrs p 'SUB1 ptc)
                    (mget 'SUB1 *ETH-TWP*))
    (calcScoreTopic (lookup-tctrs p 'SUB2 ptc)
                    (mget 'SUB2 *ETH-TWP*))
    (calcScoreTopic (lookup-tctrs p 'SUB3 ptc)
                    (mget 'SUB3 *ETH-TWP*)))
   (lookup-score p (calc-nbr-scores-map ptc pcm *eth-twp*)))
  )
;; P1, AGG
;; 8.29
;; 22.21, -4.5, 7.80, -25, 7.78



;; We will now generate the list of events that led to the above
;; counter-example for P5


;; Property 2

(b* ((TOP 'AGG)
     (P 'P1)
     (PCM `((P4 . ,(gctrs 0 0 0))
            (P5 . ,(gctrs 0 0 0))
            (P6 . ,(gctrs 0 0 0))))
     (PTC '(((P1 . AGG)
             (:0TAG . TCTRS)
             (:FIRSTMESSAGEDELIVERIES . 194)
             (:INVALIDMESSAGEDELIVERIES . 0)
             (:MESHFAILUREPENALTY . 0)
             (:MESHMESSAGEDELIVERIES . 200)
             (:MESHTIME . 147))
            ((P1 . BLOCKS)
             (:0TAG . TCTRS)
             (:FIRSTMESSAGEDELIVERIES . 100)
             (:INVALIDMESSAGEDELIVERIES . 0)
             (:MESHFAILUREPENALTY . 0)
             (:MESHMESSAGEDELIVERIES . 100)
             (:MESHTIME . 147))
            ((P1 . SUB1)
             (:0TAG . TCTRS)
             (:FIRSTMESSAGEDELIVERIES . 188)
             (:INVALIDMESSAGEDELIVERIES . 0)
             (:MESHFAILUREPENALTY . 0)
             (:MESHMESSAGEDELIVERIES . 194)
             (:MESHTIME . 141))
            ((P1 . SUB2)
             (:0TAG . TCTRS)
             (:FIRSTMESSAGEDELIVERIES . 194)
             (:INVALIDMESSAGEDELIVERIES . 0)
             (:MESHFAILUREPENALTY . 0)
             (:MESHMESSAGEDELIVERIES . 200)
             (:MESHTIME . 147))
            ((P1 . SUB3)
             (:0TAG . TCTRS)
             (:FIRSTMESSAGEDELIVERIES . 182)
             (:INVALIDMESSAGEDELIVERIES . 0)
             (:MESHFAILUREPENALTY . 0)
             (:MESHMESSAGEDELIVERIES . 188)
             (:MESHTIME . 135)))))
  (list
   (calc-nbr-scores-map ptc pcm *eth-twp*)
   (calcScoreTopic (lookup-tctrs p 'AGG ptc)
                   (mget 'AGG *ETH-TWP*))
   (calcScoreTopic (lookup-tctrs p 'BLOCKS ptc)
                   (mget 'BLOCKS *ETH-TWP*))
   (calcScoreTopic (lookup-tctrs p 'SUB1 ptc)
                   (mget 'SUB1 *ETH-TWP*))
   (calcScoreTopic (lookup-tctrs p 'SUB2 ptc)
                   (mget 'SUB2 *ETH-TWP*))
   (calcScoreTopic (lookup-tctrs p 'SUB3 ptc)
                   (mget 'SUB3 *ETH-TWP*))))

;; I need skip-proofs because I can't prove:
;; (thm (=> (natp n) (symbolp (nth-symbol n))))
(skip-proofs
 (definecd emit-meshmsgdeliveries-peer-topic
   (p1 :peer p2 :peer top :topic n :nat) :loev
   (match n
     (0 '())
     (_ (let ((pld (payload-type (nth-symbol n)
                                 (nth-pid-type n)
                                 top
                                 p1)))
          (app (list (list p1 'SND p2 'PAYLOAD pld)
                     (list p2 'RCV p1 'PAYLOAD pld))
               (emit-meshmsgdeliveries-peer-topic p1 p2 top (1- n))))))))

(definecd emit-meshmsgdeliveries-topic (ps :lop p2 :peer top :topic n :nat) :loev
  (match ps
    (() '())
    ((p . rst) (app (emit-meshmsgdeliveries-peer-topic p p2 top n)
                    (emit-meshmsgdeliveries-topic rst p2 top n)))))


;; ps is the list of all peers, except observer. p2 is the observer.
;; ts is list of all topics, n is number of messages sent by peers in ps to p2.
(definecd emit-evnts (ps :lop p2 :peer ts :lot n :nat) :loev
  (match ts
    (() '())
    ((top . rst)
     (app (emit-meshmsgdeliveries-topic ps p2 top n)
          (emit-evnts ps p2 rst n)))))


(emit-evnts '(P1 P2) 'P100 '(SUB2) 3)

;; emit events form peers in ps to all peers in ps2
(definecd emit-evnts-all (ps :lop ps2 :lop ts :lot n :nat) :loev
  (match ps2
    (() '())
    ((p . rst) (app (emit-evnts ps p ts n)
                    (emit-evnts-all ps rst ts n)))))

  
(skip-proofs
(definecd emit-evnts-ptc (ps :lop p2 :peer ts :lot maxT :pos ticks :pos n :nat
                            limiter :bool targetpeer :peer targettop :topic
                            targetn :nat) :loev
                            :skip-tests t
                            :function-contract-hints (("Goal" :in-theory
                                                       (enable hbm-evntp)))
    (app (if limiter
             (app (emit-evnts (remove-equal targetpeer ps) p2 ts n)
                  (emit-evnts ps p2 (remove-equal targettop ts) n)
                  (emit-evnts `(,targetpeer) p2 `(,targettop) targetn)
                  `((,p2 HBM ,maxT)))
           (app (emit-evnts ps p2 ts n)
                `((,p2 HBM ,maxT))))
         (if (<= (- ticks maxT) 0)
             '()
           (emit-evnts-ptc ps p2 ts maxT (- ticks maxT) n limiter targetpeer
                           targettop targetn)))))

;; (app (emit-evnts-ptc '(p1 p2) 'p100 '(BLOCKS AGG) 17 34 2 nil nil nil 1)
;;      (emit-evnts-ptc '(p1 p2) 'p100 '(BLOCKS AGG) 17 34 2 t 'p1 'BLOCKS 1))

(definec construct-mesh (ps :lop ts :lot acc :topic-lop-map) :topic-lop-map
  (match ts
    (() acc)
    ((top . rst)
     (construct-mesh ps rst (mset top ps acc)))))

(definec min-mesh-msgs-for-pos-scores (twpm :twp mm :nat) :nat
  :skip-body-contractsp t
  (match twpm
    (() mm)
    (((top . (wts . params)) . rst)
     (let ((m (params-meshMessageDeliveriesThreshold params)))
       (if (> m mm)
           (min-mesh-msgs-for-pos-scores rst m)
         (min-mesh-msgs-for-pos-scores rst mm))))))

(definec max-hbm-interval (twpm :twp hbmint :non-neg-rational) :non-neg-rational
  (match twpm
    (() hbmint)
    (((top . (wts . params)) . rst)
     (let ((h (params-hbmInterval params)))
       (if (> h hbmint)
           (max-hbm-interval rst h)
         (max-hbm-interval rst hbmint))))))

(definec max-activationwindow (twpm :twp a :non-neg-rational) :non-neg-rational
  (match twpm
    (() a)
    (((top . (wts . params)) . rst)
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

(definec evnts-for-pos-scores (ps :lop p2 :peer ts :lot ticks :pos twpm :twp) :loev
  :skip-body-contractsp t
  (if (null twpm)
      '()
    (app
     (emit-evnts-ptc ps p2 ts (max-hbm-interval twpm 0)
                     (1+ (max-activationwindow twpm 0))
                     (min-mesh-msgs-for-pos-scores twpm 0) nil nil nil 0) ;;first run
     ;;for max activation window to warm up the network
     (emit-evnts-ptc ps p2 ts (max-hbm-interval twpm 0)
                     ticks
                     (min-mesh-msgs-for-pos-scores twpm 0) nil nil nil 0)
     ;;actual run
     )))


;; (len (evnts-for-pos-scores '(P1 P2) 'P100 '(SUB2) 4 *eth-twp*))
;; (b* ((ticks 1000)
;;      (grp (initialize-group-of-meshpeers '(P1 P2 P100)
;; 					 '(P1 P2 P100)
;; 					 '(BLOCKS AGG SUB1 SUB2 SUB3)
;;                                          8))
;;      (evnts (evnts-for-pos-scores '(P1 P2) 'P100 '(BLOCKS AGG SUB1 SUB2 SUB3) ticks *eth-twp*)))
;;   (run-network-gr grp evnts (len evnts) *eth-twp* 42))


(skip-proofs
(definec evnts-for-property1-attack (ps :lop p2 :peer ts :lot ticks :pos twpm :twp
                                        targetpeer :peer targettop :topic) :loev
                                        :body-contracts-hints (("Goal"
                                                                :in-theory
                                                                (enable evntp)))
  (if (null twpm)
      '()
    (b* ((prms (cdr (mget targettop twpm)))
         ((when (null prms)) nil)
         (pmmd (max 0 (- (params-meshMessageDeliveriesThreshold prms) 1))))
      (app
       ;; for warmup + ticks/2 time, run to generate positive scores
       ;; (evnts-for-pos-scores ps p2 ts (1+ (floor ticks 2)) twpm)
       ;; then start throttling targeted (peer . top) mesh deliveries
       (emit-evnts-ptc ps p2 ts (max-hbm-interval twpm 0)
                       ticks
                       (* 5 (min-mesh-msgs-for-pos-scores twpm 0))
                       t ;;attack
                       targetpeer
                       targettop
                       pmmd))))))



;; (b* ((ticks 19)
;;      (grp (initialize-group-of-meshpeers '(P1 P2 P100)
;; 					 '(P1 P2 P100)
;; 					 '(BLOCKS AGG SUB1 SUB2 SUB3)
;;                                          2))
;;      (evnts (evnts-for-property1-attack '(P1 P2) 'P100 '(BLOCKS AGG SUB1 SUB2 SUB3)
;;                                         ticks *eth-twp* 'P1 'SUB2)))
;;   (run-network-gr grp evnts (* 2 (len evnts)) *eth-twp* 42))


;; Functions to check whether property 1 is actually being violated

(defdata lob (listof boolean))
(defdata lops (listof peer-state))

(definec ps-reqs (pss :lops p :peer top :topic) :boolean
  (match pss
    (() t)
    ((ps . rst) (^ (member-equal top (strip-cars *eth-twp*))
		   (member-equal (cons p top) (strip-cars (peer-state-nbr-tctrs ps)))
		   (> (lookup-score p (calc-nbr-scores-map (peer-state-nbr-tctrs ps)
							   (peer-state-nbr-gctrs ps)
							   *eth-twp*))
		      0)
		   (ps-reqs rst p top)))))

;; attacker peer p
(definec scorePropViolation (ps :peer-state p :peer top :topic) :boolean
  :skip-tests t
  :skip-body-contractsp t
  (^ (> (lookup-score p (calc-nbr-scores-map (peer-state-nbr-tctrs ps)
                                              (peer-state-nbr-gctrs ps)
                                              *eth-twp*))
         0)
      (< (calcScoreTopic (lookup-tctrs p top (peer-state-nbr-tctrs ps))
                          (mget top *eth-twp*))
         0)))

;; observer peer p
(skip-proofs
(definec egl->pss (egl :egl p :peer) :lops
  (match egl
    (() '())
    (((evnt . grp) . rst)
     (let ((ps (mget p grp)))
       (cons (if (null ps)
                 (new-peer-state)
               ps)
             (egl->pss rst p)))))))

(definec scorePropViolations (pss :lops p :peer top :topic) :lob
  (match pss
    (() '())
    ((ps . rst) (cons (scorePropViolation ps p top)
                      (scorePropViolations rst p top)))))

(definec scorePropViolationTopic (ps :peer-state p :peer top :topic) :all
  :skip-tests t
  :skip-body-contractsp t
  (list (calcScoreTopic (lookup-tctrs p 'BLOCKS (peer-state-nbr-tctrs ps))
                        (mget top *eth-twp*))
        (calcScoreTopic (lookup-tctrs p 'AGG (peer-state-nbr-tctrs ps))
                        (mget top *eth-twp*))
        (calcScoreTopic (lookup-tctrs p 'SUB1 (peer-state-nbr-tctrs ps))
                        (mget top *eth-twp*))
        (calcScoreTopic (lookup-tctrs p 'SUB2 (peer-state-nbr-tctrs ps))
                        (mget top *eth-twp*))
        (calcScoreTopic (lookup-tctrs p 'SUB3 (peer-state-nbr-tctrs ps))
                        (mget top *eth-twp*))
        (lookup-score p (calc-nbr-scores-map (peer-state-nbr-tctrs ps)
                                              (peer-state-nbr-gctrs ps)
                                              *eth-twp*))))


(definec scorePropViolationTopics (pss :lops p :peer top :topic) :all
  (match pss
    (() '())
    ((ps . rst) (cons (scorePropViolationTopic ps p top)
                      (scorePropViolationTopics rst p top)))))











;; ------------------------------------------------------------------------------------
;; Attack for Property 1, with a single target peer. T in trace shows a
;; property violation
;; ------------------------------------------------------------------------------------



;; (b* ((ticks 100)
;;      (grp (initialize-group-of-meshpeers '(P1 P2 P100)
;; 					 '(P1 P2 P100)
;; 					 '(BLOCKS AGG SUB1 SUB2 SUB3)
;;                                          2))
;;      (evnts (evnts-for-property1-attack '(P1 P2) 'P100 '(BLOCKS AGG SUB1 SUB2 SUB3)
;;                                         ticks *eth-twp* 'P1 'SUB2)))
;;   (scorePropViolationTopics (egl->pss (run-network grp evnts (* 10 (len evnts))
;;                                               *eth-twp* 42)
;;                                  'P100)
;;                        'P1
;;                        'SUB2))



;; (b* ((ticks 20)
;;      (grp (initialize-group-of-meshpeers '(P1 P2 P100)
;; 					 '(P1 P2 P100)
;; 					 '(BLOCKS AGG SUB1 SUB2 SUB3)
;;                                          2))
;;      (evnts (evnts-for-property1-attack '(P1 P2) 'P100 '(BLOCKS AGG SUB1 SUB2 SUB3)
;;                                         ticks *eth-twp* 'P1 'AGG)))
;;   (scorePropViolationTopics (egl->pss (run-network grp evnts (* 10 (len evnts))
;;                                               *eth-twp* 42)
;;                                  'P100)
;;                        'P1
;;                        'AGG))



;; Shows T, meaning property violated in trace of booleans
(b* ((ticks 100)
     (grp (initialize-group-of-meshpeers '(P1 P2 P3)
					 '(P1 P2 P3)
					 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                         8))
     (evnts (take 10000 (evnts-for-property1-attack '(P1) 'P3 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                    ticks *eth-twp* 'P1 'AGG))))
  (scorePropViolations (egl->pss (run-network grp evnts (* 10 (len evnts))
                                              *eth-twp* 42)
                                 'P3)
                       'P1
                       'AGG))


;; Careful : processing 20k events takes 17mins on my machine, very high
;; compared to 10k events.


;; 10 peers, mssgs among themselves, 10k evnts, 68.94 seconds realtime, 68.40 seconds runtime
(time$
 (b* ((ticks 100)
      (d (mget :d (cdr (mget 'BLOCKS *eth-twp*))))
      (ps (gen-peers 1 10))
      (grp (initialize-group-of-meshpeers ps
                                          ps
                                          '(BLOCKS AGG SUB1 SUB2 SUB3)
                                          d))
      (evnts (take 10000 (evnts-for-property1-attack '(P1) 'P3 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                     ticks *eth-twp* 'P1 'AGG))))
   (scorePropViolations (egl->pss (run-network grp evnts (* 10 (len evnts))
                                               *eth-twp* 42)
                                  'P3)
                        'P1
                        'AGG))
 )


;; 100 peers, mssgs among others, 100k evnts, 1797.86 seconds realtime, 1783.72
;; seconds runtime
;; 30 mins
;;  2312.45 seconds realtime, 2269.70 seconds runtime
(time$
 (b* ((ticks 100)
      (d (mget :d (cdr (mget 'BLOCKS *eth-twp*))))
      (ps (gen-peers 1 100))
      (grp (initialize-group-of-meshpeers ps
                                          ps
                                          '(BLOCKS AGG SUB1 SUB2 SUB3)
                                          d))
      (evnts (take 10000 (evnts-for-property1-attack '(P1) 'P100 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                     ticks *eth-twp* 'P1 'AGG))))
   (scorePropViolations (egl->pss (run-network grp evnts (* 10 (len evnts))
                                               *eth-twp* 42)
                                  'P100)
                        'P1
                        'AGG))
 )


;; 1000 peers, mssgs among themselves, 10k evnts, 58 mins
;; 3485.58 seconds realtime, 3455.27 seconds runtime
(time$
 (b* ((ticks 100)
      (d (mget :d (cdr (mget 'BLOCKS *eth-twp*))))
      (ps (gen-peers 1 1000))
      (grp (initialize-group-of-meshpeers ps
                                          ps
                                          '(BLOCKS AGG SUB1 SUB2 SUB3)
                                          d))
      (evnts (take 10000 (evnts-for-property1-attack '(P1) 'P1000 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                     ticks *eth-twp* 'P1 'AGG))))
   (scorePropViolations (egl->pss (run-network grp evnts (* 10 (len evnts))
                                               *eth-twp* 42)
                                  'P1000)
                        'P1
                        'AGG))
 )




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
(definecd eth-attack-violations (gr :group evnts :loev p1 :peer p2 :peer top :topic i :nat twpm :twp s :nat acc :lob) :lob
    :ic (is-valid-twp twpm)
    :skip-tests t
    :body-contracts-strictp nil
    (if (v (zp i)
           (endp evnts))
        acc
      (b* (((mv k s) (defdata::genrandom-seed
                       (1- (expt 2 31))
                       (mod s (expt 2 31))))
           (actor (caar evnts))
           (actor-state (lookup-state actor gr))
           ((res4 next-actor-state evs) (transition actor actor-state (car evnts)
                                                    twpm k))
           (next-actor-events (network-propagator evs nil))
           (newgrp (mset actor next-actor-state gr))
	   (res (scorePropViolation (mget p1 newgrp) p2 top)))
              (eth-attack-violations
               newgrp
               ;;mix generated events with remaining events
               (app
		(cdr evnts)
		next-actor-events
		)
	       p1
               p2
	       top
               (1- i)
               twpm
               s
	       (cons res acc)))))
)

; 7.68 seconds realtime, 7.62 seconds runtime
; (2,930,243,792 bytes allocated).
(time$
 (b* ((ticks 100)
      (n 10)
      (d (mget :d (cdr (mget 'BLOCKS *eth-twp*))))
      (ps (gen-peers 1 n))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   (gen-circular-topo n d)
                   (topics)))
      (evnts (take 10000 (evnts-for-property1-attack '(P1) 'P10 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                     ticks *eth-twp* 'P1
                                                     'AGG))))
    (eth-attack-violations grp evnts 'P10 'P1 'AGG (* 10 (len evnts))
                           *eth-twp* 42 nil)))


; 65.49 seconds realtime, 64.31 seconds runtime
; (41,323,921,952 bytes allocated).
(time$
 (b* ((ticks 100)
      (n 100)
      (d (mget :d (cdr (mget 'BLOCKS *eth-twp*))))
      (ps (gen-peers 1 n))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   (gen-circular-topo n d)
                   (topics)))
      (evnts (take 10000 (evnts-for-property1-attack '(P1) 'P100 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                     ticks *eth-twp* 'P1
                                                     'AGG))))
    (eth-attack-violations grp evnts 'P100 'P1 'AGG (* 10 (len evnts))
                           *eth-twp* 42 nil)))


; 69.64 seconds realtime, 67.90 seconds runtime
; (42,245,425,632 bytes allocated).
(time$
 (b* ((ticks 100)
      (n 1000)
      (d (mget :d (cdr (mget 'BLOCKS *eth-twp*))))
      (ps (gen-peers 1 n))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   (gen-circular-topo n d)
                   (topics)))
      (evnts (take 10000 (evnts-for-property1-attack '(P1) 'P1000 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                     ticks *eth-twp* 'P1
                                                     'AGG))))
    (eth-attack-violations grp evnts 'P1000 'P1 'AGG (* 10 (len evnts))
                           *eth-twp* 42 nil)))



;; attack on goerli network
;; 9.35 mins
;; ; 561.46 seconds realtime, 513.43 seconds runtime
;; (1,068,677,623,184 bytes allocated).
(time$
 (b* ((ticks 100)
      (d (mget :d (cdr (mget 'BLOCKS *eth-twp*))))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
=                   *goerli*
                   '(BLOCKS AGG SUB1 SUB2 SUB3)))
      (evnts (grab 10000 (evnts-for-property1-attack '(P222) 'P834 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                     ticks *eth-twp* 'P222 'AGG))))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts 'P834 'P222 'AGG (* 10 (len evnts))
                          *eth-twp* 42 nil)))



;; attack on rinkeby network
; 1945.18 seconds realtime, 1848.42 seconds runtime
;; 32 mins
; (2,886,666,214,832 bytes allocated).
(time$
 (b* ((ticks 100)
      (d (mget :d (cdr (mget 'BLOCKS *eth-twp*))))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   *rinkeby*
                   '(BLOCKS AGG SUB1 SUB2 SUB3)))
      (evnts (grab 10000 (evnts-for-property1-attack '(P256) 'P436 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                     ticks *eth-twp* 'P256 'AGG))))
   ;; P256 is attacker, P436 is observer who records violations
   (eth-attack-violations grp evnts 'P436 'P256 'AGG (* 10 (len evnts))
                          *eth-twp* 42 nil)))


;; attack on ropsten network
; 474.83 seconds realtime, 435.23 seconds runtime
; 8 mins
; (1,141,741,823,040 bytes allocated).
(time$
 (b* ((ticks 100)
      (d (mget :d (cdr (mget 'BLOCKS *eth-twp*))))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   *ropsten*
                   '(BLOCKS AGG SUB1 SUB2 SUB3)))
      (evnts (grab 10000 (evnts-for-property1-attack '(P256) 'P436 '(BLOCKS AGG SUB1 SUB2 SUB3)
                                                     ticks *eth-twp* 'P256 'AGG))))
   ;; P256 is attacker, P436 is observer who records violations
   (eth-attack-violations grp evnts 'P436 'P256 'AGG (* 10 (len evnts))
                          *eth-twp* 42 nil)))


;; ------------------------------------------------------------------------------------
;; Counterexamples for Property 2
;; ------------------------------------------------------------------------------------


(defdata-attach tctrs :enumerator nth-good-counters-custom)

(property (ptc :pt-tctrs-map
	       pglb :p-gctrs-map
	       p :peer
	       top :topic
	       delta-p3 :non-neg-rational
	       delta-p3b :non-neg-rational
	       delta-p4 :non-neg-rational
	       delta-p6 :non-neg-rational
	       delta-p7 :non-neg-rational)
  :proofs? nil
  :testing-timeout 600
  :CHECK-CONTRACTS? nil
  :hyps (^ (member-equal top (strip-cars *eth-twp*))
	   (member-equal (cons p top) (strip-cars ptc))
	   ;; Require glb indexed by p in pglb to not be empty and thus not return nil
           (member-equal p (strip-cars pglb))
	   ;; Require that at least one delta is non-zero
	   (> (+ delta-p3 delta-p3b delta-p4 delta-p6 delta-p7) 0))
  ;; Define the new ptc using our deltas
  (b* ((tc (lookup-tctrs p top ptc))
       (glb (lookup-gctrs p pglb))
       (new-tc (update-meshMessageDeliveries
		  tc
		  (- (tctrs-meshMessageDeliveries tc) delta-p3)))
       (new-ptc (put-assoc-equal `(,p . ,top) new-tc ptc)))
    (> (lookup-score p (calc-nbr-scores-map ptc pglb *eth-twp*))
       (lookup-score p (calc-nbr-scores-map new-ptc pglb *eth-twp*)))))

;;effect due to purturbations alone : -751/60 = -12.52
(b* ((DELTA-P7 0)
     (DELTA-P6 1)
     (DELTA-P4 0)
     (DELTA-P3B 1)
     (DELTA-P3 1)
     (TOP 'SUB2)
     (P 'P9)
     (PGLB '((P9 0 0 0) (P10 0 0 0) (P11 0 0 0)))
     (PTC '(((P9 . BLOCKS)
             (:0TAG . TCTRS)
             (:FIRSTMESSAGEDELIVERIES . 170)
             (:INVALIDMESSAGEDELIVERIES . 0)
             (:MESHFAILUREPENALTY . 0)
             (:MESHMESSAGEDELIVERIES . 176)
             (:MESHTIME . 123))
            ((P9 . AGG)
             (:0TAG . TCTRS)
             (:FIRSTMESSAGEDELIVERIES . 117)
             (:INVALIDMESSAGEDELIVERIES . 0)
             (:MESHFAILUREPENALTY . 0)
             (:MESHMESSAGEDELIVERIES . 123)
             (:MESHTIME . 170))
            ((P9 . SUB1)
             (:0TAG . TCTRS)
             (:FIRSTMESSAGEDELIVERIES . 164)
             (:INVALIDMESSAGEDELIVERIES . 0)
             (:MESHFAILUREPENALTY . 0)
             (:MESHMESSAGEDELIVERIES . 170)
             (:MESHTIME . 117))
            ((P9 . SUB2)
             (:0TAG . TCTRS)
             (:FIRSTMESSAGEDELIVERIES . 111)
             (:INVALIDMESSAGEDELIVERIES . 0)
             (:MESHFAILUREPENALTY . 0)
             (:MESHMESSAGEDELIVERIES . 117)
             (:MESHTIME . 164))
            ((P9 . SUB3)
             (:0TAG . TCTRS)
             (:FIRSTMESSAGEDELIVERIES . 158)
             (:INVALIDMESSAGEDELIVERIES . 0)
             (:MESHFAILUREPENALTY . 0)
             (:MESHMESSAGEDELIVERIES . 164)
             (:MESHTIME . 111))))
     (tc (lookup-tctrs p top ptc))
     (glb (lookup-gctrs p pglb))
     (new-tc (update-invalidMessageDeliveries
              (update-meshFailurePenalty
               (update-meshMessageDeliveries
                tc
                (+ (tctrs-meshMessageDeliveries tc) delta-p3))
               (+ (tctrs-meshFailurePenalty tc) delta-p3b))
              (+ (tctrs-invalidMessageDeliveries tc) delta-p4)))
     (new-ptc (put-assoc-equal `(,p . ,top) new-tc ptc))
     (new-glb-counters `(,(first glb)
                         ,(+ (second glb) delta-p6)
                         ,(+ (third glb) delta-p7)))
     (new-pglb (put-assoc-equal p new-glb-counters pglb)))
  (list (calcScoreTopic (lookup-tctrs p 'BLOCKS ptc)
                        (cdr (assoc-equal 'BLOCKS *ETH-TWP*)))
        (calcScoreTopic (lookup-tctrs p 'AGG ptc)
                        (cdr (assoc-equal 'AGG *ETH-TWP*)))
        (calcScoreTopic (lookup-tctrs p 'SUB1 ptc)
                        (cdr (assoc-equal 'SUB1 *ETH-TWP*)))
        (calcScoreTopic (lookup-tctrs p 'SUB2 ptc)
                        (cdr (assoc-equal 'SUB2 *ETH-TWP*)))
        (calcScoreTopic (lookup-tctrs p 'SUB3 ptc)
                        (cdr (assoc-equal 'SUB3 *ETH-TWP*)))
        (calcScoreTopic (lookup-tctrs p 'SUB2 new-ptc)
                        (cdr (assoc-equal 'SUB2 *ETH-TWP*)))
        (lookup-score p (calc-nbr-scores-map ptc pglb *eth-twp*))
        (lookup-score p (calc-nbr-scores-map new-ptc new-pglb *eth-twp*))))

;; 21.59 10.24 7.77 7.82 7.76 -4.70

;; (67463/3125 5121/500
;;             194159/25000 48857/6250 193997/25000
;;             -176233/37500 818/25 818/25)



;; ------------------------------------------------------------------------------------
;; Counterexamples for Property 3
;; ------------------------------------------------------------------------------------

(property
   (imd mmd mt fmd mfp p :non-neg-rational wtpm :wp)
   :check-contracts? nil
   :proofs? nil
   (=> (^ (== wtpm (cdr (assoc-equal 'BLOCKS *ETH-TWP*)))
          (>= (params-meshMessageDeliveriesCap (cdr wtpm))
              (params-meshMessageDeliveriesThreshold (cdr wtpm)))
          (> mt (params-activationWindow (cdr wtpm))))
       (>= (calcScoreTopic (tctrs imd mmd  (+ p mt) fmd mfp) wtpm)
           (calcScoreTopic (tctrs imd mmd  mt fmd mfp) wtpm))))

(property
   (imd mmd mt fmd mfp p :non-neg-rational wtpm :wp)
   :check-contracts? nil
   :proofs? nil
   (=> (^ (== wtpm (cdr (assoc-equal 'AGG *ETH-TWP*)))
          (>= (params-meshMessageDeliveriesCap (cdr wtpm))
              (params-meshMessageDeliveriesThreshold (cdr wtpm)))
          (> mt (params-activationWindow (cdr wtpm))))
       (>= (calcScoreTopic (tctrs imd mmd  (+ p mt) fmd mfp) wtpm)
           (calcScoreTopic (tctrs imd mmd  mt fmd mfp) wtpm))))

(property
   (imd mmd mt fmd mfp p :non-neg-rational wtpm :wp)
   :check-contracts? nil
   :proofs? nil
   (=> (^ (== wtpm (cdr (assoc-equal 'SUB2 *ETH-TWP*)))
          (>= (params-meshMessageDeliveriesCap (cdr wtpm))
              (params-meshMessageDeliveriesThreshold (cdr wtpm)))
          (> mt (params-activationWindow (cdr wtpm))))
       (>= (calcScoreTopic (tctrs imd mmd  (+ p mt) fmd mfp) wtpm)
           (calcScoreTopic (tctrs imd mmd  mt fmd mfp) wtpm))))


;; Max's proof of prop3, GENERALLY (i.e. not just for Eth.)
(definec tctrs-same-except-good-stuff-incr (tctrs0 tctrs1 :tctrs) :bool
  (^ (= (tctrs-invalidMessageDeliveries tctrs0)
	(tctrs-invalidMessageDeliveries tctrs1))
     (<= (tctrs-meshMessageDeliveries tctrs0)
	 (tctrs-meshMessageDeliveries tctrs1))
     (<= (tctrs-meshTime tctrs0)
	 (tctrs-meshTime tctrs1))
     (<= (tctrs-firstMessageDeliveries tctrs0)
	 (tctrs-firstMessageDeliveries tctrs1))
     (= (tctrs-meshFailurePenalty tctrs0)
	(tctrs-meshFailurePenalty tctrs1))))

(property p1-monotone (tctrs0 tctrs1 :tctrs wtpm :wp)
  :h (^ (tctrs-same-except-good-stuff-incr tctrs0 tctrs1)
	(> (tctrs-meshTime tctrs0)
	   (params-activationWindow (cdr wtpm)))
	(>= (params-meshMessageDeliveriesCap (cdr wtpm))
	    (params-meshMessageDeliveriesThreshold (cdr wtpm))))
  (<= (* (mget :w1 (car wtpm))
           (calcp1 (tctrs-meshtime tctrs0)
                   (params-meshtimequantum (cdr wtpm))
                   (params-timequantainmeshcap (cdr wtpm))))
      (* (mget :w1 (car wtpm))
           (calcp1 (tctrs-meshtime tctrs1)
                   (params-meshtimequantum (cdr wtpm))
                   (params-timequantainmeshcap (cdr wtpm)))))
  :hints (("Goal" :use
	   ((:instance calcp1-definition-rule
		       (meshTime (tctrs-meshtime tctrs0))
		       (meshTimeQuantum (params-meshtimequantum (cdr wtpm)))
		       (timeQInMeshCap (params-timequantainmeshcap (cdr wtpm))))
	    (:instance calcp1-definition-rule
		       (meshTime (tctrs-meshtime tctrs1))
		       (meshTimeQuantum (params-meshtimequantum (cdr wtpm)))
		       (timeQInMeshCap (params-timequantainmeshcap (cdr wtpm))))))))

(property p2-monotone (tctrs0 tctrs1 :tctrs wtpm :wp)
  :h (^ (tctrs-same-except-good-stuff-incr tctrs0 tctrs1)
	(> (tctrs-meshTime tctrs0)
	   (params-activationWindow (cdr wtpm)))
	(>= (params-meshMessageDeliveriesCap (cdr wtpm))
	    (params-meshMessageDeliveriesThreshold (cdr wtpm))))
  (<= (* (mget :w2 (car wtpm))
	 (calcP2 (tctrs-firstMessageDeliveries tctrs0) (params-p2cap (cdr wtpm))))
      (* (mget :w2 (car wtpm))
	 (calcP2 (tctrs-firstMessageDeliveries tctrs1) (params-p2cap (cdr wtpm)))))
  :hints (("Goal" :use
	   ((:instance calcP2-definition-rule
		       (firstMessageDeliveries (tctrs-firstMessageDeliveries tctrs0))
		       (p2cap (params-p2cap (cdr wtpm))))
	    (:instance calcP2-definition-rule
		       (firstMessageDeliveries (tctrs-firstMessageDeliveries tctrs1))
		       (p2cap (params-p2cap (cdr wtpm))))))))

(property p3-monotone (tctrs0 tctrs1 :tctrs wtpm :wp)
  :h (^ (tctrs-same-except-good-stuff-incr tctrs0 tctrs1)
	(> (tctrs-meshTime tctrs0)
	   (params-activationWindow (cdr wtpm)))
	(>= (params-meshMessageDeliveriesCap (cdr wtpm))
	    (params-meshMessageDeliveriesThreshold (cdr wtpm))))
  (<= (* (mget :w3 (car wtpm))
	 (calcP3 (tctrs-meshTime tctrs0)
		 (params-activationWindow (cdr wtpm)) 
		 (tctrs-meshMessageDeliveries tctrs0)
		 (params-meshMessageDeliveriesCap (cdr wtpm))
		 (params-meshMessageDeliveriesThreshold (cdr wtpm))))
      (* (mget :w3 (car wtpm))
	 (calcP3 (tctrs-meshTime tctrs1)
		 (params-activationWindow (cdr wtpm)) 
		 (tctrs-meshMessageDeliveries tctrs1)
		 (params-meshMessageDeliveriesCap (cdr wtpm))
		 (params-meshMessageDeliveriesThreshold (cdr wtpm)))))
  :hints (("Goal" :use
	   ((:instance calcP3-definition-rule
		       (meshTime (tctrs-meshTime tctrs0))
		       (activationWindow (params-activationWindow (cdr wtpm)))
		       (meshMessageDeliveries (tctrs-meshMessageDeliveries tctrs0))
		       (meshMessageDeliveriesCap (params-meshMessageDeliveriesCap (cdr wtpm)))
		       (meshMessageDeliveriesThreshold
			(params-meshMessageDeliveriesThreshold (cdr wtpm))))
	    (:instance calcP3-definition-rule
		       (meshTime (tctrs-meshTime tctrs1))
		       (activationWindow (params-activationWindow (cdr wtpm)))
		       (meshMessageDeliveries (tctrs-meshMessageDeliveries tctrs1))
		       (meshMessageDeliveriesCap (params-meshMessageDeliveriesCap (cdr wtpm)))
		       (meshMessageDeliveriesThreshold
			(params-meshMessageDeliveriesThreshold (cdr wtpm))))
	    (:instance
	     calc-deficit-definition-rule
	     (meshmessagedeliveries (tctrs-meshmessagedeliveries tctrs0))
	     (meshmessagedeliveriescap (params-meshmessagedeliveriescap (cdr wtpm)))
	     (meshmessagedeliveriesthreshold
	      (params-meshmessagedeliveriesthreshold (cdr wtpm))))
	    (:instance
	     calc-deficit-definition-rule
	     (meshmessagedeliveries (tctrs-meshmessagedeliveries tctrs1))
	     (meshmessagedeliveriescap (params-meshmessagedeliveriescap (cdr wtpm)))
	     (meshmessagedeliveriesthreshold
	      (params-meshmessagedeliveriesthreshold (cdr wtpm))))))))

(property p3b-monotone (tctrs0 tctrs1 :tctrs wtpm :wp)
  :h (^ (tctrs-same-except-good-stuff-incr tctrs0 tctrs1)
	(> (tctrs-meshTime tctrs0)
	   (params-activationWindow (cdr wtpm)))
	(>= (params-meshMessageDeliveriesCap (cdr wtpm))
	    (params-meshMessageDeliveriesThreshold (cdr wtpm))))
  (<= (* (mget :w3b (car wtpm))
	 (calcP3b (tctrs-meshTime tctrs0)
		  (params-activationWindow (cdr wtpm))
		  (tctrs-meshFailurePenalty tctrs0)
		  (tctrs-meshMessageDeliveries tctrs0)
		  (params-meshMessageDeliveriesCap (cdr wtpm))
		  (params-meshMessageDeliveriesThreshold (cdr wtpm))))
      (* (mget :w3b (car wtpm))
	 (calcP3b (tctrs-meshTime tctrs1)
		  (params-activationWindow (cdr wtpm))
		  (tctrs-meshFailurePenalty tctrs1)
		  (tctrs-meshMessageDeliveries tctrs1)
		  (params-meshMessageDeliveriesCap (cdr wtpm))
		  (params-meshMessageDeliveriesThreshold (cdr wtpm)))))
  :hints (("Goal" :use
	   ((:instance calcP3b-definition-rule
		       (meshTime (tctrs-meshTime tctrs0))
		       (activationWindow (params-activationWindow (cdr wtpm)))
		       (meshFailurePenalty (tctrs-meshFailurePenalty tctrs0))
		       (meshMessageDeliveries (tctrs-meshMessageDeliveries tctrs0))
		       (meshMessageDeliveriesCap (params-meshMessageDeliveriesCap (cdr wtpm)))
		       (meshMessageDeliveriesThreshold
			(params-meshMessageDeliveriesThreshold (cdr wtpm))))
	    (:instance calcP3b-definition-rule
		       (meshTime (tctrs-meshTime tctrs1))
		       (activationWindow (params-activationWindow (cdr wtpm)))
		       (meshFailurePenalty (tctrs-meshFailurePenalty tctrs1))
		       (meshMessageDeliveries (tctrs-meshMessageDeliveries tctrs1))
		       (meshMessageDeliveriesCap (params-meshMessageDeliveriesCap (cdr wtpm)))
		       (meshMessageDeliveriesThreshold
			(params-meshMessageDeliveriesThreshold (cdr wtpm))))
	    (:instance
	     calc-deficit-definition-rule
	     (meshmessagedeliveries (tctrs-meshmessagedeliveries tctrs0))
	     (meshmessagedeliveriescap (params-meshmessagedeliveriescap (cdr wtpm)))
	     (meshmessagedeliveriesthreshold
	      (params-meshmessagedeliveriesthreshold (cdr wtpm))))
	    (:instance
	     calc-deficit-definition-rule
	     (meshmessagedeliveries (tctrs-meshmessagedeliveries tctrs1))
	     (meshmessagedeliveriescap (params-meshmessagedeliveriescap (cdr wtpm)))
	     (meshmessagedeliveriesthreshold
	      (params-meshmessagedeliveriesthreshold (cdr wtpm))))))))

(property p4-monotone (tctrs0 tctrs1 :tctrs wtpm :wp)
  :h (^ (tctrs-same-except-good-stuff-incr tctrs0 tctrs1)
	(> (tctrs-meshTime tctrs0)
	   (params-activationWindow (cdr wtpm)))
	(>= (params-meshMessageDeliveriesCap (cdr wtpm))
	    (params-meshMessageDeliveriesThreshold (cdr wtpm))))
  (<= (* (mget :w4 (car wtpm))
	 (calcP4 (tctrs-invalidMessageDeliveries tctrs0)))
      (* (mget :w4 (car wtpm))
	 (calcP4 (tctrs-invalidMessageDeliveries tctrs1)))))

(property P1+P2+P3+P3b+P4-monotone (p1 p2 p3 p3b p4 p1a p2a p3a p3ba p4a :rational)
  :h (^ (<= p1 p1a)
	(<= p2 p2a)
	(<= p3 p3a)
	(<= p3b p3ba)
	(<= p4 p4a))
  (<= (+ p1 p2 p3 p3b p4)
      (+ p1a p2a p3a p3ba p4a)))

(property A<=B->AC<=BC (A B :rational C :non-neg-rational)
  :h (<= A B)
  (<= (* C A) (* C B)))

(defthm prop3
 (=> (^ (tctrsp tctrs0)
        (tctrsp tctrs1)
        (wpp wtpm)
        (tctrs-same-except-good-stuff-incr tctrs0 tctrs1)
        (> (tctrs-meshtime tctrs0)
           (params-activationwindow (cdr wtpm)))
        (>= (params-meshmessagedeliveriescap (cdr wtpm))
            (params-meshmessagedeliveriesthreshold (cdr wtpm))))
     (<= (calcscoretopic tctrs0 wtpm)
         (calcscoretopic tctrs1 wtpm)))
 :instructions
 ((:use (:instance calcscoretopic-definition-rule
                   (tctrs tctrs0)))
  :pro
  (:claim
   (equal
       (calcscoretopic tctrs0 wtpm)
       (let ((weights (car wtpm)) (tctrs tctrs0))
         (let ((params (cdr wtpm)))
           (* (params-topicweight params)
              (+ (* (mget :w1 weights)
                    (calcp1 (tctrs-meshtime tctrs)
                            (params-meshtimequantum params)
                            (params-timequantainmeshcap params)))
                 (* (mget :w2 weights)
                    (calcp2 (tctrs-firstmessagedeliveries tctrs)
                            (params-p2cap params)))
                 (* (mget :w3 weights)
                    (calcp3 (tctrs-meshtime tctrs)
                            (params-activationwindow params)
                            (tctrs-meshmessagedeliveries tctrs)
                            (params-meshmessagedeliveriescap params)
                            (params-meshmessagedeliveriesthreshold params)))
                 (* (mget :w3b weights)
                    (calcp3b (tctrs-meshtime tctrs)
                             (params-activationwindow params)
                             (tctrs-meshfailurepenalty tctrs)
                             (tctrs-meshmessagedeliveries tctrs)
                             (params-meshmessagedeliveriescap params)
                             (params-meshmessagedeliveriesthreshold params)))
                 (* (mget :w4 weights)
                    (calcp4 (tctrs-invalidmessagedeliveries tctrs)))))))))
  (:drop 1)
  (:use (:instance calcscoretopic-definition-rule
                   (tctrs tctrs1)))
  :pro
  (:claim
   (equal
       (calcscoretopic tctrs1 wtpm)
       (let ((weights (car wtpm)) (tctrs tctrs1))
         (let ((params (cdr wtpm)))
           (* (params-topicweight params)
              (+ (* (mget :w1 weights)
                    (calcp1 (tctrs-meshtime tctrs)
                            (params-meshtimequantum params)
                            (params-timequantainmeshcap params)))
                 (* (mget :w2 weights)
                    (calcp2 (tctrs-firstmessagedeliveries tctrs)
                            (params-p2cap params)))
                 (* (mget :w3 weights)
                    (calcp3 (tctrs-meshtime tctrs)
                            (params-activationwindow params)
                            (tctrs-meshmessagedeliveries tctrs)
                            (params-meshmessagedeliveriescap params)
                            (params-meshmessagedeliveriesthreshold params)))
                 (* (mget :w3b weights)
                    (calcp3b (tctrs-meshtime tctrs)
                             (params-activationwindow params)
                             (tctrs-meshfailurepenalty tctrs)
                             (tctrs-meshmessagedeliveries tctrs)
                             (params-meshmessagedeliveriescap params)
                             (params-meshmessagedeliveriesthreshold params)))
                 (* (mget :w4 weights)
                    (calcp4 (tctrs-invalidmessagedeliveries tctrs)))))))))
  (:drop 1)
  (:use (:instance p1-monotone))
  :pro
  (:claim (<= (* (mget :w1 (car wtpm))
                 (calcp1 (tctrs-meshtime tctrs0)
                         (params-meshtimequantum (cdr wtpm))
                         (params-timequantainmeshcap (cdr wtpm))))
              (* (mget :w1 (car wtpm))
                 (calcp1 (tctrs-meshtime tctrs1)
                         (params-meshtimequantum (cdr wtpm))
                         (params-timequantainmeshcap (cdr wtpm))))))
  (:drop 1)
  (:use (:instance p2-monotone))
  :pro
  (:claim (<= (* (mget :w2 (car wtpm))
                 (calcp2 (tctrs-firstmessagedeliveries tctrs0)
                         (params-p2cap (cdr wtpm))))
              (* (mget :w2 (car wtpm))
                 (calcp2 (tctrs-firstmessagedeliveries tctrs1)
                         (params-p2cap (cdr wtpm))))))
  (:drop 1)
  (:use (:instance p3-monotone))
  :pro
  (:claim
       (<= (* (mget :w3 (car wtpm))
              (calcp3 (tctrs-meshtime tctrs0)
                      (params-activationwindow (cdr wtpm))
                      (tctrs-meshmessagedeliveries tctrs0)
                      (params-meshmessagedeliveriescap (cdr wtpm))
                      (params-meshmessagedeliveriesthreshold (cdr wtpm))))
           (* (mget :w3 (car wtpm))
              (calcp3 (tctrs-meshtime tctrs1)
                      (params-activationwindow (cdr wtpm))
                      (tctrs-meshmessagedeliveries tctrs1)
                      (params-meshmessagedeliveriescap (cdr wtpm))
                      (params-meshmessagedeliveriesthreshold (cdr wtpm))))))
  (:drop 1)
  (:use (:instance p3b-monotone))
  :pro
  (:claim
       (<= (* (mget :w3b (car wtpm))
              (calcp3b (tctrs-meshtime tctrs0)
                       (params-activationwindow (cdr wtpm))
                       (tctrs-meshfailurepenalty tctrs0)
                       (tctrs-meshmessagedeliveries tctrs0)
                       (params-meshmessagedeliveriescap (cdr wtpm))
                       (params-meshmessagedeliveriesthreshold (cdr wtpm))))
           (* (mget :w3b (car wtpm))
              (calcp3b (tctrs-meshtime tctrs1)
                       (params-activationwindow (cdr wtpm))
                       (tctrs-meshfailurepenalty tctrs1)
                       (tctrs-meshmessagedeliveries tctrs1)
                       (params-meshmessagedeliveriescap (cdr wtpm))
                       (params-meshmessagedeliveriesthreshold (cdr wtpm))))))
  (:drop 1)
  (:use (:instance p4-monotone))
  :pro
  (:claim (<= (* (mget :w4 (car wtpm))
                 (calcp4 (tctrs-invalidmessagedeliveries tctrs0)))
              (* (mget :w4 (car wtpm))
                 (calcp4 (tctrs-invalidmessagedeliveries tctrs1)))))
  (:drop 1)
  (:use
   (:instance
      p1+p2+p3+p3b+p4-monotone
      (p1 (* (mget :w1 (car wtpm))
             (calcp1 (tctrs-meshtime tctrs0)
                     (params-meshtimequantum (cdr wtpm))
                     (params-timequantainmeshcap (cdr wtpm)))))
      (p1a (* (mget :w1 (car wtpm))
              (calcp1 (tctrs-meshtime tctrs1)
                      (params-meshtimequantum (cdr wtpm))
                      (params-timequantainmeshcap (cdr wtpm)))))
      (p2 (* (mget :w2 (car wtpm))
             (calcp2 (tctrs-firstmessagedeliveries tctrs0)
                     (params-p2cap (cdr wtpm)))))
      (p2a (* (mget :w2 (car wtpm))
              (calcp2 (tctrs-firstmessagedeliveries tctrs1)
                      (params-p2cap (cdr wtpm)))))
      (p3 (* (mget :w3 (car wtpm))
             (calcp3 (tctrs-meshtime tctrs0)
                     (params-activationwindow (cdr wtpm))
                     (tctrs-meshmessagedeliveries tctrs0)
                     (params-meshmessagedeliveriescap (cdr wtpm))
                     (params-meshmessagedeliveriesthreshold (cdr wtpm)))))
      (p3a (* (mget :w3 (car wtpm))
              (calcp3 (tctrs-meshtime tctrs1)
                      (params-activationwindow (cdr wtpm))
                      (tctrs-meshmessagedeliveries tctrs1)
                      (params-meshmessagedeliveriescap (cdr wtpm))
                      (params-meshmessagedeliveriesthreshold (cdr wtpm)))))
      (p3b (* (mget :w3b (car wtpm))
              (calcp3b (tctrs-meshtime tctrs0)
                       (params-activationwindow (cdr wtpm))
                       (tctrs-meshfailurepenalty tctrs0)
                       (tctrs-meshmessagedeliveries tctrs0)
                       (params-meshmessagedeliveriescap (cdr wtpm))
                       (params-meshmessagedeliveriesthreshold (cdr wtpm)))))
      (p3ba (* (mget :w3b (car wtpm))
               (calcp3b (tctrs-meshtime tctrs1)
                        (params-activationwindow (cdr wtpm))
                        (tctrs-meshfailurepenalty tctrs1)
                        (tctrs-meshmessagedeliveries tctrs1)
                        (params-meshmessagedeliveriescap (cdr wtpm))
                        (params-meshmessagedeliveriesthreshold (cdr wtpm)))))
      (p4 (* (mget :w4 (car wtpm))
             (calcp4 (tctrs-invalidmessagedeliveries tctrs0))))
      (p4a (* (mget :w4 (car wtpm))
              (calcp4 (tctrs-invalidmessagedeliveries tctrs1))))))
  :pro
  (:claim
      (<= (+ (* (mget :w1 (car wtpm))
                (calcp1 (tctrs-meshtime tctrs0)
                        (params-meshtimequantum (cdr wtpm))
                        (params-timequantainmeshcap (cdr wtpm))))
             (* (mget :w2 (car wtpm))
                (calcp2 (tctrs-firstmessagedeliveries tctrs0)
                        (params-p2cap (cdr wtpm))))
             (* (mget :w3 (car wtpm))
                (calcp3 (tctrs-meshtime tctrs0)
                        (params-activationwindow (cdr wtpm))
                        (tctrs-meshmessagedeliveries tctrs0)
                        (params-meshmessagedeliveriescap (cdr wtpm))
                        (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w3b (car wtpm))
                (calcp3b (tctrs-meshtime tctrs0)
                         (params-activationwindow (cdr wtpm))
                         (tctrs-meshfailurepenalty tctrs0)
                         (tctrs-meshmessagedeliveries tctrs0)
                         (params-meshmessagedeliveriescap (cdr wtpm))
                         (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w4 (car wtpm))
                (calcp4 (tctrs-invalidmessagedeliveries tctrs0))))
          (+ (* (mget :w1 (car wtpm))
                (calcp1 (tctrs-meshtime tctrs1)
                        (params-meshtimequantum (cdr wtpm))
                        (params-timequantainmeshcap (cdr wtpm))))
             (* (mget :w2 (car wtpm))
                (calcp2 (tctrs-firstmessagedeliveries tctrs1)
                        (params-p2cap (cdr wtpm))))
             (* (mget :w3 (car wtpm))
                (calcp3 (tctrs-meshtime tctrs1)
                        (params-activationwindow (cdr wtpm))
                        (tctrs-meshmessagedeliveries tctrs1)
                        (params-meshmessagedeliveriescap (cdr wtpm))
                        (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w3b (car wtpm))
                (calcp3b (tctrs-meshtime tctrs1)
                         (params-activationwindow (cdr wtpm))
                         (tctrs-meshfailurepenalty tctrs1)
                         (tctrs-meshmessagedeliveries tctrs1)
                         (params-meshmessagedeliveriescap (cdr wtpm))
                         (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w4 (car wtpm))
                (calcp4 (tctrs-invalidmessagedeliveries tctrs1))))))
  (:drop 1)
  (:claim
    (= (* (params-topicweight (cdr wtpm))
          (+ (* (mget :w1 (car wtpm))
                (calcp1 (tctrs-meshtime tctrs0)
                        (params-meshtimequantum (cdr wtpm))
                        (params-timequantainmeshcap (cdr wtpm))))
             (* (mget :w2 (car wtpm))
                (calcp2 (tctrs-firstmessagedeliveries tctrs0)
                        (params-p2cap (cdr wtpm))))
             (* (mget :w3 (car wtpm))
                (calcp3 (tctrs-meshtime tctrs0)
                        (params-activationwindow (cdr wtpm))
                        (tctrs-meshmessagedeliveries tctrs0)
                        (params-meshmessagedeliveriescap (cdr wtpm))
                        (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w3b (car wtpm))
                (calcp3b (tctrs-meshtime tctrs0)
                         (params-activationwindow (cdr wtpm))
                         (tctrs-meshfailurepenalty tctrs0)
                         (tctrs-meshmessagedeliveries tctrs0)
                         (params-meshmessagedeliveriescap (cdr wtpm))
                         (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w4 (car wtpm))
                (calcp4 (tctrs-invalidmessagedeliveries tctrs0)))))
       (calcscoretopic tctrs0 wtpm)))
  (:claim
    (= (* (params-topicweight (cdr wtpm))
          (+ (* (mget :w1 (car wtpm))
                (calcp1 (tctrs-meshtime tctrs1)
                        (params-meshtimequantum (cdr wtpm))
                        (params-timequantainmeshcap (cdr wtpm))))
             (* (mget :w2 (car wtpm))
                (calcp2 (tctrs-firstmessagedeliveries tctrs1)
                        (params-p2cap (cdr wtpm))))
             (* (mget :w3 (car wtpm))
                (calcp3 (tctrs-meshtime tctrs1)
                        (params-activationwindow (cdr wtpm))
                        (tctrs-meshmessagedeliveries tctrs1)
                        (params-meshmessagedeliveriescap (cdr wtpm))
                        (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w3b (car wtpm))
                (calcp3b (tctrs-meshtime tctrs1)
                         (params-activationwindow (cdr wtpm))
                         (tctrs-meshfailurepenalty tctrs1)
                         (tctrs-meshmessagedeliveries tctrs1)
                         (params-meshmessagedeliveriescap (cdr wtpm))
                         (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w4 (car wtpm))
                (calcp4 (tctrs-invalidmessagedeliveries tctrs1)))))
       (calcscoretopic tctrs1 wtpm)))
  (:claim (non-neg-rationalp (params-topicweight (cdr wtpm))))
  (:use
   (:instance
       a<=b->ac<=bc
       (c (params-topicweight (cdr wtpm)))
       (a (+ (* (mget :w1 (car wtpm))
                (calcp1 (tctrs-meshtime tctrs0)
                        (params-meshtimequantum (cdr wtpm))
                        (params-timequantainmeshcap (cdr wtpm))))
             (* (mget :w2 (car wtpm))
                (calcp2 (tctrs-firstmessagedeliveries tctrs0)
                        (params-p2cap (cdr wtpm))))
             (* (mget :w3 (car wtpm))
                (calcp3 (tctrs-meshtime tctrs0)
                        (params-activationwindow (cdr wtpm))
                        (tctrs-meshmessagedeliveries tctrs0)
                        (params-meshmessagedeliveriescap (cdr wtpm))
                        (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w3b (car wtpm))
                (calcp3b (tctrs-meshtime tctrs0)
                         (params-activationwindow (cdr wtpm))
                         (tctrs-meshfailurepenalty tctrs0)
                         (tctrs-meshmessagedeliveries tctrs0)
                         (params-meshmessagedeliveriescap (cdr wtpm))
                         (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w4 (car wtpm))
                (calcp4 (tctrs-invalidmessagedeliveries tctrs0)))))
       (b (+ (* (mget :w1 (car wtpm))
                (calcp1 (tctrs-meshtime tctrs1)
                        (params-meshtimequantum (cdr wtpm))
                        (params-timequantainmeshcap (cdr wtpm))))
             (* (mget :w2 (car wtpm))
                (calcp2 (tctrs-firstmessagedeliveries tctrs1)
                        (params-p2cap (cdr wtpm))))
             (* (mget :w3 (car wtpm))
                (calcp3 (tctrs-meshtime tctrs1)
                        (params-activationwindow (cdr wtpm))
                        (tctrs-meshmessagedeliveries tctrs1)
                        (params-meshmessagedeliveriescap (cdr wtpm))
                        (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w3b (car wtpm))
                (calcp3b (tctrs-meshtime tctrs1)
                         (params-activationwindow (cdr wtpm))
                         (tctrs-meshfailurepenalty tctrs1)
                         (tctrs-meshmessagedeliveries tctrs1)
                         (params-meshmessagedeliveriescap (cdr wtpm))
                         (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w4 (car wtpm))
                (calcp4 (tctrs-invalidmessagedeliveries tctrs1)))))))
  :pro
  (:claim
   (<= (* (params-topicweight (cdr wtpm))
          (+ (* (mget :w1 (car wtpm))
                (calcp1 (tctrs-meshtime tctrs0)
                        (params-meshtimequantum (cdr wtpm))
                        (params-timequantainmeshcap (cdr wtpm))))
             (* (mget :w2 (car wtpm))
                (calcp2 (tctrs-firstmessagedeliveries tctrs0)
                        (params-p2cap (cdr wtpm))))
             (* (mget :w3 (car wtpm))
                (calcp3 (tctrs-meshtime tctrs0)
                        (params-activationwindow (cdr wtpm))
                        (tctrs-meshmessagedeliveries tctrs0)
                        (params-meshmessagedeliveriescap (cdr wtpm))
                        (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w3b (car wtpm))
                (calcp3b (tctrs-meshtime tctrs0)
                         (params-activationwindow (cdr wtpm))
                         (tctrs-meshfailurepenalty tctrs0)
                         (tctrs-meshmessagedeliveries tctrs0)
                         (params-meshmessagedeliveriescap (cdr wtpm))
                         (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w4 (car wtpm))
                (calcp4 (tctrs-invalidmessagedeliveries tctrs0)))))
       (* (params-topicweight (cdr wtpm))
          (+ (* (mget :w1 (car wtpm))
                (calcp1 (tctrs-meshtime tctrs1)
                        (params-meshtimequantum (cdr wtpm))
                        (params-timequantainmeshcap (cdr wtpm))))
             (* (mget :w2 (car wtpm))
                (calcp2 (tctrs-firstmessagedeliveries tctrs1)
                        (params-p2cap (cdr wtpm))))
             (* (mget :w3 (car wtpm))
                (calcp3 (tctrs-meshtime tctrs1)
                        (params-activationwindow (cdr wtpm))
                        (tctrs-meshmessagedeliveries tctrs1)
                        (params-meshmessagedeliveriescap (cdr wtpm))
                        (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w3b (car wtpm))
                (calcp3b (tctrs-meshtime tctrs1)
                         (params-activationwindow (cdr wtpm))
                         (tctrs-meshfailurepenalty tctrs1)
                         (tctrs-meshmessagedeliveries tctrs1)
                         (params-meshmessagedeliveriescap (cdr wtpm))
                         (params-meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w4 (car wtpm))
                (calcp4 (tctrs-invalidmessagedeliveries tctrs1)))))))
  (:drop 1)
  :prove))

