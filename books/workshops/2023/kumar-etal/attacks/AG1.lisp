(in-package "ACL2S")
(include-book "attack")

(definec alltopics () :lot
  '(AGG BLOCKS SUB1 SUB2 SUB3))

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
(defconst *AttestationSubnetCount* (- (len (alltopics)) 2))         ;; ARBITRARY 
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

;; ;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L162
;; (definecd scoreDecay(x :non-neg-rational) :non-neg-rational
;;   (b* (((when (= x 0)) 0)
;;        (numOfTimes (/ x *slot-duration*)))
;;     3/4))
;;     ;;(expt *decayToZero* (floor 1 numOfTimes))))

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
	  398/1000
	  ;; FirstMessageDeliveriesDecay = scoreDecay(20 * oneEpochDuration)
	  794/1000
	  63/100 ;; behaviourPenaltyDecay
	  ;;  MeshFailurePenaltyDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  398/1000
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 * oneEpochDuration)
	  912/1000
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
	  1/100 ;; MeshMessageDeliveriesDecay  = scoreDecay(1 epoch) #L108
	  1/100 ;; FirstMessageDeliveriesDecay = scoreDecay(1 epoch) #L105
	  63/100 ;; behaviourPenaltyDecay
	  1/100 ;; MeshFailurePenaltyDecay     = scoreDecay(1 epoch) #L114
	  912/1000 ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs) #L116
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
	  749/1000
	  ;; FirstMessageDeliveriesDecay   = scoreDecay(*subnet-firstDecay* x 1 epoch) #L139
	  316/1000
	  631/1000 ;; behaviourPenaltyDecay
	  ;; MeshFailurePenaltyDecay       = scoreDecay(*subnet-meshDecay* x 1 epoch)  #L148
	  749/1000
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs)                     #L150
	  912/1000
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

;; ---------------------- ATTACK ------------------------------

; 53.06 seconds realtime, 50.89 seconds runtime
; (67,770,610,624 bytes allocated).
;; (time$
;;  (b* ((attacktopics '(SUB1))
;;       (grp (initialize-group-of-meshpeers '(A B)
;;                                           '(A B)
;;                                           (topics)
;;                                           100))
;;       (evnts (emit-evnts-ticks 'A 'B (alltopics) attacktopics 20 1 18)))
;;    (eth-attack-violations grp evnts evnts 'A 'B attacktopics 0 *eth-twp* 42 nil)))


;; attack on goerli network
; 251.74 seconds realtime, 230.03 seconds runtime
; (646,418,567,808 bytes allocated).
;; (nil t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t)
(time$
 (b* ((attacktopics '(SUB1))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   *goerli*
                   (alltopics)))
      (evnts (emit-evnts 'P222 'P834 (alltopics)
                               attacktopics 20 1 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P222 'P834 attacktopics 0
                          *eth-twp* 42 nil)))


;; attack on rinkeby network
; 448.01 seconds realtime, 416.43 seconds runtime
; (1,161,282,802,096 bytes allocated).
;; (nil t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t)
(time$
 (b* ((attacktopics '(SUB1))
      (grp (reduce* graph->group 
                    (initialize-group-of-meshpeers '()
                                                   '()
                                                   (topics)
                                                   100)
                    *rinkeby*
                    (alltopics)))
      (evnts (emit-evnts 'P256 'P436 (alltopics)
                               attacktopics 20 1 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P256 'P436 attacktopics 0
                          *eth-twp* 42 nil)))


;; attack on ropsten network
; 74.05 seconds realtime, 73.69 seconds runtime
; (4,870,541,376 bytes allocated).
;; (nil t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t)
(time$
 (b* ((attacktopics '(SUB1))
      (grp (reduce* graph->group 
                    (initialize-group-of-meshpeers '()
                                                   '()
                                                   (topics)
                                                   100)
                    *ropsten*
                    (alltopics)))
      (evnts (emit-evnts 'P256 'P448 (alltopics)
                               attacktopics 20 1 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P256 'P448 attacktopics 0
                          *eth-twp* 42 nil)))


;; with 100* len evnts
; 786.90 seconds realtime, 695.95 seconds runtime
; (2,073,070,226,864 bytes allocated).
;; (nil t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t)
;; since not displaying hbm events
