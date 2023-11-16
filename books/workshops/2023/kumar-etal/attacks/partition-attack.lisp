; cert-flags: ? t :ttags :all :skip-proofs-okp t

(in-package "ACL2S")
(include-book "attack")

;; Setup TWP for AG3

(definec alltopics-part () :lot
  '(AGG BLOCKS SUB1 SUB2 SUB3 SUB4 SUB5 SUB6 SUB7 SUB8 SUB9
        SUB10 SUB11 SUB12))

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

(defconst *decayToZero-part* 1/100)

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     shared/params/config.go#L123

(defconst *seconds-per-slot-part* 1) ;; ARBITRARY 
(defconst *one-epoch-duration-part* 1) ;; ARBITRARY 

(defconst *aggregateWeight-part* (/ 1 2)) ;; weight for aggregate topic, see #L100
(defconst *beaconBlockWeight-part* (/ 8 10)) ;; weight for beacon topic, see #L77

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/gossip_scoring_params.go#L154
(defconst *slot-duration-part* (* *seconds-per-slot-part* 1))

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;    shared/params/config.go#L48
(defconst *slots-per-epoch-part* 10) ;; ARBITRARY 
(defconst *blocks-per-epoch-part* *slots-per-epoch-part*) ;; #L75
(defconst *decay-epoch-part* 5) ;; #L74

;; In line number comments, if I write BC, I am referring to:
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/pubsub.go

;; If I write SERV, I am referring to:
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/service.go

;; In all other cases, as indicated previously, I am referring to gossip_scoring_params.go.

;; I assume all times are given in units of 1 second ...

(defconst *enable-larger-gossip-history-part* 'nil)

(defconst *hbmInterval-part* (/ 700 1000))

(defconst *topicCap-part* (+ 32 (/ 72 100)))

(defconst *comm-count-per-slot-part* 10) ;; ARBITRARY - refer to #L173 ... they have not decided yet!
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     shared/params/config.go#L123
(defconst *target-aggregators-per-committee-part* 5) ;; ARBITRARY
(defconst *aggregators-per-slot-part* (* *comm-count-per-slot-part* *target-aggregators-per-committee-part*)) ;; #L1871
(defconst *agg-per-epoch-part* (* *aggregators-per-slot-part* *slots-per-epoch-part*))
(defconst *attestationTotalWeight-part* 1) ;; #L23
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;; shared/params/network_config.go#L40
(defconst *AttestationSubnetCount-part* (- (len (alltopics-part)) 2))         ;; ARBITRARY 
(defconst *MinGenesisActiveValidatorCount-part* 300) ;; ARBITRARY -----------------|
;; -------> but currently needs to be divisible by 50 x attestationSubnetCount.

(defconst *subnet-topicWeight-part* (/ *attestationTotalWeight-part* *AttestationSubnetCount-part*)) ;; #L121
(defconst *activeValidators-part* *MinGenesisActiveValidatorCount-part*) ;; #L169
(defconst *subnet-subnetWeight-part* (/ *activeValidators-part* *AttestationSubnetCount-part*)) ;; #L122
(defconst *subnet-minimumWeight-part* (/ *subnet-subnetWeight-part* 50)) ;; #L123
(defconst *subnet-numsPerSlot-part* (floor *subnet-subnetWeight-part* *slots-per-epoch-part*)) ;; #L124
(defconst *subnet-comsPerSlot-part* *comm-count-per-slot-part*) ;; #L125
(defconst *subnet-exceedsThreshold-part*
  (>= *subnet-comsPerSlot-part*
      (* 2 (/ *AttestationSubnetCount-part* *slots-per-epoch-part*)))) ;; #L126
(defconst *subnet-firstDecay-part* (if *subnet-exceedsThreshold-part* 4 1)) ;; #L127, 130
(defconst *subnet-meshDecay-part* (if *subnet-exceedsThreshold-part* 16 4)) ;; #L128, 131

(defconst *eth-default-block-weights-part*
  (weights (/ 324 10000)  ;; w_1  = time in mesh weight                (#L78)
           1              ;; w_2  = first message deliveries weight    (#L81)
           (/ -717 1000)  ;; w_3  = mesh message deliveries weight     (#L84)
           (/ -717 1000)  ;; w_3b = mesh failure penalty weight        (#L90)
           (- -140 (/ 4475 10000)) ;; w_4  = invalid messages weight   (#L92)
           1       ;; w_5  = application-specific score weight         (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-block-weights-part*))

(defconst *eth-default-agg-weights-part*
  (weights (/ 324 10000) ;; w_1  = time in mesh weight              (#L101)
           (/ 128 1000)  ;; w_2  = first message deliveries weight  (#L104)
           (/ -64 1000)  ;; w_3  = mesh message deliveries weight   (#L107)
           (/ -64 1000)  ;; w_3b = mesh failure penalty weight      (#L113)
           (- -140 (/ 4475 10000)) ;; w_4 = invalid messages weight (#L115)
           1             ;; w_5 = application-specific score weight    (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-agg-weights-part*))

(defconst *eth-default-agg-subnet-weights-part*
  (weights (/ 324 10000) ;; w_1 = time in mesh weight                  (#L134)
           (/ 955 1000)  ;; w_2 = first message deliveries weight      (#L138)
           (- -37 (/ 55 100)) ;; w_3  = mesh message deliveries weight (#L141)
           (- -37 (/ 55 100)) ;; w_3b = mesh failure penalty weight    (#L147)
           -4544              ;; w_4 = invalid messages weight 
           1       ;; w_5  = application-specific score weight         (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-agg-subnet-weights-part*))

;; ;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L162
;; (definecd scoreDecay(x :non-neg-rational) :non-neg-rational
;;   (b* (((when (= x 0)) 0)
;;        (numOfTimes (/ x *slot-duration-part*)))
;;     3/4))
;;     ;;(expt *decayToZero-part* (floor 1 numOfTimes))))

;; Currently failing ...
(defconst *eth-default-block-params-part*
  (params 4               ;; activationWindow    : #L89 aka MeshMessageDeliveriesActivation
	  *slot-duration-part* ;; meshTimeQuantum     : #L79
	  23              ;; p2cap               : #L83 aka FirstMessageDeliveriesCap
	  300             ;; timeQuantaInMeshCap : #L80
	  (* *blocks-per-epoch-part*
	     *decay-epoch-part*) ;; meshMessageDeliveriesCap : #L86
	  ;; meshMessageDeliveriesThreshold             : #L87
	  (/ (* *blocks-per-epoch-part* *decay-epoch-part*) 10)
	  *topicCap-part*        ;; topiccap          : #L39 (global)
	  -16000            ;; greyListThreshold : #L33 (global)
	  8                 ;; d                 : BC #L120
	  6                 ;; dlow              : BC #L119
	  12                ;; dhigh             : default in gossipsub.go
	  6                 ;; dlazy             : default in gossipsub.go
	  *hbmInterval-part* ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60 ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-part* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-part*) ;; seenTTL       : BC #L124
	  ;; https://github.com/silesiacoin/prysm-spike/blob/
	  ;; d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L35
	  5 ;; opportunisticGraftThreshold
	  ;; Let scoreDecay(x) = decayToZero^(1/(x/oneSlotDuration)).  Then, starting at:
	  ;;
	  ;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
	  ;;     beacon-chain/p2p/gossip_scoring_params.go#L73
	  ;;
	  *beaconBlockWeight-part*
	  ;; MeshMessageDeliveriesDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  398/1000
	  ;; FirstMessageDeliveriesDecay = scoreDecay(20 * oneEpochDuration)
	  794/1000
	  63/100 ;; behaviourPenaltyDecay
	  ;;  MeshFailurePenaltyDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  398/1000
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 * oneEpochDuration)
	  912/1000
	  *decayToZero-part* ;; decayToZero
	  *slot-duration-part* ;; decayInterval
	  ))

(check= t (paramsp *eth-default-block-params-part*))

(defconst *eth-default-aggregate-params-part*
  (params (* 32 *slot-duration-part*) ;; activationWindow               : #L112
	  *slot-duration-part*        ;; meshTimeQuantum                : #L102
	  179                    ;; p2cap                          : #L106
	  300                    ;; timeQuantaInMeshCap            : #L103
	  *agg-per-epoch-part*        ;; meshMessageDeliveriesCap       : #L109
	  (/ *agg-per-epoch-part* 50) ;; meshMessageDeliveriesThreshold : #L110
	  *topicCap-part*             ;; topicCap,          see above (global)
	  -16000                 ;; greyListThreshold, see above (global)
	  8                      ;; d                                   : BC #L120
	  6                      ;; dlow                                : BC #L119
	  12                     ;; dhigh                               : default in gossipsub.go
	  6                      ;; dlazy                               : default in gossipsub.go
	  *hbmInterval-part*          ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60                     ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-part* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
          ;; TODO : clarify gossipfactor
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-part*) ;; seenTTL : BC #L124
	  5 ;; opportunisticGraftThreshold
	  *aggregateWeight-part* ;; topicWeight = aggregateWeight       #L100
	  1/100 ;; MeshMessageDeliveriesDecay  = scoreDecay(1 epoch) #L108
	  1/100 ;; FirstMessageDeliveriesDecay = scoreDecay(1 epoch) #L105
	  63/100 ;; behaviourPenaltyDecay
	  1/100 ;; MeshFailurePenaltyDecay     = scoreDecay(1 epoch) #L114
	  912/1000 ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs) #L116
	  *decayToZero-part*
	  *slot-duration-part*
	  ))

(check= t (paramsp *eth-default-aggregate-params-part*))

(defconst *eth-default-aggregate-subnet-params-part*
  (params (* 17 *slot-duration-part*) ;; activationWindow               : #L146
	  *subnet-numsPerSlot-part*   ;; meshTimeQuantum                : #L136
	  24                     ;; p2cap                          : #L140
	  300                    ;; timeQuantaInMeshCap            : #L137
	  *subnet-subnetWeight-part*  ;; meshMessageDeliveriesCap       : #L143
	  *subnet-minimumWeight-part* ;; meshMessageDeliveriesThreshold : #L144
	   *topicCap-part*             ;; topicCap,          see above (global)
	  -16000                 ;; greyListThreshold, see above (global)
	  8                      ;; d                                   : BC #L120
	  6                      ;; dlow                                : BC #L119
	  12                     ;; dhigh                               : default in gossipsub.go
	  6                      ;; dlazy                               : default in gossipsub.go
	  *hbmInterval-part*          ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60                     ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-part* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
          ;; TODO
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-part*) ;; seenTTL : BC #L124
	  5 ;; OpportunisticGraftThreshold
	  ;; TODO: MeshMessageDeliveriesWindow   = 2 seconds                           #L145
	  *subnet-topicWeight-part*  ;; topicWeight   = *subnet-topicWeight-part*                      #L134
	  ;; MeshMessageDeliveriesDecay    = scoreDecay(*subnet-meshDecay-part* x 1 epoch)  #L142
	  749/1000
	  ;; FirstMessageDeliveriesDecay   = scoreDecay(*subnet-firstDecay-part* x 1 epoch) #L139
	  316/1000
	  631/1000 ;; behaviourPenaltyDecay
	  ;; MeshFailurePenaltyDecay       = scoreDecay(*subnet-meshDecay-part* x 1 epoch)  #L148
	  749/1000
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs)                     #L150
	  912/1000
	  *decayToZero-part*
	  *slot-duration-part*
	  ))

(check= t (paramsp *eth-default-aggregate-subnet-params-part*))

(defconst *eth-twp-part*
  `((AGG . (,*eth-default-agg-weights-part* . ,*eth-default-aggregate-params-part*))
    (BLOCKS . (,*eth-default-block-weights-part* . ,*eth-default-block-params-part*))
    ;; We can have 0 or more subnet aggregator topics.  For now, let's assume 3.
    (SUB1 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB10 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB11 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB12 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB2 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB3 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB4 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB5 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB6 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB7 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB8 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    (SUB9 . (,*eth-default-agg-subnet-weights-part*
             . ,*eth-default-aggregate-subnet-params-part*))
    ))

(check= t (twpp *eth-twp-part*))

#|
"A Test with Ropsten network configuration"

;; 212.92 seconds realtime, 181.73 seconds runtime
;; (540,926,802,880 bytes allocated).
;; (100000 nil nil nil nil nil nil t t t t)
(time$
 (b* ((ticks 100)
      (pats '(P275 P262))
      (pvis '(P187 P353 P337 P476 P399 P509))
      (attacktopics '(SUB1 SUB2 SUB3))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   *ropsten*
                   (alltopics-part)))
      (evnts (emit-evnts-part pats pvis pvis (alltopics-part)
                              attacktopics 20 0 18 ticks)))
   ;; P222 is attacker, P834 is observer who records violations
   (eclipse-attack-violations grp evnts evnts pats attacktopics 'P337 0
                              *eth-twp-part* 42 nil)))

|#
