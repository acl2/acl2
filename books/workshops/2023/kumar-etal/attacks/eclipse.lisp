; cert-flags: ? t :ttags :all :skip-proofs-okp t

(in-package "ACL2S")
(include-book "attack")

;; Setup TWP for AG3

(definec alltopics-ecl () :lot
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

(defconst *decayToZero-ecl* 1/100)

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     shared/params/config.go#L123

(defconst *seconds-per-slot-ecl* 1) ;; ARBITRARY 
(defconst *one-epoch-duration-ecl* 1) ;; ARBITRARY 

(defconst *aggregateWeight-ecl* (/ 1 2)) ;; weight for aggregate topic, see #L100
(defconst *beaconBlockWeight-ecl* (/ 8 10)) ;; weight for beacon topic, see #L77

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/gossip_scoring_params.go#L154
(defconst *slot-duration-ecl* (* *seconds-per-slot-ecl* 1))

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;    shared/params/config.go#L48
(defconst *slots-per-epoch-ecl* 10) ;; ARBITRARY 
(defconst *blocks-per-epoch-ecl* *slots-per-epoch-ecl*) ;; #L75
(defconst *decay-epoch-ecl* 5) ;; #L74

;; In line number comments, if I write BC, I am referring to:
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/pubsub.go

;; If I write SERV, I am referring to:
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/service.go

;; In all other cases, as indicated previously, I am referring to gossip_scoring_params.go.

;; I assume all times are given in units of 1 second ...

(defconst *enable-larger-gossip-history-ecl* 'nil)

(defconst *hbmInterval-ecl* (/ 700 1000))

(defconst *topicCap-ecl* (+ 32 (/ 72 100)))

(defconst *comm-count-per-slot-ecl* 10) ;; ARBITRARY - refer to #L173 ... they have not decided yet!
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     shared/params/config.go#L123
(defconst *target-aggregators-per-committee-ecl* 5) ;; ARBITRARY
(defconst *aggregators-per-slot-ecl* (* *comm-count-per-slot-ecl* *target-aggregators-per-committee-ecl*)) ;; #L1871
(defconst *agg-per-epoch-ecl* (* *aggregators-per-slot-ecl* *slots-per-epoch-ecl*))
(defconst *attestationTotalWeight-ecl* 1) ;; #L23
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;; shared/params/network_config.go#L40
(defconst *AttestationSubnetCount-ecl* (- (len (alltopics-ecl)) 2))         ;; ARBITRARY 
(defconst *MinGenesisActiveValidatorCount-ecl* 300) ;; ARBITRARY -----------------|
;; -------> but currently needs to be divisible by 50 x attestationSubnetCount.

(defconst *subnet-topicWeight-ecl* (/ *attestationTotalWeight-ecl* *AttestationSubnetCount-ecl*)) ;; #L121
(defconst *activeValidators-ecl* *MinGenesisActiveValidatorCount-ecl*) ;; #L169
(defconst *subnet-subnetWeight-ecl* (/ *activeValidators-ecl* *AttestationSubnetCount-ecl*)) ;; #L122
(defconst *subnet-minimumWeight-ecl* (/ *subnet-subnetWeight-ecl* 50)) ;; #L123
(defconst *subnet-numsPerSlot-ecl* (floor *subnet-subnetWeight-ecl* *slots-per-epoch-ecl*)) ;; #L124
(defconst *subnet-comsPerSlot-ecl* *comm-count-per-slot-ecl*) ;; #L125
(defconst *subnet-exceedsThreshold-ecl*
  (>= *subnet-comsPerSlot-ecl*
      (* 2 (/ *AttestationSubnetCount-ecl* *slots-per-epoch-ecl*)))) ;; #L126
(defconst *subnet-firstDecay-ecl* (if *subnet-exceedsThreshold-ecl* 4 1)) ;; #L127, 130
(defconst *subnet-meshDecay-ecl* (if *subnet-exceedsThreshold-ecl* 16 4)) ;; #L128, 131

(defconst *eth-default-block-weights-ecl*
  (weights (/ 324 10000)  ;; w_1  = time in mesh weight                (#L78)
           1              ;; w_2  = first message deliveries weight    (#L81)
           (/ -717 1000)  ;; w_3  = mesh message deliveries weight     (#L84)
           (/ -717 1000)  ;; w_3b = mesh failure penalty weight        (#L90)
           (- -140 (/ 4475 10000)) ;; w_4  = invalid messages weight   (#L92)
           1       ;; w_5  = application-specific score weight         (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-block-weights-ecl*))

(defconst *eth-default-agg-weights-ecl*
  (weights (/ 324 10000) ;; w_1  = time in mesh weight              (#L101)
           (/ 128 1000)  ;; w_2  = first message deliveries weight  (#L104)
           (/ -64 1000)  ;; w_3  = mesh message deliveries weight   (#L107)
           (/ -64 1000)  ;; w_3b = mesh failure penalty weight      (#L113)
           (- -140 (/ 4475 10000)) ;; w_4 = invalid messages weight (#L115)
           1             ;; w_5 = application-specific score weight    (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-agg-weights-ecl*))

(defconst *eth-default-agg-subnet-weights-ecl*
  (weights (/ 324 10000) ;; w_1 = time in mesh weight                  (#L134)
           (/ 955 1000)  ;; w_2 = first message deliveries weight      (#L138)
           (- -37 (/ 55 100)) ;; w_3  = mesh message deliveries weight (#L141)
           (- -37 (/ 55 100)) ;; w_3b = mesh failure penalty weight    (#L147)
           -4544              ;; w_4 = invalid messages weight 
           1       ;; w_5  = application-specific score weight         (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-agg-subnet-weights-ecl*))

;; ;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L162
;; (definecd scoreDecay(x :non-neg-rational) :non-neg-rational
;;   (b* (((when (= x 0)) 0)
;;        (numOfTimes (/ x *slot-duration-ecl*)))
;;     3/4))
;;     ;;(expt *decayToZero-ecl* (floor 1 numOfTimes))))

(defconst *eth-default-block-params-ecl*
  (params 4               ;; activationWindow    : #L89 aka MeshMessageDeliveriesActivation
	  *slot-duration-ecl* ;; meshTimeQuantum     : #L79
	  23              ;; p2cap               : #L83 aka FirstMessageDeliveriesCap
	  300             ;; timeQuantaInMeshCap : #L80
	  (* *blocks-per-epoch-ecl*
	     *decay-epoch-ecl*) ;; meshMessageDeliveriesCap : #L86
	  ;; meshMessageDeliveriesThreshold             : #L87
	  (/ (* *blocks-per-epoch-ecl* *decay-epoch-ecl*) 10)
	  *topicCap-ecl*        ;; topiccap          : #L39 (global)
	  -16000            ;; greyListThreshold : #L33 (global)
	  8                 ;; d                 : BC #L120
	  6                 ;; dlow              : BC #L119
	  12                ;; dhigh             : default in gossipsub.go
	  6                 ;; dlazy             : default in gossipsub.go
	  *hbmInterval-ecl* ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60 ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-ecl* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-ecl*) ;; seenTTL       : BC #L124
	  ;; https://github.com/silesiacoin/prysm-spike/blob/
	  ;; d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L35
	  5 ;; opportunisticGraftThreshold
	  ;; Let scoreDecay(x) = decayToZero^(1/(x/oneSlotDuration)).  Then, starting at:
	  ;;
	  ;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
	  ;;     beacon-chain/p2p/gossip_scoring_params.go#L73
	  ;;
	  *beaconBlockWeight-ecl*
	  ;; MeshMessageDeliveriesDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  398/1000
	  ;; FirstMessageDeliveriesDecay = scoreDecay(20 * oneEpochDuration)
	  794/1000
	  63/100 ;; behaviourPenaltyDecay
	  ;;  MeshFailurePenaltyDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  398/1000
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 * oneEpochDuration)
	  912/1000
	  *decayToZero-ecl* ;; decayToZero
	  *slot-duration-ecl* ;; decayInterval
	  ))

(check= t (paramsp *eth-default-block-params-ecl*))

(defconst *eth-default-aggregate-params-ecl*
  (params (* 32 *slot-duration-ecl*) ;; activationWindow               : #L112
	  *slot-duration-ecl*        ;; meshTimeQuantum                : #L102
	  179                    ;; p2cap                          : #L106
	  300                    ;; timeQuantaInMeshCap            : #L103
	  *agg-per-epoch-ecl*        ;; meshMessageDeliveriesCap       : #L109
	  (/ *agg-per-epoch-ecl* 50) ;; meshMessageDeliveriesThreshold : #L110
	  *topicCap-ecl*             ;; topicCap,          see above (global)
	  -16000                 ;; greyListThreshold, see above (global)
	  8                      ;; d                                   : BC #L120
	  6                      ;; dlow                                : BC #L119
	  12                     ;; dhigh                               : default in gossipsub.go
	  6                      ;; dlazy                               : default in gossipsub.go
	  *hbmInterval-ecl*          ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60                     ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-ecl* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
          ;; TODO : clarify gossipfactor
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-ecl*) ;; seenTTL : BC #L124
	  5 ;; opportunisticGraftThreshold
	  *aggregateWeight-ecl* ;; topicWeight = aggregateWeight       #L100
	  1/100 ;; MeshMessageDeliveriesDecay  = scoreDecay(1 epoch) #L108
	  1/100 ;; FirstMessageDeliveriesDecay = scoreDecay(1 epoch) #L105
	  63/100 ;; behaviourPenaltyDecay
	  1/100 ;; MeshFailurePenaltyDecay     = scoreDecay(1 epoch) #L114
	  912/1000 ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs) #L116
	  *decayToZero-ecl*
	  *slot-duration-ecl*
	  ))

(check= t (paramsp *eth-default-aggregate-params-ecl*))

(defconst *eth-default-aggregate-subnet-params-ecl*
  (params (* 17 *slot-duration-ecl*) ;; activationWindow               : #L146
	  *subnet-numsPerSlot-ecl*   ;; meshTimeQuantum                : #L136
	  24                     ;; p2cap                          : #L140
	  300                    ;; timeQuantaInMeshCap            : #L137
	  *subnet-subnetWeight-ecl*  ;; meshMessageDeliveriesCap       : #L143
	  *subnet-minimumWeight-ecl* ;; meshMessageDeliveriesThreshold : #L144
	   *topicCap-ecl*             ;; topicCap,          see above (global)
	  -16000                 ;; greyListThreshold, see above (global)
	  8                      ;; d                                   : BC #L120
	  6                      ;; dlow                                : BC #L119
	  12                     ;; dhigh                               : default in gossipsub.go
	  6                      ;; dlazy                               : default in gossipsub.go
	  *hbmInterval-ecl*          ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60                     ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-ecl* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
          ;; TODO
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-ecl*) ;; seenTTL : BC #L124
	  5 ;; OpportunisticGraftThreshold
	  ;; TODO: MeshMessageDeliveriesWindow   = 2 seconds                           #L145
	  *subnet-topicWeight-ecl*  ;; topicWeight   = *subnet-topicWeight-ecl*                      #L134
	  ;; MeshMessageDeliveriesDecay    = scoreDecay(*subnet-meshDecay-ecl* x 1 epoch)  #L142
	  749/1000
	  ;; FirstMessageDeliveriesDecay   = scoreDecay(*subnet-firstDecay-ecl* x 1 epoch) #L139
	  316/1000
	  631/1000 ;; behaviourPenaltyDecay
	  ;; MeshFailurePenaltyDecay       = scoreDecay(*subnet-meshDecay-ecl* x 1 epoch)  #L148
	  749/1000
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs)                     #L150
	  912/1000
	  *decayToZero-ecl*
	  *slot-duration-ecl*
	  ))

(check= t (paramsp *eth-default-aggregate-subnet-params-ecl*))

(defconst *eth-twp-ecl*
  `((AGG . (,*eth-default-agg-weights-ecl* . ,*eth-default-aggregate-params-ecl*))
    (BLOCKS . (,*eth-default-block-weights-ecl* . ,*eth-default-block-params-ecl*))
    ;; We can have 0 or more subnet aggregator topics.  For now, let's assume 3.
    (SUB1 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB10 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB11 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB12 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB2 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB3 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB4 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB5 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB6 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB7 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB8 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    (SUB9 . (,*eth-default-agg-subnet-weights-ecl*
             . ,*eth-default-aggregate-subnet-params-ecl*))
    ))

(check= t (twpp *eth-twp-ecl*))

;; graph : *Ropsten-ecl*
;; P40 , the victim has degree 3
;; connected to P162, P226, P45
;; P16 can send to all 3

#|
"A Test with ropsten network configuration"

(time$
 (b* ((ticks 100)
      (pats '(P162 P226 P45))
      (attacktopics '(SUB1 SUB2 SUB3))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   *ropsten*
                   (alltopics-ecl)))
      (evnts (emit-evnts-eclipse pats pats 'P40 (alltopics-ecl)
                                 attacktopics 20 0 18 ticks)))
   ;; P222 is attacker, P834 is observer who records violations
   (eclipse-attack-violations grp evnts evnts pats attacktopics 'P40 0
                              *eth-twp-ecl* 42 nil)))

|#
