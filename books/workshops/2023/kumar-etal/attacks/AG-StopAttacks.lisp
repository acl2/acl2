; cert-flags: ? t :ttags :all :skip-proofs-okp t

(in-package "ACL2S")
(include-book "attack")

;; Setup TWP for AG3

(definec alltopics-ag () :lot
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

(defconst *decayToZero-ags* 1/100)

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     shared/params/config.go#L123

(defconst *seconds-per-slot-ags* 1) ;; ARBITRARY 
(defconst *one-epoch-duration-ags* 1) ;; ARBITRARY 

(defconst *aggregateWeight-ags* (/ 1 2)) ;; weight for aggregate topic, see #L100
(defconst *beaconBlockWeight-ags* (/ 8 10)) ;; weight for beacon topic, see #L77

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/gossip_scoring_params.go#L154
(defconst *slot-duration-ags* (* *seconds-per-slot-ags* 1))

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;    shared/params/config.go#L48
(defconst *slots-per-epoch-ags* 10) ;; ARBITRARY 
(defconst *blocks-per-epoch-ags* *slots-per-epoch-ags*) ;; #L75
(defconst *decay-epoch-ags* 5) ;; #L74

;; In line number comments, if I write BC, I am referring to:
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/pubsub.go

;; If I write SERV, I am referring to:
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/service.go

;; In all other cases, as indicated previously, I am referring to gossip_scoring_params.go.

;; I assume all times are given in units of 1 second ...

(defconst *enable-larger-gossip-history-ags* 'nil)

(defconst *hbmInterval-ags* (/ 700 1000))

(defconst *topicCap-ags* (+ 32 (/ 72 100)))

(defconst *comm-count-per-slot-ags* 10) ;; ARBITRARY - refer to #L173 ... they have not decided yet!
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     shared/params/config.go#L123
(defconst *target-aggregators-per-committee-ags* 5) ;; ARBITRARY
(defconst *aggregators-per-slot-ags* (* *comm-count-per-slot-ags* *target-aggregators-per-committee-ags*)) ;; #L1871
(defconst *agg-per-epoch-ags* (* *aggregators-per-slot-ags* *slots-per-epoch-ags*))
(defconst *attestationTotalWeight-ags* 1) ;; #L23
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;; shared/params/network_config.go#L40
(defconst *AttestationSubnetCount-ags* (- (len (alltopics-ag)) 2))         ;; ARBITRARY 
(defconst *MinGenesisActiveValidatorCount-ags* 300) ;; ARBITRARY -----------------|
;; -------> but currently needs to be divisible by 50 x attestationSubnetCount.

(defconst *subnet-topicWeight-ags* (/ *attestationTotalWeight-ags* *AttestationSubnetCount-ags*)) ;; #L121
(defconst *activeValidators-ags* *MinGenesisActiveValidatorCount-ags*) ;; #L169
(defconst *subnet-subnetWeight-ags* (/ *activeValidators-ags* *AttestationSubnetCount-ags*)) ;; #L122
(defconst *subnet-minimumWeight-ags* (/ *subnet-subnetWeight-ags* 50)) ;; #L123
(defconst *subnet-numsPerSlot-ags* (floor *subnet-subnetWeight-ags* *slots-per-epoch-ags*)) ;; #L124
(defconst *subnet-comsPerSlot-ags* *comm-count-per-slot-ags*) ;; #L125
(defconst *subnet-exceedsThreshold-ags*
  (>= *subnet-comsPerSlot-ags*
      (* 2 (/ *AttestationSubnetCount-ags* *slots-per-epoch-ags*)))) ;; #L126
(defconst *subnet-firstDecay-ags* (if *subnet-exceedsThreshold-ags* 4 1)) ;; #L127, 130
(defconst *subnet-meshDecay-ags* (if *subnet-exceedsThreshold-ags* 16 4)) ;; #L128, 131

(defconst *eth-default-block-weights-ags*
  (weights (/ 324 10000)  ;; w_1  = time in mesh weight                (#L78)
           1              ;; w_2  = first message deliveries weight    (#L81)
           (/ -717 1000)  ;; w_3  = mesh message deliveries weight     (#L84)
           (/ -717 1000)  ;; w_3b = mesh failure penalty weight        (#L90)
           (- -140 (/ 4475 10000)) ;; w_4  = invalid messages weight   (#L92)
           1       ;; w_5  = application-specific score weight         (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-block-weights-ags*))

(defconst *eth-default-agg-weights-ags*
  (weights (/ 324 10000) ;; w_1  = time in mesh weight              (#L101)
           (/ 128 1000)  ;; w_2  = first message deliveries weight  (#L104)
           (/ -64 1000)  ;; w_3  = mesh message deliveries weight   (#L107)
           (/ -64 1000)  ;; w_3b = mesh failure penalty weight      (#L113)
           (- -140 (/ 4475 10000)) ;; w_4 = invalid messages weight (#L115)
           1             ;; w_5 = application-specific score weight    (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-agg-weights-ags*))

(defconst *eth-default-agg-subnet-weights-ags*
  (weights (/ 324 10000) ;; w_1 = time in mesh weight                  (#L134)
           (/ 955 1000)  ;; w_2 = first message deliveries weight      (#L138)
           (- -37 (/ 55 100)) ;; w_3  = mesh message deliveries weight (#L141)
           (- -37 (/ 55 100)) ;; w_3b = mesh failure penalty weight    (#L147)
           -4544              ;; w_4 = invalid messages weight 
           1       ;; w_5  = application-specific score weight         (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-agg-subnet-weights-ags*))

;; ;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L162
;; (definecd scoreDecay(x :non-neg-rational) :non-neg-rational
;;   (b* (((when (= x 0)) 0)
;;        (numOfTimes (/ x *slot-duration-ags*)))
;;     3/4))
;;     ;;(expt *decayToZero* (floor 1 numOfTimes))))

;; Currently failing ...
(defconst *eth-default-block-params-ags*
  (params 4               ;; activationWindow    : #L89 aka MeshMessageDeliveriesActivation
	  *slot-duration-ags* ;; meshTimeQuantum     : #L79
	  23              ;; p2cap               : #L83 aka FirstMessageDeliveriesCap
	  300             ;; timeQuantaInMeshCap : #L80
	  (* *blocks-per-epoch-ags*
	     *decay-epoch-ags*) ;; meshMessageDeliveriesCap : #L86
	  ;; meshMessageDeliveriesThreshold             : #L87
	  (/ (* *blocks-per-epoch-ags* *decay-epoch-ags*) 10)
	  *topicCap-ags*        ;; topiccap          : #L39 (global)
	  -16000            ;; greyListThreshold : #L33 (global)
	  8                 ;; d                 : BC #L120
	  6                 ;; dlow              : BC #L119
	  12                ;; dhigh             : default in gossipsub.go
	  6                 ;; dlazy             : default in gossipsub.go
	  *hbmInterval-ags* ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60 ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-ags* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-ags*) ;; seenTTL       : BC #L124
	  ;; https://github.com/silesiacoin/prysm-spike/blob/
	  ;; d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L35
	  5 ;; opportunisticGraftThreshold
	  ;; Let scoreDecay(x) = decayToZero^(1/(x/oneSlotDuration)).  Then, starting at:
	  ;;
	  ;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
	  ;;     beacon-chain/p2p/gossip_scoring_params.go#L73
	  ;;
	  *beaconBlockWeight-ags*
	  ;; MeshMessageDeliveriesDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  398/1000
	  ;; FirstMessageDeliveriesDecay = scoreDecay(20 * oneEpochDuration)
	  794/1000
	  63/100 ;; behaviourPenaltyDecay
	  ;;  MeshFailurePenaltyDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  398/1000
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 * oneEpochDuration)
	  912/1000
	  *decayToZero-ags* ;; decayToZero
	  *slot-duration-ags* ;; decayInterval
	  ))

(check= t (paramsp *eth-default-block-params-ags*))

(defconst *eth-default-aggregate-params-ags*
  (params (* 32 *slot-duration-ags*) ;; activationWindow               : #L112
	  *slot-duration-ags*        ;; meshTimeQuantum                : #L102
	  179                    ;; p2cap                          : #L106
	  300                    ;; timeQuantaInMeshCap            : #L103
	  *agg-per-epoch-ags*        ;; meshMessageDeliveriesCap       : #L109
	  (/ *agg-per-epoch-ags* 50) ;; meshMessageDeliveriesThreshold : #L110
	  *topicCap-ags*             ;; topicCap,          see above (global)
	  -16000                 ;; greyListThreshold, see above (global)
	  8                      ;; d                                   : BC #L120
	  6                      ;; dlow                                : BC #L119
	  12                     ;; dhigh                               : default in gossipsub.go
	  6                      ;; dlazy                               : default in gossipsub.go
	  *hbmInterval-ags*          ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60                     ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-ags* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
          ;; TODO : clarify gossipfactor
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-ags*) ;; seenTTL : BC #L124
	  5 ;; opportunisticGraftThreshold
	  *aggregateWeight-ags* ;; topicWeight = aggregateWeight       #L100
	  1/100 ;; MeshMessageDeliveriesDecay  = scoreDecay(1 epoch) #L108
	  1/100 ;; FirstMessageDeliveriesDecay = scoreDecay(1 epoch) #L105
	  63/100 ;; behaviourPenaltyDecay
	  1/100 ;; MeshFailurePenaltyDecay     = scoreDecay(1 epoch) #L114
	  912/1000 ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs) #L116
	  *decayToZero-ags*
	  *slot-duration-ags*
	  ))

(check= t (paramsp *eth-default-aggregate-params-ags*))

(defconst *eth-default-aggregate-subnet-params-ags*
  (params (* 17 *slot-duration-ags*) ;; activationWindow               : #L146
	  *subnet-numsPerSlot-ags*   ;; meshTimeQuantum                : #L136
	  24                     ;; p2cap                          : #L140
	  300                    ;; timeQuantaInMeshCap            : #L137
	  *subnet-subnetWeight-ags*  ;; meshMessageDeliveriesCap       : #L143
	  *subnet-minimumWeight-ags* ;; meshMessageDeliveriesThreshold : #L144
	   *topicCap-ags*             ;; topicCap,          see above (global)
	  -16000                 ;; greyListThreshold, see above (global)
	  8                      ;; d                                   : BC #L120
	  6                      ;; dlow                                : BC #L119
	  12                     ;; dhigh                               : default in gossipsub.go
	  6                      ;; dlazy                               : default in gossipsub.go
	  *hbmInterval-ags*          ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60                     ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-ags* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
          ;; TODO
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-ags*) ;; seenTTL : BC #L124
	  5 ;; OpportunisticGraftThreshold
	  ;; TODO: MeshMessageDeliveriesWindow   = 2 seconds                           #L145
	  *subnet-topicWeight-ags*  ;; topicWeight   = *subnet-topicWeight*                      #L134
	  ;; MeshMessageDeliveriesDecay    = scoreDecay(*subnet-meshDecay* x 1 epoch)  #L142
	  749/1000
	  ;; FirstMessageDeliveriesDecay   = scoreDecay(*subnet-firstDecay* x 1 epoch) #L139
	  316/1000
	  631/1000 ;; behaviourPenaltyDecay
	  ;; MeshFailurePenaltyDecay       = scoreDecay(*subnet-meshDecay* x 1 epoch)  #L148
	  749/1000
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs)                     #L150
	  912/1000
	  *decayToZero-ags*
	  *slot-duration-ags*
	  ))

(check= t (paramsp *eth-default-aggregate-subnet-params-ags*))

(defconst *eth-twp-ags*
  `((AGG . (,*eth-default-agg-weights-ags* . ,*eth-default-aggregate-params-ags*))
    (BLOCKS . (,*eth-default-block-weights-ags* . ,*eth-default-block-params-ags*))
    ;; We can have 0 or more subnet aggregator topics.  For now, let's assume 3.
    (SUB1 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB10 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB11 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB12 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB2 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB3 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB4 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB5 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB6 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB7 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB8 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    (SUB9 . (,*eth-default-agg-subnet-weights-ags*
             . ,*eth-default-aggregate-subnet-params-ags*))
    ))

(check= t (twpp *eth-twp-ags*))

;; ;; Gadget test
;; ; 4.69 seconds realtime, 4.35 seconds runtime
;; (time$
;;  (b* ((attacktopics '(SUB1 SUB2 SUB3))
;;       (alltopics-ag '(AGG BLOCKS SUB1 SUB2 SUB3 SUB4 SUB5 SUB6 SUB7 SUB8 SUB9
;;  SUB10 SUB11 SUB12))
;;       (grp (initialize-group-of-meshpeers '(A B)
;;                                           '(A B)
;;                                           alltopics-ag
;;                                           100))
;;       (evnts (emit-evnts 'A 'B alltopics-ag attacktopics 20 0 18)))
;;     (eth-attack-violations grp evnts evnts 'A 'B attacktopics 0
;;                            *eth-twp-ags* 42 nil)))

#|
"Some Tests with different network configurations"

;; attack on goerli network
; 68.36 seconds realtime, 67.32 seconds runtime
; (6,654,552,064 bytes allocated).
;; (nil t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t)

(time$
 (b* ((attacktopics '(SUB1 SUB2 SUB3))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   *goerli*
                   (alltopics-ag)))
      (evnts (emit-evnts 'P222 'P834 (alltopics-ag) attacktopics 20 0 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P222 'P834 attacktopics 0 *eth-twp-ags* 42 nil)))

;; attack on rinkeby network
; 124.95 seconds realtime, 124.29 seconds runtime
; (25,857,190,080 bytes allocated).
;; (nil t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t)
(time$
 (b* ((attacktopics '(SUB1 SUB2 SUB3))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   *rinkeby*
                   (alltopics-ag)))
      (evnts (emit-evnts 'P256 'P436 (alltopics-ag)
                               attacktopics 20 0 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P256 'P436 attacktopics 0
                          *eth-twp-ags* 42 nil)))


;; attack on ropsten network
; 80.54 seconds realtime, 80.35 seconds runtime
; (11,101,636,128 bytes allocated).
;; (nil t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t)
(time$
 (b* ((attacktopics '(SUB1 SUB2 SUB3))
      (grp (reduce* graph->group 
                    (initialize-group-of-meshpeers '()
                                                   '()
                                                   (topics)
                                                   100)
                    *ropsten*
                    (alltopics-ag)))
      (evnts (emit-evnts 'P256 'P448 (alltopics-ag)
                         attacktopics 20 0 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P256 'P448 attacktopics 0
                          *eth-twp-ags* 42 nil)))

;; attack on goerli network
; 106.51 seconds realtime, 106.27 seconds runtime
; (6,489,955,424 bytes allocated).
(time$
 (b* ((attacktopics '(SUB1 SUB2))
      (grp (reduce* graph->group 
                    (initialize-group-of-meshpeers '()
                                                   '()
                                                   (topics)
                                                   100)
                    *goerli*
                    (alltopics-ag)))
      (evnts (emit-evnts 'P222 'P834 (alltopics-ag)
                         attacktopics 20 0 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P222 'P834 attacktopics 0
                          *eth-twp-ags* 42 nil)))


;; attack on rinkeby network
; 118.49 seconds realtime, 117.96 seconds runtime
; (24,517,137,296 bytes allocated).
;; (nil t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t)
(time$
 (b* ((attacktopics '(SUB1 SUB2))
      (grp (reduce* graph->group 
                    (initialize-group-of-meshpeers '()
                                                   '()
                                                   (topics)
                                                   100)
                    *rinkeby*
                    (alltopics-ag)))
      (evnts (emit-evnts 'P256 'P436 (alltopics-ag)
                         attacktopics 20 0 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P256 'P436 attacktopics 0
                          *eth-twp-ags* 42 nil)))


;; attack on ropsten network
; 82.58 seconds realtime, 82.35 seconds runtime
; (10,707,740,928 bytes allocated).
;; (nil t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t
;;      t t t t t t t t t t t t t t t t t t t t)
(time$
 (b* ((attacktopics '(SUB1 SUB2))
      (grp (reduce* graph->group 
                    (initialize-group-of-meshpeers '()
                                                   '()
                                                   (topics)
                                                   100)
                    *ropsten*
                    (alltopics-ag)))
      (evnts (emit-evnts 'P256 'P448 (alltopics-ag)
                         attacktopics 20 0 18)))
   (eth-attack-violations grp evnts evnts 'P256 'P448 attacktopics 0
                          *eth-twp-ags* 42 nil)))




;; goerli
; 83.36 seconds realtime, 83.15 seconds runtime
; (6,348,026,784 bytes allocated).
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
                    (alltopics-ag)))
      (evnts (emit-evnts 'P222 'P834 (alltopics-ag) attacktopics 20 0 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P222 'P834 attacktopics 0
                          *eth-twp-ags* 42 nil)))


;; rinkeby
; 114.39 seconds realtime, 114.12 seconds runtime
; (23,385,789,744 bytes allocated).
(time$
 (b* ((attacktopics '(SUB1))
      (grp (reduce* graph->group 
                    (initialize-group-of-meshpeers '()
                                                   '()
                                                   (topics)
                                                   100)
                    *rinkeby*
                    (alltopics-ag)))
      (evnts (emit-evnts 'P256 'P436 (alltopics-ag)
                         attacktopics 20 0 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P256 'P436 attacktopics 0
                          *eth-twp-ags* 42 nil)))


; 81.27 seconds realtime, 80.91 seconds runtime
; (10,372,926,704 bytes allocated).
(time$
 (b* ((attacktopics '(SUB1))
      (grp (reduce* graph->group 
                    (initialize-group-of-meshpeers '()
                                                   '()
                                                   (topics)
                                                   100)
                    *ropsten*
                    (alltopics-ag)))
      (evnts (emit-evnts 'P256 'P448 (alltopics-ag)
                               attacktopics 20 0 18)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P256 'P448 attacktopics 0
                          *eth-twp-ags* 42 nil)))

|#
