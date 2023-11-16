; cert-flags: ? t :ttags :all :skip-proofs-okp t

(in-package "ACL2S")
(include-book "attack")

;; Setup TWP for AG3

(definec alltopics-ag2 () :lot
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

(defconst *decayToZero-ag2* 1/100)

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     shared/params/config.go#L123

(defconst *seconds-per-slot-ag2* 1) ;; ARBITRARY 
(defconst *one-epoch-duration-ag2* 1) ;; ARBITRARY 

(defconst *aggregateWeight-ag2* (/ 1 2)) ;; weight for aggregate topic, see #L100
(defconst *beaconBlockWeight-ag2* (/ 8 10)) ;; weight for beacon topic, see #L77

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/gossip_scoring_params.go#L154
(defconst *slot-duration-ag2* (* *seconds-per-slot-ag2* 1))

;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;    shared/params/config.go#L48
(defconst *slots-per-epoch-ag2* 10) ;; ARBITRARY 
(defconst *blocks-per-epoch-ag2* *slots-per-epoch-ag2*) ;; #L75
(defconst *decay-epoch-ag2* 5) ;; #L74

;; In line number comments, if I write BC, I am referring to:
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/pubsub.go

;; If I write SERV, I am referring to:
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     beacon-chain/p2p/service.go

;; In all other cases, as indicated previously, I am referring to gossip_scoring_params.go.

;; I assume all times are given in units of 1 second ...

(defconst *enable-larger-gossip-history-ag2* 'nil)

(defconst *hbmInterval-ag2* (/ 700 1000))

(defconst *topicCap-ag2* (+ 32 (/ 72 100)))

(defconst *comm-count-per-slot-ag2* 10) ;; ARBITRARY - refer to #L173 ... they have not decided yet!
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;;     shared/params/config.go#L123
(defconst *target-aggregators-per-committee-ag2* 5) ;; ARBITRARY
(defconst *aggregators-per-slot-ag2* (* *comm-count-per-slot-ag2* *target-aggregators-per-committee-ag2*)) ;; #L1871
(defconst *agg-per-epoch-ag2* (* *aggregators-per-slot-ag2* *slots-per-epoch-ag2*))
(defconst *attestationTotalWeight-ag2* 1) ;; #L23
;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
;; shared/params/network_config.go#L40
(defconst *AttestationSubnetCount-ag2* (- (len (alltopics-ag2)) 2))         ;; ARBITRARY 
(defconst *MinGenesisActiveValidatorCount-ag2* 300) ;; ARBITRARY -----------------|
;; -------> but currently needs to be divisible by 50 x attestationSubnetCount.

(defconst *subnet-topicWeight-ag2* (/ *attestationTotalWeight-ag2* *AttestationSubnetCount-ag2*)) ;; #L121
(defconst *activeValidators-ag2* *MinGenesisActiveValidatorCount-ag2*) ;; #L169
(defconst *subnet-subnetWeight-ag2* (/ *activeValidators-ag2* *AttestationSubnetCount-ag2*)) ;; #L122
(defconst *subnet-minimumWeight-ag2* (/ *subnet-subnetWeight-ag2* 50)) ;; #L123
(defconst *subnet-numsPerSlot-ag2* (floor *subnet-subnetWeight-ag2* *slots-per-epoch-ag2*)) ;; #L124
(defconst *subnet-comsPerSlot-ag2* *comm-count-per-slot-ag2*) ;; #L125
(defconst *subnet-exceedsThreshold-ag2*
  (>= *subnet-comsPerSlot-ag2*
      (* 2 (/ *AttestationSubnetCount-ag2* *slots-per-epoch-ag2*)))) ;; #L126
(defconst *subnet-firstDecay-ag2* (if *subnet-exceedsThreshold-ag2* 4 1)) ;; #L127, 130
(defconst *subnet-meshDecay-ag2* (if *subnet-exceedsThreshold-ag2* 16 4)) ;; #L128, 131

(defconst *eth-default-block-weights-ag2*
  (weights (/ 324 10000)  ;; w_1  = time in mesh weight                (#L78)
           1              ;; w_2  = first message deliveries weight    (#L81)
           (/ -717 1000)  ;; w_3  = mesh message deliveries weight     (#L84)
           (/ -717 1000)  ;; w_3b = mesh failure penalty weight        (#L90)
           (- -140 (/ 4475 10000)) ;; w_4  = invalid messages weight   (#L92)
           1       ;; w_5  = application-specific score weight         (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-block-weights-ag2*))

(defconst *eth-default-agg-weights-ag2*
  (weights (/ 324 10000) ;; w_1  = time in mesh weight              (#L101)
           (/ 128 1000)  ;; w_2  = first message deliveries weight  (#L104)
           (/ -64 1000)  ;; w_3  = mesh message deliveries weight   (#L107)
           (/ -64 1000)  ;; w_3b = mesh failure penalty weight      (#L113)
           (- -140 (/ 4475 10000)) ;; w_4 = invalid messages weight (#L115)
           1             ;; w_5 = application-specific score weight    (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-agg-weights-ag2*))

(defconst *eth-default-agg-subnet-weights-ag2*
  (weights (/ 324 10000) ;; w_1 = time in mesh weight                  (#L134)
           (/ 955 1000)  ;; w_2 = first message deliveries weight      (#L138)
           (- -37 (/ 55 100)) ;; w_3  = mesh message deliveries weight (#L141)
           (- -37 (/ 55 100)) ;; w_3b = mesh failure penalty weight    (#L147)
           -4544              ;; w_4 = invalid messages weight 
           1       ;; w_5  = application-specific score weight         (#L43, global)
           (- -35 (/ 11 100))   ;; w_6  = IP-co-location factor weight (#L44, global)
           (- -15 (/ 92 100)))) ;; w_7 = behavioral penalty weight     (#L47, global)

(check= t (weightsp *eth-default-agg-subnet-weights-ag2*))

;; ;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L162
;; (definecd scoreDecay(x :non-neg-rational) :non-neg-rational
;;   (b* (((when (= x 0)) 0)
;;        (numOfTimes (/ x *slot-duration*)))
;;     3/4))
;;     ;;(expt *decayToZero-ag2* (floor 1 numOfTimes))))

;; Currently failing ...
(defconst *eth-default-block-params-ag2*
  (params 4               ;; activationWindow    : #L89 aka MeshMessageDeliveriesActivation
	  *slot-duration-ag2* ;; meshTimeQuantum     : #L79
	  23              ;; p2cap               : #L83 aka FirstMessageDeliveriesCap
	  300             ;; timeQuantaInMeshCap : #L80
	  (* *blocks-per-epoch-ag2*
	     *decay-epoch-ag2*) ;; meshMessageDeliveriesCap : #L86
	  ;; meshMessageDeliveriesThreshold             : #L87
	  (/ (* *blocks-per-epoch-ag2* *decay-epoch-ag2*) 10)
	  *topicCap-ag2*        ;; topiccap          : #L39 (global)
	  -16000            ;; greyListThreshold : #L33 (global)
	  8                 ;; d                 : BC #L120
	  6                 ;; dlow              : BC #L119
	  12                ;; dhigh             : default in gossipsub.go
	  6                 ;; dlazy             : default in gossipsub.go
	  *hbmInterval-ag2* ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60 ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-ag2* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-ag2*) ;; seenTTL       : BC #L124
	  ;; https://github.com/silesiacoin/prysm-spike/blob/
	  ;; d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/beacon-chain/p2p/gossip_scoring_params.go#L35
	  5 ;; opportunisticGraftThreshold
	  ;; Let scoreDecay(x) = decayToZero^(1/(x/oneSlotDuration)).  Then, starting at:
	  ;;
	  ;; https://github.com/silesiacoin/prysm-spike/blob/d5ac70f0406b445a276ee61ba10fdf0eb6aafa0f/
	  ;;     beacon-chain/p2p/gossip_scoring_params.go#L73
	  ;;
	  *beaconBlockWeight-ag2*
	  ;; MeshMessageDeliveriesDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  398/1000
	  ;; FirstMessageDeliveriesDecay = scoreDecay(20 * oneEpochDuration)
	  794/1000
	  63/100 ;; behaviourPenaltyDecay
	  ;;  MeshFailurePenaltyDecay = scoreDecay(decayEpoch * oneEpochDuration)
	  398/1000
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 * oneEpochDuration)
	  912/1000
	  *decayToZero-ag2* ;; decayToZero
	  *slot-duration-ag2* ;; decayInterval
	  ))

(check= t (paramsp *eth-default-block-params-ag2*))

(defconst *eth-default-aggregate-params-ag2*
  (params (* 32 *slot-duration-ag2*) ;; activationWindow               : #L112
	  *slot-duration-ag2*        ;; meshTimeQuantum                : #L102
	  179                    ;; p2cap                          : #L106
	  300                    ;; timeQuantaInMeshCap            : #L103
	  *agg-per-epoch-ag2*        ;; meshMessageDeliveriesCap       : #L109
	  (/ *agg-per-epoch-ag2* 50) ;; meshMessageDeliveriesThreshold : #L110
	  *topicCap-ag2*             ;; topicCap,          see above (global)
	  -16000                 ;; greyListThreshold, see above (global)
	  8                      ;; d                                   : BC #L120
	  6                      ;; dlow                                : BC #L119
	  12                     ;; dhigh                               : default in gossipsub.go
	  6                      ;; dlazy                               : default in gossipsub.go
	  *hbmInterval-ag2*          ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60                     ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-ag2* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
          ;; TODO : clarify gossipfactor
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-ag2*) ;; seenTTL : BC #L124
	  5 ;; opportunisticGraftThreshold
	  *aggregateWeight-ag2* ;; topicWeight = aggregateWeight       #L100
	  1/100 ;; MeshMessageDeliveriesDecay  = scoreDecay(1 epoch) #L108
	  1/100 ;; FirstMessageDeliveriesDecay = scoreDecay(1 epoch) #L105
	  63/100 ;; behaviourPenaltyDecay
	  1/100 ;; MeshFailurePenaltyDecay     = scoreDecay(1 epoch) #L114
	  912/1000 ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs) #L116
	  *decayToZero-ag2*
	  *slot-duration-ag2*
	  ))

(check= t (paramsp *eth-default-aggregate-params-ag2*))

(defconst *eth-default-aggregate-subnet-params-ag2*
  (params (* 17 *slot-duration-ag2*) ;; activationWindow               : #L146
	  *subnet-numsPerSlot-ag2*   ;; meshTimeQuantum                : #L136
	  24                     ;; p2cap                          : #L140
	  300                    ;; timeQuantaInMeshCap            : #L137
	  *subnet-subnetWeight-ag2*  ;; meshMessageDeliveriesCap       : #L143
	  *subnet-minimumWeight-ag2* ;; meshMessageDeliveriesThreshold : #L144
	   *topicCap-ag2*             ;; topicCap,          see above (global)
	  -16000                 ;; greyListThreshold, see above (global)
	  8                      ;; d                                   : BC #L120
	  6                      ;; dlow                                : BC #L119
	  12                     ;; dhigh                               : default in gossipsub.go
	  6                      ;; dlazy                               : default in gossipsub.go
	  *hbmInterval-ag2*          ;; hbmInterval (aka HeartbeatInterval) : BC #L118
	  60                     ;; fanoutTTL (defaults to GossipSubFanoutTTL) : default in gossipsub.go
	  ;; mcacheLen (aka GossipSubHistoryLength) (see below)
	  (if *enable-larger-gossip-history-ag2* 12 6) ;; BC #L122, 130, 131
	  ;; mcacheGsp (aka GossipFactor) (defaults to GossipSubGossipFactor)
          ;; (see below)
          ;; TODO
	  (/ 1 1) ;; default in gossipsub.go
	  (* 500 *hbmInterval-ag2*) ;; seenTTL : BC #L124
	  5 ;; OpportunisticGraftThreshold
	  ;; TODO: MeshMessageDeliveriesWindow   = 2 seconds                           #L145
	  *subnet-topicWeight-ag2*  ;; topicWeight   = *subnet-topicWeight*                      #L134
	  ;; MeshMessageDeliveriesDecay    = scoreDecay(*subnet-meshDecay* x 1 epoch)  #L142
	  749/1000
	  ;; FirstMessageDeliveriesDecay   = scoreDecay(*subnet-firstDecay* x 1 epoch) #L139
	  316/1000
	  631/1000 ;; behaviourPenaltyDecay
	  ;; MeshFailurePenaltyDecay       = scoreDecay(*subnet-meshDecay* x 1 epoch)  #L148
	  749/1000
	  ;; InvalidMessageDeliveriesDecay = scoreDecay(50 epochs)                     #L150
	  912/1000
	  *decayToZero-ag2*
	  *slot-duration-ag2*
	  ))

(check= t (paramsp *eth-default-aggregate-subnet-params-ag2*))

(defconst *eth-twp-ag2*
  `((AGG . (,*eth-default-agg-weights-ag2* . ,*eth-default-aggregate-params-ag2*))
    (BLOCKS . (,*eth-default-block-weights-ag2* . ,*eth-default-block-params-ag2*))
    ;; We can have 0 or more subnet aggregator topics.  For now, let's assume 3.
    (SUB1 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB10 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB11 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB12 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB2 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB3 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB4 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB5 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB6 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB7 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB8 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    (SUB9 . (,*eth-default-agg-subnet-weights-ag2*
             . ,*eth-default-aggregate-subnet-params-ag2*))
    ))

(check= t (twpp *eth-twp-ag2*))


#|
;; Gadget test
(time$
 (b* ((ticks 100)
      (attacktopics '(SUB1 SUB2 SUB3))
      (alltopics-ag2 '(AGG BLOCKS SUB1 SUB2 SUB3 SUB4 SUB5 SUB6 SUB7 SUB8 SUB9
 SUB10 SUB11 SUB12))
      (grp (initialize-group-of-meshpeers '(A B)
                                          '(A B)
                                          alltopics-ag2
                                          100))
      (evnts (emit-evnts-ticks 'A 'B alltopics-ag2 attacktopics 20 0 18 ticks)))
    (eth-attack-violations grp evnts 'A 'B attacktopics (* 10 (len evnts))
                           *eth-twp-ag2* 42 nil)))

|#



;; we will now create an eclipse attack
(skip-proofs
 ;; emit attack events from p1 to p2, in the attacked topic top
 (definecd emit-evnts-ps (ps :lop p2 :peer ts ats :lot n m elapsed :nat)
   :loev
   (match ps
     (() `((,p2 HBM ,elapsed)))
     ((p . rst) (app
		 (emit-meshmsgdeliveries-peer-topics p p2 (set-difference-equal ts ats) n)
		 (emit-meshmsgdeliveries-peer-topics p p2 ats m)
		 (emit-evnts-ps rst p2 ts ats n m elapsed))))))

#|
"Some Tests with different network configurations"
;; attack on goerli network
; 43.51 seconds realtime, 37.49 seconds runtime
; (107,992,054,352 bytes allocated).
(time$
 (b* ((ticks 100)
      (attacktopics '(SUB1 SUB2))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   *goerli*
                   (alltopics-ag2)))
      (evnts (emit-evnts-ticks 'P222 'P834 (alltopics-ag2)
                               attacktopics 20 0 18 ticks)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P222 'P834 attacktopics (* 10 (len evnts))
                          *eth-twp-ag2* 42 nil)))


;; attack on rinkeby network
; 110.07 seconds realtime, 101.16 seconds runtime
; (280,513,736,960 bytes allocated).
(time$
 (b* ((ticks 100)
      (attacktopics '(SUB1 SUB2))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   *rinkeby*
                   (alltopics-ag2)))
      (evnts (emit-evnts-ticks 'P256 'P436 (alltopics-ag2)
                               attacktopics 20 0 18 ticks)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P256 'P436 attacktopics (* 10 (len evnts))
                          *eth-twp-ag2* 42 nil)))


;; attack on ropsten network
; 23.78 seconds realtime, 22.07 seconds runtime
; (66,255,058,912 bytes allocated).
(time$
 (b* ((ticks 100)
      (attacktopics '(SUB1 SUB2))
      (grp (reduce* graph->group 
                   (initialize-group-of-meshpeers '()
                                                  '()
                                                  (topics)
                                                  100)
                   *ropsten*
                   (alltopics-ag2)))
      (evnts (emit-evnts-ticks 'P256 'P448 (alltopics-ag2)
                               attacktopics 20 0 18 ticks)))
   ;; P222 is attacker, P834 is observer who records violations
   (eth-attack-violations grp evnts evnts 'P256 'P448 attacktopics (* 10 (len evnts))
                          *eth-twp-ag2* 42 nil)))
|#
