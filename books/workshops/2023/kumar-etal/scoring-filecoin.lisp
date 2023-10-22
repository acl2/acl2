(in-package "ACL2S")
(in-theory (enable remove-assoc-equal))
(include-book "higher-order")
(include-book "utils")

(def-const *few-seconds* 5)
(def-const *two-minutes* 120)
(def-const *one-minute* 60)
(def-const *one-hour* (* 60 *one-minute*))

(include-book "network")

;; ------------------ File Coin Case Study (github.com/filecoin-project/lotus) ------------------------------

;; GossipSub is my private version forked off of be065ce0510e81d820a2cdb9762e63fd012122ba
;; Libp2p is my private version forked off of 4400328a581babd9a196e71ddffbe996ae7b3b59

(defconst *FC-weights-block*
  '(27/1000 ;; w_1  = time in mesh weight     (#L139)
    5       ;; w_2  = first message deliveries weight   (#L144)
    0       ;; w_3  = mesh message deliveries weight    (disabled)
    0       ;; w_3b = mesh failure penalty weight       (disabled)
    -1000   ;; w_4  = invalid messages weight           (#L172)
    1       ;; w_5  = application-specific score weight (#L265, global)
    -100    ;; w_6  = IP-co-location factor weight      (#L269, global)
    -10))   ;; w_7 = behavioral penalty weight          (#L274, global)

(check= t (weightsp *FC-weights-block*))

;; https://github.com/libp2p/go-libp2p-pubsub/blob/566fdfa6fc1c1bfda9b9d56ccf99142dfc5ef5a7/score_params.go#L280
(definec ScoreParameterDecayWithBase(decay :non-neg-rational base :non-neg-rational decayToZero :non-neg-rational) :non-neg-rational
  (if (equal (* decay base) 0) 0
    (let ((ticks (/ decay base)))
      (expt decayToZero (floor 1 ticks)))))

(definec ScoreParameterDecay(decay :non-neg-rational) :non-neg-rational
  (ScoreParameterDecayWithBase decay 1 (/ 1 100)))

(defconst *FC-params-block*
  ;; https://github.com/filecoin-project/lotus/blob/
  ;;     5416ce54431fff8333b6ef80e86ac1194ef23577/node/modules/lp2p/pubsub.go
  ;;
  ;; 7036636fcfd47ee378614e7105399700585968f3
  ;;
  (params 0  ;; activationWindow         : disabled
          ;; (MeshMessageDeliveriesActivation), legal
	  1   ;; meshTimeQuantum               : #L140
	  100 ;; p2cap                         : #L146 (FirstMessageDeliveriesCap)
	  1   ;; timeQuantaInMeshCap           : #L141
	  0   ;; meshMessageDeliveriesCap      : disabled
	  0   ;; meshMessageDeliveriesThreshold: disabled
	  100000000   ;; topiccap                    : disabled
	  -2500 ;; grayListThreshold           : #L43 (global)
	  8     ;; d                           : #L28 (global)
	  6     ;; dlow                        : #L31 (global)
	  12    ;; dhigh                       : #L32 (global)
	  12    ;; dlazy                       : #L33 (global)
	  1     ;; hbmInterval                 : default in gossipsub.go
	  60    ;; fanoutTTL                   : default in gossipsub.go
	  10    ;; mcacheLen                   : #L36 (global)
	  (/ 1 10) ;; mcacheGsp                : #L37 (gloabl)
	  120   ;; seenTTL                     : defualt (TimeCacheDuration) in pubsub.go
	  (/ 7 2)   ;; opportunisticGraftThreshold : #L45 (global)
          1/10 ;; topicWeight = 0.1                      (#L136)
	  0 ;; meshMessageDeliveriesDecay (does not matter since it's disabled)
	  0 ;; firstMessageDeliveriesDecay (does not matter since it's disabled)
	  (ScoreParameterDecay *one-hour*) ;; behaviourPenaltyDecay (#L275)
	  0 ;; meshFailurePenaltyDecay (does not matter since it's disabled)
	  (ScoreParameterDecay *one-hour*) ;; invalidMessageDeliveriesDecay (#L173)
	  ;; https://github.com/libp2p/go-libp2p-pubsub/blob/566fdfa6fc1c1bfda9b9d56ccf99142dfc5ef5a7/score_params.go#L275
	  (/ 1 100) ;; decayToZero (#L278)
	  1 ;; decayInterval (#L277)
	  ))

(check= t (paramsp *FC-params-block*))
(check= nil (params-legalp *FC-params-block*))

(defconst *FC-weights-msgs*
  '(2778/1000 ;; w_1  = time in mesh weight               (#L180)
    1/2       ;; w_2  = first message deliveries weight   (#L185)
    0       ;; w_3  = mesh message deliveries weight      (disabled)
    0       ;; w_3b = mesh failure penalty weight         (disabled)
    -1000   ;; w_4  = invalid messages weight             (#L206)
    1       ;; w_5  = application-specific score weight   (#L265, global)
    -100    ;; w_6  = IP-co-location factor weight        (#L269, global)
    -10))   ;; w_7 = behavioral penalty weight            (#L274, global)

(check= t (weightsp *FC-weights-msgs*))
(check= t (weightsp *FC-weights-block*))

(defconst *FC-params-msgs*
  (params 0 ;; activationWindow                : disabled
	  1 ;; meshTimeQuantum                 : #L182
	  100 ;; p2cap                         : #L187 (FirstMessageDeliveriesCap)
	  1 ;; timeQuantaInMeshCap             : #L182
	  0 ;; meshMessageDeliveriesCap        : disabled
	  0 ;; meshMessageDeliveriesThreshold  : disabled
	  100000000     ;; topiccap                    : disabled
	  -2500 ;; grayListThreshold           : #L43 (global)
	  8     ;; d                           : #L28 (global)
	  6     ;; dlow                        : #L31 (global)
	  12    ;; dhigh                       : #L32 (global)
	  12    ;; dlazy                       : #L33 (global)
	  1     ;; hbmInterval                 : default in gossipsub.go
	  60    ;; fanoutTTL                   : default in gossipsub.go
	  10    ;; mcacheLen                   : #L36 (global)
	  (/ 1 2)   ;; mcacheGsp                   : #L37 (gloabl)
	  120   ;; seenTTL                     : defualt (TimeCacheDuration) in pubsub.go
	  (/ 7 2)   ;; opportunisticGraftThreshold : #L45 (global)
	  ;; TODO: invalidMessageDeliveriesDecay = 1 hour   (#L207)
          1/10 ;; topicWeight = 0.1                    (#L177)
	  0 ;; meshMessageDeliveriesDecay (disabled)
	  (ScoreParameterDecay (* 10 *one-minute*)) ;; firstMessageDeliveriesDecay (#L186)
	  (ScoreParameterDecay *one-hour*) ;; behaviourPenaltyDecay (#L275)
	  0 ;; meshFailurePenaltyDecay (disabled)
	  (ScoreParameterDecay *one-hour*) ;; invalidMessageDeliveriesDecay
	  (/ 1 100) ;; decayToZero
	  1 ;; decayInterval
	  ))

(check= t (paramsp *FC-params-msgs*))
(check= nil (params-legalp *FC-params-msgs*))

;; this is a twp
(defconst *FC-TPW* `((BLOCKS . (,*FC-weights-block* . ,*FC-params-block*))
                     (MESSAGES   . (,*FC-weights-msgs* . ,*FC-params-msgs*))))
 
;;high values
(defdata lows (range integer (0 <= _ <= 1)))

;;low values
(defdata highs (range integer (500 < _ <= 1000)))

(defdata-subtype lows nat)
(defdata-subtype highs nat)

;; setting badbehaviour as 0
(defun nth-bad-counters-custom (n)
  (tctrs (nth-lows (+ n 3)) (nth-lows (+ n 2))
            (nth-lows (+ n 3)) (nth-lows (+ n 4)) (nth-lows (+ n 7))))

;; keeping bad behaviors 0 as it drops score too much
(defun nth-good-counters-custom (n)
  (tctrs 0 (nth-highs (+ n 2)) (nth-highs (+ n 3)) (nth-highs (+ n 4)) 0))

(defun nth-counters-custom (n)
  (if (== 0 (mod n 2))
      (nth-bad-counters-custom n)
    (nth-good-counters-custom n)))

(defdata-attach tctrs :enumerator nth-counters-custom)

(set-ignore-ok t)
(defun nth-glb-counters-custom (n)
  (declare (irrelevant n))
  (list 0 0 0))

(defdata-attach gctrs :enumerator nth-glb-counters-custom)

;; PTC for peer P1 with FC topics and counters
(property FC-PT-TCTRS-MAP-SAMPL (m-ctrs :tctrs b-ctrs :tctrs)
          (pt-tctrs-mapp `(((P1 . blocks) . ,b-ctrs)
                           ((P1 . messages) . ,m-ctrs)))
          :hints (("Goal" :in-theory (enable pt-tctrs-mapp))))

;; Contribution of P3 and P3b to FC score is 0, for both blocks and messages
(property p3-p3b=0 (tctrs :tctrs wtpm :wp)
          (=> (^ (v (== wtpm (car *fc-tpw*))   ;; blocks
		    (== wtpm (cdar *fc-tpw*))) ;; messages
		 (<= (mget :meshmessagedeliveriesthreshold (cdr wtpm))
		     (mget :meshmessagedeliveriescap (cdr wtpm))))
              (= (+ (* (caddr (car wtpm))
		       (calcp3 (tctrs-meshtime tctrs)
			       (mget :activationwindow (cdr wtpm))
			       (tctrs-meshmessagedeliveries tctrs)
			       (mget :meshmessagedeliveriescap (cdr wtpm))
			       (mget :meshmessagedeliveriesthreshold (cdr wtpm))))
		    (* (cadddr (car wtpm))
		       (calcp3b (tctrs-meshtime tctrs)
				(mget :activationwindow (cdr wtpm))
				(tctrs-meshfailurepenalty tctrs)
				(tctrs-meshmessagedeliveries tctrs)
				(mget :meshmessagedeliveriescap (cdr wtpm))
				(mget :meshmessagedeliveriesthreshold (cdr
								       wtpm)))))
		 0))
          :hints (("Goal" :in-theory (enable twpp wpp weightsp))))

;; With just 1 invalid message, the score contribution due to P4 in topic
;; BLOCKS exceeds sum of maximum possible score due to both topics
(property p4-penalty-too-high-blocks (wtpm :wp)
          (=> (<= (mget :meshmessagedeliveriesthreshold (cdr wtpm))
                  (mget :meshmessagedeliveriescap (cdr wtpm)))
              (< (+ (* (fifth (cadar *fc-tpw*)) ;; blocks
		       (calcP4 1)) ;; 1 invalid message delivery
                    (calcMaxScoreTopic (cdar *fc-tpw*))
                    (calcMaxScoreTopic (cdadr *fc-tpw*)))
		 0)))

;; With just 1 invalid message, the score contribution due to P4 in topic
;; MESSAGES exceeds maximum possible score due to both topics
(property p4-penalty-too-high-messages (wtpm :wp)
          (=> (<= (mget :meshmessagedeliveriesthreshold (cdr wtpm))
                  (mget :meshmessagedeliveriescap (cdr wtpm)))
              (< (+ (* (fifth (cadadr *fc-tpw*)) ;; messages
		       (calcP4 1)) ;; 1 invalid message delivery
                    (calcMaxScoreTopic (cdar *fc-tpw*))
                    (calcMaxScoreTopic (cdadr *fc-tpw*)))
		 0)))




;; (SET-DEBUGGER-ENABLE T)
;; (set-ignore-ok t)
;; (b* ((TOP 'MESSAGES)
;;      (P 'P9)
;;      (PGLB '((P7 1000 0 0)
;;             (P8 1000 0 0)
;;             (P9 1000 0 0)))
;;      (PTC '(((P9 . BLOCKS)
;;              (:0TAG . TCTRS)
;;              (:FIRSTMESSAGEDELIVERIES . 712)
;;          (:INVALIDMESSAGEDELIVERIES . 0)
;;          (:MESHFAILUREPENALTY . 0)
;;          (:MESHMESSAGEDELIVERIES . 718)
;;          (:MESHTIME . 965))
;;         ((P9 . MESSAGES)
;;          (:0TAG . TCTRS)
;;          (:FIRSTMESSAGEDELIVERIES . 0)
;;          (:INVALIDMESSAGEDELIVERIES . 1)
;;          (:MESHFAILUREPENALTY . 1)
;;          (:MESHMESSAGEDELIVERIES . 0)
;;          (:MESHTIME . 1))
;;         ((P10 . BLOCKS)
;;          (:0TAG . TCTRS)
;;          (:FIRSTMESSAGEDELIVERIES . 694)
;;          (:INVALIDMESSAGEDELIVERIES . 0)
;;          (:MESHFAILUREPENALTY . 0)
;;          (:MESHMESSAGEDELIVERIES . 700)
;;          (:MESHTIME . 947))
;;         ((P10 . MESSAGES)
;;          (:0TAG . TCTRS)
;;          (:FIRSTMESSAGEDELIVERIES . 0)
;;          (:INVALIDMESSAGEDELIVERIES . 1)
;;          (:MESHFAILUREPENALTY . 1)
;;          (:MESHMESSAGEDELIVERIES . 0)
;;          (:MESHTIME . 1))
;;         ((P11 . BLOCKS)
;;          (:0TAG . TCTRS)
;;          (:FIRSTMESSAGEDELIVERIES . 682)
;;          (:INVALIDMESSAGEDELIVERIES . 0)
;;          (:MESHFAILUREPENALTY . 0)
;;          (:MESHMESSAGEDELIVERIES . 688)
;;          (:MESHTIME . 935))
;;         ((P11 . MESSAGES)
;;          (:0TAG . TCTRS)
;;          (:FIRSTMESSAGEDELIVERIES . 0)
;;          (:INVALIDMESSAGEDELIVERIES . 1)
;;          (:MESHFAILUREPENALTY . 1)
;;          (:MESHMESSAGEDELIVERIES . 0)
;;          (:MESHTIME . 1)))))
;;   (list (calc-nbr-scores-map ptc pglb *FC-TPW*)
;;         (calcScoreTopic (lookup-tctrs p 'BLOCKS ptc)
;;                         (cdr (assoc-equal top *FC-TPW*)))
;;         (calcScoreTopic (lookup-tctrs p 'MESSAGES ptc)
;;                         (cdr (assoc-equal top *FC-TPW*)))))


;; ;; Topic : Messages
;; ;; Score : -199/2 = -99.5
;; ;; Overall score : 400527/500 = 801

;; ;; (((P9 . 20561/200)
;; ;;   (P10 . -99439/100)
;; ;;   (P11 . -298317/200))

;; ;;all counters 0 : 0

;; ;; 1000 mesh time, 1000 first msg deliveries : 500.027

;; ;; 1000 mesh time, 1000 first msg deliveries, 1 bad behaviour : 400

;; ;; 1000 mesh time, 1000 first msg deliveries, 2 bad behaviours : 100.027

;; ;; 1000 mesh time, 1000 first msg deliveries, 2 bad behaviours, 0 mesh time : 100

;; ;; 1000 mesh time, 80 first msg deliveries, 2 bad behaviours, 0 mesh time : 0


;; (defdata-attach tctrs :enumerator nth-good-counters-custom)

;; (property (ptc :pt-tctrs-map
;; 	       pglb :p-gctrs-map
;; 	       p :peer
;; 	       top :topic
;; 	       delta-p3 :nat
;; 	       delta-p3b :nat
;; 	       delta-p4 :nat
;; 	       delta-p6 :nat
;; 	       delta-p7 :nat)
;;   :proofs? nil
;;   :testing-timeout 600
;;   :CHECK-CONTRACTS? nil
;;   :hyps (^ (member-equal top (strip-cars *FC-TPW*))
;; 	   (member-equal (cons p top) (strip-cars ptc))
;; 	   ;; Require glb indexed by p in pglb to not be empty and thus not return nil
;;            (member-equal p (strip-cars pglb))
;; 	   ;; Require that at least one delta is non-zero
;; 	   (> (+ delta-p3 delta-p3b delta-p4 delta-p6 delta-p7) 0))
;;   ;; Define the new ptc using our deltas
;;   (b* ((tc (lookup-tctrs p top ptc))
;;        (glb (lookup-gctrs p pglb))
;;        (new-tc (update-invalidMessageDeliveries
;; 		(update-meshFailurePenalty
;; 		 (update-meshMessageDeliveries
;; 		  tc
;; 		  (+ (tctrs-meshMessageDeliveries tc) delta-p3))
;; 		 (+ (tctrs-meshFailurePenalty tc) delta-p3b))
;; 		(+ (tctrs-invalidMessageDeliveries tc) delta-p4)))
;;        (new-ptc (put-assoc-equal `(,p . ,top) new-tc ptc))
;;        (new-gctrs`(,(first pglb)
;; 			   ,(+ (second glb) delta-p6)
;; 			   ,(+ (third glb) delta-p7)))
;;        (new-pglb (put-assoc-equal p new-gctrs pglb)))
;;     (> (lookup-score p (calc-nbr-scores-map ptc pglb *FC-TPW*))
;;        (lookup-score p (calc-nbr-scores-map new-ptc new-pglb *FC-TPW*)))))



;; (b* ((DELTA-P7 0)
;;      (DELTA-P6 1)
;;      (DELTA-P4 0)
;;      (DELTA-P3B 1)
;;      (DELTA-P3 1)
;;      (TOP 'BLOCKS)
;;      (P 'P1)
;;      (PGLB '((P1 0 0 0) (P2 0 0 0) (P3 0 0 0)))
;;      (PTC '(((P1 . BLOCKS)
;;          (:0TAG . TCTRS)
;;          (:FIRSTMESSAGEDELIVERIES . 971)
;;          (:INVALIDMESSAGEDELIVERIES . 0)
;;          (:MESHFAILUREPENALTY . 0)
;;          (:MESHMESSAGEDELIVERIES . 977)
;;          (:MESHTIME . 724))
;;         ((P1 . MESSAGES)
;;          (:0TAG . TCTRS)
;;          (:FIRSTMESSAGEDELIVERIES . 718)
;;          (:INVALIDMESSAGEDELIVERIES . 0)
;;          (:MESHFAILUREPENALTY . 0)
;;          (:MESHMESSAGEDELIVERIES . 724)
;;          (:MESHTIME . 971))))
;;      (tc (lookup-tctrs p top ptc))
;;      (glb (lookup-gctrs p pglb))
;;      (new-tc (update-invalidMessageDeliveries
;;               (update-meshFailurePenalty
;;                (update-meshMessageDeliveries
;;                 tc
;;                 (+ (tctrs-meshMessageDeliveries tc) delta-p3))
;;                (+ (tctrs-meshFailurePenalty tc) delta-p3b))
;;               (+ (tctrs-invalidMessageDeliveries tc) delta-p4)))
;;      (new-ptc (put-assoc-equal `(,p . ,top) new-tc ptc))
;;      (new-gctrs`(,(first glb)
;;                          ,(+ (second glb) delta-p6)
;;                          ,(+ (third glb) delta-p7)))
;;      (new-pglb (put-assoc-equal p new-gctrs pglb)))
;;   (list (calc-nbr-scores-map ptc pglb *FC-TPW*)
;;         (calcScoreTopic (lookup-tctrs p 'BLOCKS ptc)
;;                         (cdr (assoc-equal 'BLOCKS *FC-TPW*)))
;;         (calcScoreTopic (lookup-tctrs p 'MESSAGES ptc)
;;                         (cdr (assoc-equal 'MESSAGES *FC-TPW*)))
;;         (lookup-score p (calc-nbr-scores-map ptc pglb *FC-TPW*))
;;         (lookup-score p (calc-nbr-scores-map new-ptc new-pglb *FC-TPW*))))



;;Taking inspiration from FileCoin parameters, i.e. high penalties and
;;satisfying legal param requirements, we come up with good parameters which we
;;hope should satisfy all properties

(defconst *GOOD-params-msgs*
  (params 10 ;; activationWindow                : disabled
	  1 ;; meshTimeQuantum                 : #L182
	  100 ;; p2cap                         : #L187 (FirstMessageDeliveriesCap)
	  1 ;; timeQuantaInMeshCap             : #L182
	  10 ;; meshMessageDeliveriesCap      
	  2 ;; meshMessageDeliveriesThreshold 
	  10     ;; topiccap                    
	  -2500 ;; grayListThreshold           : #L43 (global)
	  8     ;; d                           : #L28 (global)
	  6     ;; dlow                        : #L31 (global)
	  12    ;; dhigh                       : #L32 (global)
	  12    ;; dlazy                       : #L33 (global)
	  1     ;; hbmInterval                 : default in gossipsub.go
	  60    ;; fanoutTTL                   : default in gossipsub.go
	  10    ;; mcacheLen                   : #L36 (global)
	  (/ 1 2)   ;; mcacheGsp                   : #L37 (gloabl)
	  120   ;; seenTTL                     : defualt (TimeCacheDuration) in pubsub.go
	  (/ 7 2)   ;; opportunisticGraftThreshold : #L45 (global)
	  ;; TODO: invalidMessageDeliveriesDecay = 1 hour   (#L207)
          1/2 ;; topicWeight = 0.5                   (#L177)
	  9/10 ;; meshMessageDeliveriesDecay
	  (ScoreParameterDecay (* 10 *one-minute*)) ;; firstMessageDeliveriesDecay (#L186)
	  (ScoreParameterDecay *one-hour*) ;; behaviourPenaltyDecay (#L275)
	  9/10 ;; meshFailurePenaltyDecay
	  (ScoreParameterDecay *one-hour*) ;; invalidMessageDeliveriesDecay
	  1/100 ;; decayToZero
	  1 ;; decayInterval
	  ))


(defconst *GOOD-params-block*
  ;; https://github.com/filecoin-project/lotus/blob/
  ;;     5416ce54431fff8333b6ef80e86ac1194ef23577/node/modules/lp2p/pubsub.go
  ;;
  ;; 7036636fcfd47ee378614e7105399700585968f3
  ;;
  (params 10  ;; activationWindow         : disabled
          ;; (MeshMessageDeliveriesActivation), legal
	  1   ;; meshTimeQuantum               : #L140
	  100 ;; p2cap                         : #L146 (FirstMessageDeliveriesCap)
	  1   ;; timeQuantaInMeshCap           : #L141
          10   ;; meshMessageDeliveriesCap      : disabled
	  2   ;; meshMessageDeliveriesThreshold: disabled
	  100  ;; topiccap                    : disabled
	  -2500 ;; grayListThreshold           : #L43 (global)
	  8     ;; d                           : #L28 (global)
	  6     ;; dlow                        : #L31 (global)
	  12    ;; dhigh                       : #L32 (global)
	  12    ;; dlazy                       : #L33 (global)
	  1     ;; hbmInterval                 : default in gossipsub.go
	  60    ;; fanoutTTL                   : default in gossipsub.go
	  10    ;; mcacheLen                   : #L36 (global)
	  1/10 ;; mcacheGsp                : #L37 (gloabl)
	  120   ;; seenTTL                     : defualt (TimeCacheDuration) in pubsub.go
	  7/2   ;; opportunisticGraftThreshold : #L45 (global)
          1/2 ;; topicWeight = 0.5                      (#L136)
	  9/10  ;; meshMessageDeliveriesDecay (does not matter since it's disabled)
	  (ScoreParameterDecay (* 10 *one-minute*)) ;; firstMessageDeliveriesDecay (does not matter since it's disabled)
	  (ScoreParameterDecay *one-hour*) ;; behaviourPenaltyDecay (#L275)
	  9/10 ;; meshFailurePenaltyDecay (does not matter since it's disabled)
	  (ScoreParameterDecay *one-hour*) ;; invalidMessageDeliveriesDecay (#L173)
	  ;; https://github.com/libp2p/go-libp2p-pubsub/blob/566fdfa6fc1c1bfda9b9d56ccf99142dfc5ef5a7/score_params.go#L275
	  1/100 ;; decayToZero (#L278)
	  1 ;; decayInterval (#L277)
	  ))

(check= t (paramsp *GOOD-params-block*))
(check= t (paramsp *GOOD-params-msgs*))

(defconst *GOOD-weights-msgs*
  '(27/1000 ;; w_1  = time in mesh weight     (#L139)
    5       ;; w_2  = first message deliveries weight   (#L144)
    -1000       ;; w_3  = mesh message deliveries weight    (disabled)
    -1000       ;; w_3b = mesh failure penalty weight       (disabled)
    -1000   ;; w_4  = invalid messages weight           (#L172)
    1       ;; w_5  = application-specific score weight (#L265, global)
    -100    ;; w_6  = IP-co-location factor weight      (#L269, global)
    -10))   ;; w_7 = behavioral penalty weight          (#L274, global)

(defconst *GOOD-weights-block*
  '(27/1000 ;; w_1  = time in mesh weight     (#L139)
    5       ;; w_2  = first message deliveries weight   (#L144)
    -1000       ;; w_3  = mesh message deliveries weight    (disabled)
    -1000       ;; w_3b = mesh failure penalty weight       (disabled)
    -1000   ;; w_4  = invalid messages weight           (#L172)
    1       ;; w_5  = application-specific score weight (#L265, global)
    -100    ;; w_6  = IP-co-location factor weight      (#L269, global)
    -10))   ;; w_7 = behavioral penalty weight          (#L274, global)

(check= t (weightsp *GOOD-weights-block*))
(check= t (weightsp *GOOD-weights-msgs*))

(defconst *good-twp*
  `((MSGS . (,*GOOD-weights-msgs* . ,*GOOD-params-msgs*))
    (BLOCK . (,*GOOD-weights-block* . ,*GOOD-params-block*))))

(check= t (twpp *good-twp*))

;; PTC for peer P1 with GOOD topics and counters
(property GOOD-PT-TCTRS-MAP-SAMPL (m-ctrs :tctrs b-ctrs :tctrs)
          (pt-tctrs-mapp `(((P1 . MSGS) . ,b-ctrs)
                           ((P1 . BLOCK) . ,m-ctrs)))
          :hints (("Goal" :in-theory (enable pt-tctrs-mapp))))


(property p3-penalty-too-high-good-blocks ()
          (< (+ (* (third (cadar *good-twp*))
                   (calcP3 1000 (params-activationWindow (cddar *good-twp*)) 
                           1 ;; 1  < 2
                           (params-meshMessageDeliveriesCap (cddar *good-twp*))
                           (params-meshMessageDeliveriesThreshold (cddar *good-twp*)))) ;; 1 invalid message delivery
                (calcMaxScoreTopic (cdar *good-twp*))
                (calcMaxScoreTopic (cdadr *good-twp*)))
             0))

;; With just 1 invalid message, the score contribution due to P4 in topic
;; BLOCKS exceeds sum of maximum possible score due to both topics
(property p4-penalty-too-high-good-blocks (wtpm :wp)
          (=> (<= (mget :meshmessagedeliveriesthreshold (cdr wtpm))
                  (mget :meshmessagedeliveriescap (cdr wtpm)))
              (< (+ (* (fifth (cadar *good-twp*)) ;; blocks
		       (calcP4 1)) ;; 1 invalid message delivery
                    (calcMaxScoreTopic (cdar *good-twp*))
                    (calcMaxScoreTopic (cdadr *good-twp*)))
		 0)))

;; With just 1 invalid message, the score contribution due to P4 in topic
;; MESSAGES exceeds maximum possible score due to both topics
(property p4-penalty-too-high-good-messages (wtpm :wp)
          (=> (<= (mget :meshmessagedeliveriesthreshold (cdr wtpm))
                  (mget :meshmessagedeliveriescap (cdr wtpm)))
              (< (+ (* (fifth (cadadr *good-twp*)) ;; messages
		       (calcP4 1)) ;; 1 invalid message delivery
                    (calcMaxScoreTopic (cdar *good-twp*))
                    (calcMaxScoreTopic (cdadr *good-twp*)))
		 0)))

;; ------------------------------------------------------------------------------------
;; Property 1
;; ------------------------------------------------------------------------------------

(property (ptc :pt-tctrs-map pcm :p-gctrs-map p :peer top :topic)
	  :proofs? nil
          :TESTING-TIMEOUT 600
	  :hyps  (^ (member-equal top (strip-cars *good-twp*))
	      (member-equal (cons p top) (strip-cars ptc))
	      (> (lookup-score p (calc-nbr-scores-map ptc pcm *good-twp*)) 0))
	   (> (calcScoreTopic (lookup-tctrs p top ptc) (cdr (assoc-equal top *good-twp*)))
              0))

;; ------------------------------------------------------------------------------------
;; Counterexamples for Property 2
;; ------------------------------------------------------------------------------------

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
  :hyps (^ (member-equal top (strip-cars *good-twp*))
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
    (> (lookup-score p (calc-nbr-scores-map ptc pglb *good-twp*))
       (lookup-score p (calc-nbr-scores-map new-ptc pglb *good-twp*)))))


;; ------------------------------------------------------------------------------------
;; Counterexamples for Property 3
;; ------------------------------------------------------------------------------------

(property
   (imd mmd mt fmd mfp p :non-neg-rational wtpm :wp)
   :check-contracts? nil
   :proofs? nil
   (=> (^ (== wtpm (cdr (assoc-equal 'MSGS *good-TWP*)))
          (>= (params-meshMessageDeliveriesCap (cdr wtpm))
              (params-meshMessageDeliveriesThreshold (cdr wtpm)))
          (> mt (params-activationWindow (cdr wtpm))))
       (>= (calcScoreTopic (tctrs imd mmd  (+ p mt) fmd mfp) wtpm)
           (calcScoreTopic (tctrs imd mmd  mt fmd mfp) wtpm))))
