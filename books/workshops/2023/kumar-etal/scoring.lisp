(in-package "ACL2S")
(include-book "higher-order")
(include-book "utils")

(def-const *few-seconds* 5)
(def-const *two-minutes* 120)

(defdata peer symbol)
(defdata lop (listof peer))
; Already defined. See 
(defdata frac (range rational (0 <= _ <= 1)))

(defdata-subtype neg-rational rational)
(defdata-subtype non-neg-rational rational)
(defdata-subtype pos-rational rational)
(defdata-subtype frac rational)

(property frac-type (x :frac)
  (^ (rationalp x)
     (<= 0 x)
     (<= x 1))
  :rule-classes :forward-chaining)

(in-theory (disable fracp))

(definec nth-peer-custom (n :nat) :peer
  (intern-in-package-of-symbol
   (concatenate 'string "P" (str::nat-to-dec-string n))
   'APP))

(definec gen-peers (b n :nat) :lop
  (match n
    (0 '())
    (& (cons (nth-peer-custom b)
             (gen-peers (1+ b) (1- n))))))

(defdata-attach peer :enumerator nth-peer-custom)

;; Generates n peers
(create-map* (lambda (n) (nth-peer-custom n))
             nat-listp
             lopp
             (:name mk-peers))

(definec topics () :tl
  ;; topics in FILECOIN
; '(BLOCKS MESSAGES))
  ;; sample topics 
; FM SE SEC DS PL PS NT))
  ;; topics in ETH-2.0, has to be in ascending order because we construct maps
  '(AGG BLOCKS SUB1 SUB2 SUB3))  

(definec nth-topic-custom (n :nat) :symbol
  (nth (mod n (len (topics))) (topics)))

(definec topicp (top :all) :bool
  (symbolp top))

(register-type topic
  :predicate topicp
  :enumerator nth-topic-custom)

(defdata lot (listof topic))

;; Counters per topic
(defdata tctrs
  (record (invalidMessageDeliveries . non-neg-rational)
          (meshMessageDeliveries    . non-neg-rational)
          (meshTime                 . non-neg-rational)
          (firstMessageDeliveries   . non-neg-rational)
          (meshFailurePenalty       . non-neg-rational)))

(property tctrs-check3 (tc :tctrs)
  (^ (<= 0 (mget :meshtime tc))
     (<= 0 (mget :meshfailurepenalty tc))
     (<= 0 (mget :firstmessagedeliveries tc))
     (<= 0 (mget :invalidmessagedeliveries tc))
     (<= 0 (mget :meshmessagedeliveries tc)))
  :hints (("goal" :in-theory (enable tctrsp)))
  :rule-classes :linear)

(definecd new-tctrs () :tctrs
  (tctrs 0 0 0 0 0))

;; pt-tctrs-map keeps track of tctrs per peer per topic
(defdata pt (cons peer topic))
(defdata lopt (listof pt))

;; Pete: try making this into a map and use mget/ mset instead and do
;; this for all similar alistof types.
(defdata pt-tctrs-map (map pt tctrs))


(defun pt-tctrs-topic (peer tops n acc)
  (if (endp tops)
      acc
    (pt-tctrs-topic peer
                    (cdr tops)
                    (1+ n)
                    (mset (cons peer (car tops))
                          (nth-tctrs n)
                          acc))))

(defun mk-ptc (tops peers n acc)
  (if (endp peers)
      acc
    (mk-ptc tops (cdr peers) (+ (* (len peers) (len (topics))) n)
            (pt-tctrs-topic (car peers) tops n acc))))

(defun nth-pt-tctrs-map-custom (n)
  (mk-ptc (topics) (map* mk-peers (natlist-from n 3)) n nil))

;; (property mk-ptc-pt-tctrs-mapp (n :nat)
;;           ;:proofs? nil
;;           :check-contracts? nil
;;           (pt-tctrs-mapp (nth-pt-tctrs-map-custom n)))

(defdata-attach pt-tctrs-map :enumerator
  nth-pt-tctrs-map-custom)

;; Global counters : counters across all topics
;; P5, P6 and P7
;; Pete: make this a record and do for all such types that are lists.
(defdata gctrs
  (record (apco . rational)
          (ipco . non-neg-rational)
          (bhvo . non-neg-rational)))

(property gctrs-check3 (gc :gctrs)
  (^ (<= 0 (mget :ipco gc))
     (<= 0 (mget :bhvo gc)))
  :hints (("goal" :in-theory (enable gctrsp)))
  :rule-classes :linear)

(definecd new-gctrs () :gctrs
  (gctrs 0 0 0))

;; Unlike tctrs, P5, P6 and P7 are only per-peer
(defdata p-gctrs-map (map peer gctrs))

(defun mk-pc (peers n acc)
  (if (endp peers)
      acc
    (mk-pc (cdr peers) (+ n 1) (mset (car peers) (nth-gctrs n) acc))))

(defun nth-p-gctrs-map-custom (n)
  (mk-pc (map* mk-peers (natlist-from n 3)) n nil))

(defdata-attach p-gctrs-map :enumerator nth-p-gctrs-map-custom)

;;maps Peers -> Scores
(defdata peer-rational-map (map peer rational))

;; functions to affect change in individual tctrs.
;; multiple tctrs can be updated by function composition.
(definecd update-invalidMessageDeliveries
  (tctrs :tctrs invalidMessageDeliveries :non-neg-rational) :tctrs
  (mset :invalidMessageDeliveries invalidMessageDeliveries tctrs))

(definecd increment-invalidMessageDeliveries (cs :tctrs) :tctrs
  (update-invalidMessageDeliveries cs (+ 1 (tctrs-invalidMessageDeliveries cs))))

(definecd update-meshMessageDeliveries
  (tctrs :tctrs meshMessageDeliveries :non-neg-rational) :tctrs
  (mset :meshMessageDeliveries meshMessageDeliveries tctrs))

(definecd increment-meshMessageDeliveries (cs :tctrs) :tctrs
  (update-meshMessageDeliveries cs (+ 1 (tctrs-meshMessageDeliveries cs))))

(definecd update-meshTime (tctrs :tctrs meshTime :non-neg-rational) :tctrs
  (mset :meshTime meshTime tctrs))

(definecd update-firstMessageDeliveries
  (tctrs :tctrs firstMessageDeliveries :non-neg-rational) :tctrs
  (mset :firstMessageDeliveries firstMessageDeliveries tctrs))

(definecd increment-firstMessageDeliveries (cs :tctrs) :tctrs
  (update-firstMessageDeliveries cs (+ 1 (tctrs-firstMessageDeliveries cs))))

(definecd update-meshFailurePenalty
  (tctrs :tctrs meshFailurePenalty :non-neg-rational) :tctrs
  (mset :meshFailurePenalty meshFailurePenalty tctrs))

(definecd increment-meshFailurePenalty (cs :tctrs) :tctrs
  (update-meshFailurePenalty cs (+ 1 (tctrs-meshFailurePenalty cs))))

(defdata params
  (record (activationWindow                 . nat)
          (meshTimeQuantum                  . pos)
          (p2cap                            . nat)
          (timeQuantaInMeshCap              . nat)
          (meshMessageDeliveriesCap         . pos-rational)
          (meshMessageDeliveriesThreshold   . pos-rational)
          (topiccap                         . rational)
          ;;^^  NOTE - this is actually global, needs to be same across topics.
          (grayListThreshold                . rational)
          (d                                . nat)
          (dlow                             . nat)
          (dhigh                            . nat)
          (dlazy                            . nat)
          (hbmInterval                      . pos-rational)
          (fanoutTTL                        . pos-rational)
          (mcacheLen                        . pos)
          (mcacheGsp                        . non-neg-rational)
          (seenTTL                          . non-neg-rational)
          (opportunisticGraftThreshold      . non-neg-rational)
          (topicWeight                      . non-neg-rational)
          (meshMessageDeliveriesDecay       . frac)
          (firstMessageDeliveriesDecay      . frac)
          (behaviourPenaltyDecay            . frac)
          (meshFailurePenaltyDecay          . frac)
          (invalidMessageDeliveriesDecay    . frac)
          (decayToZero                      . frac)
          (decayInterval                    . pos-rational)))

(defdata params-legal
  (record (activationWindow                 . nat)
          (meshTimeQuantum                  . pos)
          (p2cap                            . nat)
          (timeQuantaInMeshCap              . nat)
          (meshMessageDeliveriesCap         . pos-rational)
          (meshMessageDeliveriesThreshold   . pos-rational)
          (topiccap                         . rational)
          ;;^^  NOTE - this is actually global, needs to be same across topics.
          (grayListThreshold                . rational)
          (d                                . nat)
          (dlow                             . nat)
          (dhigh                            . nat)
          (dlazy                            . nat)
          (hbmInterval                      . pos-rational)
          (fanoutTTL                        . pos-rational)
          (mcacheLen                        . pos)
          (mcacheGsp                        . non-neg-rational)
          (seenTTL                          . non-neg-rational)
          (opportunisticGraftThreshold      . non-neg-rational)
          (topicWeight                      . non-neg-rational)
          (meshMessageDeliveriesDecay       . frac)
          (firstMessageDeliveriesDecay      . frac)
          (behaviourPenaltyDecay            . frac)
          (meshFailurePenaltyDecay          . frac)
          (invalidMessageDeliveriesDecay    . frac)
          (decayToZero                      . frac)
          (decayInterval                    . pos-rational)))

; The records book we use has a loop-stopper that makes it hard to
; determine how msets are rewritten, so I wrote a small book to adjust
; that and now it is part of defdata.

(property params-check2 (x :params)
          (^ (pos-rationalp (mget :meshmessagedeliveriescap x))
             (pos-rationalp (mget :meshmessagedeliveriesthreshold x))
             (pos-rationalp (mget :decayinterval x))
             (natp (mget :activationwindow x))
             (posp (mget :meshtimequantum x))
             (natp (mget :p2cap x))
             (natp (mget :timequantainmeshcap x))
             (rationalp (mget :topiccap x))
             (rationalp (mget :graylistthreshold x))
             (natp (mget :d x))
             (natp (mget :dlow x))
             (natp (mget :dhigh x))
             (natp (mget :dlazy x))
             (pos-rationalp (mget :hbminterval x))
             (pos-rationalp (mget :fanoutttl x))
             (posp (mget :mcachelen x))
             (non-neg-rationalp (mget :mcachegsp x))
             (non-neg-rationalp (mget :seenttl x))
             (non-neg-rationalp (mget :opportunisticgraftthreshold x))
             (non-neg-rationalp (mget :topicweight x))
             (fracp (mget :meshmessagedeliveriesdecay x))
             (fracp (mget :firstmessagedeliveriesdecay x))
             (fracp (mget :behaviourpenaltydecay x))
             (fracp (mget :meshfailurepenaltydecay x))
             (fracp (mget :invalidmessagedeliveriesdecay x))
             (fracp (mget :decaytozero x)))
          :rule-classes :forward-chaining)
          
;; Pete: make a record
(defdata weights
  (record (w1 . non-neg-rational)
          (w2 . non-neg-rational)
          (w3 . non-pos-rational)
          (w3b . non-pos-rational)
          (w4 . neg-rational)
          (w5 . non-neg-rational)
          (w6 . neg-rational)
          (w7 . neg-rational)))

(property weights-check3 (ws :weights)
  (^ (<= 0 (mget :w1 ws))
     (<= 0 (mget :w2 ws))
     (>= 0 (mget :w3 ws))
     (>= 0 (mget :w3b ws))
     (> 0 (mget :w4 ws))
     (<= 0 (mget :w5 ws))
     (> 0 (mget :w6 ws))
     (> 0 (mget :w7 ws)))
  :hints (("goal" :in-theory (enable weightsp)))
  :rule-classes :linear)

;; both weights and params are indexed by topic
(defdata wp (cons weights params))

(property wp-type (x :wp)
  (^ (weightsp (car x))
     (paramsp (cdr x)))
  :rule-classes :forward-chaining)

(defdata twp (map topic wp))
(defdata maybe-wp (or nil wp))
(defdata niltype nil)

;; weights, params and wp are huge data structures,
;; so we disable their definitions to speed up theorem proving
(in-theory (disable weightsp paramsp wpp tctrsp))

(definecd is-valid-twp (twp :twp) :boolean
  (v (endp twp)
     (let ((params (cddar twp)))
       (^ (weightsp (cadar twp))
          (paramsp params)
          (>= (mget :meshMessageDeliveriesCap params)
              (mget :meshMessageDeliveriesThreshold params))
          (<= (mget :dlow params) (mget :d params))
          (>= (mget :dhigh params) (mget :d params))
          (>= (mget :decayInterval params) 1)                
          (is-valid-twp (cdr twp))))))

(property mget-twp (top :topic twpm :twp)
  (let ((x (mget top twpm)))
    (=> x
        (^ (wpp x)
           (weightsp (car x))
           (paramsp (cdr x))))))
          
(property lookup-twpm-check2 (top :topic twpm :twp)
  :check-contracts? nil
  (b* ((x (mget top twpm))
       (ps (cdr x)))
    (=> (^ (is-valid-twp twpm) x)
        (<= (mget :meshmessagedeliveriesthreshold ps)
            (mget :meshmessagedeliveriescap ps))))
  :hints (("goal" :in-theory (enable is-valid-twp mget))))

(property lookup-twpm-check3 (top :topic twpm :twp)
  :check-contracts? nil
  (b* ((x (mget top twpm))
       (ps (cdr x)))
    (=> (^ (is-valid-twp twpm) x)
        (<= (mget :dlow ps)
            (mget :d ps))))
  :hints (("goal" :in-theory (enable is-valid-twp mget))))

(property lookup-twpm-check4 (twpm :twp)
  :check-contracts? nil
  (=> (is-valid-twp twpm)
      (<= (mget :dlow (cddr (car twpm)))
          (mget :d (cddr (car twpm)))))
  :hints (("goal" :in-theory (enable is-valid-twp mget))))

(property car-twpm-check5 (twpm :twp :cons params :all)
  :check-contracts? nil
  (=> (^ (is-valid-twp twpm) (equal params (cddar twpm)))
      (^ (>= (params-meshMessageDeliveriesCap params)
             (params-meshMessageDeliveriesThreshold params))
         (<= (params-dlow params) (params-d params))
         (>= (params-dhigh params) (params-d params))))
  :hints (("Goal" :in-theory (enable is-valid-twp)))
  :rule-classes :forward-chaining)

(definecd calcP1
  (meshTime :non-neg-rational meshTimeQuantum :pos timeQInMeshCap :nat) :rational
  (min (/ meshTime meshTimeQuantum) timeQInMeshCap))

(property maxP1
  (meshTime :non-neg-rational meshTimeQuantum :pos timeQInMeshCap
            :nat)
  (<= (calcP1 meshTime meshTimeQuantum timeQInMeshCap) timeQInMeshCap)
  :hints (("Goal" :in-theory (enable calcP1))))

(definecd calcP2
  (firstMessageDeliveries :non-neg-rational p2cap :nat) :non-neg-rational
  (min firstMessageDeliveries p2cap))

(property maxP2 (firstMessageDeliveries :non-neg-rational p2cap :nat)
  (<= (calcP2 firstMessageDeliveries p2cap) p2cap)
  :hints (("Goal" :in-theory (enable calcP2))))

(definecd calc-deficit
  (meshMessageDeliveries :non-neg-rational
                         meshMessageDeliveriesCap 
                         meshMessageDeliveriesThreshold :pos-rational)  :non-neg-rational
  :ic (>= meshMessageDeliveriesCap meshMessageDeliveriesThreshold)
  (b* ((mmd (min meshMessageDeliveries meshMessageDeliveriesCap))
       (deficit (- meshMessageDeliveriesThreshold mmd)))
    (if (> deficit 0)
        deficit
      0)))

(definecd calcP3
  (meshTime :non-neg-rational
            activationWindow :nat
            meshMessageDeliveries :non-neg-rational
            meshMessageDeliveriesCap 
            meshMessageDeliveriesThreshold :pos-rational) :non-neg-rational
  :ic (>= meshMessageDeliveriesCap meshMessageDeliveriesThreshold)
  (b* ((deficit (calc-deficit meshMessageDeliveries
                              meshMessageDeliveriesCap
                              meshMessageDeliveriesThreshold)))
    (if (and (> meshTime activationWindow)
             (< meshMessageDeliveries meshMessageDeliveriesThreshold))
        (* deficit deficit)
      0)))

;; not checking activation window here because we don't immediately prune a
;; peer just after adding them
(definecd calcP3b
  (meshTime :non-neg-rational
            activationWindow :nat
            meshFailurePenalty 
            meshMessageDeliveries :non-neg-rational
            meshMessageDeliveriesCap 
            meshMessageDeliveriesThreshold :pos-rational) :non-neg-rational
  :ic (>= meshMessageDeliveriesCap meshMessageDeliveriesThreshold)
  (if (and (> meshTime activationWindow)
           (< meshMessageDeliveries meshMessageDeliveriesThreshold))
      (let ((deficit (calc-deficit meshMessageDeliveries
                                   meshMessageDeliveriesCap
                                   meshMessageDeliveriesThreshold)))
        (+ meshFailurePenalty (* deficit deficit)))
    meshFailurePenalty))
  
(property non-pos-p3-p3b (tctrs :tctrs  wtpm :wp)
  (=> (<= (mget :meshmessagedeliveriesthreshold (cdr wtpm))
          (mget :meshmessagedeliveriescap (cdr wtpm)))
      (>= 0
          (+ (* (mget :w3 (car wtpm))
                (calcp3 (tctrs-meshtime tctrs)
                        (mget :activationwindow (cdr wtpm))
                        (tctrs-meshmessagedeliveries tctrs)
                        (mget :meshmessagedeliveriescap (cdr wtpm))
                        (mget :meshmessagedeliveriesthreshold (cdr wtpm))))
             (* (mget :w3b (car wtpm))
                (calcp3b (tctrs-meshtime tctrs)
                         (mget :activationwindow (cdr wtpm))
                         (tctrs-meshfailurepenalty tctrs)
                         (tctrs-meshmessagedeliveries tctrs)
                         (mget :meshmessagedeliveriescap (cdr wtpm))
                         (mget :meshmessagedeliveriesthreshold (cdr wtpm)))))))
  :hints (("Goal" :in-theory (enable twpp wpp weightsp))))

(definecd calcP4
  (invalidMessageDeliveries :non-neg-rational) :non-neg-rational
  (* invalidMessageDeliveries invalidMessageDeliveries))

(definecd calcP7 (badBehaviour :non-neg-rational) :non-neg-rational
  (* badBehaviour badBehaviour))

(definecd calcScoreTopic (tctrs :tctrs wtpm :wp) :rational
  :skip-tests t
  :function-contract-hints (("Goal" :in-theory (enable wpp)))
  :body-contracts-hints (("Goal" :in-theory (enable wpp)))
  :ic (>= (params-meshMessageDeliveriesCap (cdr wtpm))
          (params-meshMessageDeliveriesThreshold (cdr wtpm)))
  (b* ((weights (car wtpm))
       (params (cdr wtpm)))
    (* (params-topicweight params)
       (+ (* (mget :w1 weights)
             (calcP1 (tctrs-meshTime tctrs)
                     (params-meshTimeQuantum params)
                     (params-timeQuantaInMeshCap params)))
          (* (mget :w2 weights)
             (calcP2 (tctrs-firstMessageDeliveries tctrs) (params-p2cap params)))
          (* (mget :w3 weights)
             (calcP3 (tctrs-meshTime tctrs) (params-activationWindow params) 
                     (tctrs-meshMessageDeliveries tctrs) (params-meshMessageDeliveriesCap params)
                     (params-meshMessageDeliveriesThreshold params)))
          (* (mget :w3b weights)
             (calcP3b (tctrs-meshTime tctrs) (params-activationWindow params)
                      (tctrs-meshFailurePenalty tctrs) (tctrs-meshMessageDeliveries
                                                        tctrs)
                      (params-meshMessageDeliveriesCap params) (params-meshMessageDeliveriesThreshold params)))
          (* (mget :w4 weights)
             (calcP4 (tctrs-invalidMessageDeliveries tctrs)))
          ))))

(property max-helper2 (tctrs :tctrs wtpm :wp)
  (=> (>= (params-meshMessageDeliveriesCap (cdr wtpm))
          (params-meshMessageDeliveriesThreshold (cdr wtpm)))
      (b* ((weights (car wtpm))
           (params (cdr wtpm)))
        (<= (* (params-topicweight params)
               (+ (* (mget :w1 weights)
                     (calcP1 (tctrs-meshTime tctrs)
                             (params-meshTimeQuantum params)
                             (params-timeQuantaInMeshCap params)))
                  (* (mget :w2 weights)
                     (calcP2 (tctrs-firstMessageDeliveries tctrs)
                             (params-p2cap params)))))
            (* (params-topicweight params)
               (+ (* (mget :w1 weights)
                     (params-timeQuantaInMeshCap params))
                  (* (mget :w2 weights)
                     (params-p2cap params)))))))
  :hints (("Goal"
           :in-theory (enable weightsp paramsp calcP2 calcP1 wpp))))

;; This shows that we only need P1 and P2 to get max score. Other
;; components only lead to decline in the score.
(property max-helper3 (tctrs :tctrs wtpm :wp)
  (=> (>= (params-meshMessageDeliveriesCap (cdr wtpm))
          (params-meshMessageDeliveriesThreshold (cdr wtpm)))
      (b* ((weights (car wtpm))
           (params (cdr wtpm)))
        (<= (calcScoreTopic tctrs wtpm)
            (* (params-topicweight params)
               (+ (* (mget :w1 weights)
                     (calcP1 (tctrs-meshTime tctrs)
                             (params-meshTimeQuantum params)
                             (params-timeQuantaInMeshCap params)))
                  (* (mget :w2 weights)
                     (calcP2 (tctrs-firstMessageDeliveries tctrs)
                             (params-p2cap params))))))))
  :hints (("Goal"
           :in-theory (enable calcScoreTopic wpp weightsp paramsp))))

 ;; limit on max. score, independent of counters
(property max-topic-score (tctrs :tctrs wtpm :wp)
  (=> (>= (params-meshMessageDeliveriesCap (cdr wtpm))
          (params-meshMessageDeliveriesThreshold (cdr wtpm)))
      (b* ((weights (car wtpm))
           (params (cdr wtpm)))
        (<= (calcScoreTopic tctrs wtpm)
            (* (params-topicweight params)
               (+ (* (mget :w1 weights)
                     (params-timeQuantaInMeshCap params))
                  (* (mget :w2 weights)
                     (params-p2cap params)))))))
  :hints (("Goal" :use (max-helper2 max-helper3)
           :in-theory (enable wpp))))

        
;; Armed with this property, we can define a function to only calculate the
;; maximum possible score.
(definecd calcMaxScoreTopic (wtpm :wp) :rational
  :skip-tests t
  :function-contract-hints (("Goal" :in-theory (enable wpp)))
  :body-contracts-hints (("Goal" :in-theory (enable wpp)))
  :ic (>= (params-meshMessageDeliveriesCap (cdr wtpm))
          (params-meshMessageDeliveriesThreshold (cdr wtpm)))
  (b* ((weights (car wtpm))
       (params (cdr wtpm)))
    (* (params-topicweight params)
       (+ (* (mget :w1 weights)
             (params-timeQuantaInMeshCap params))
          (* (mget :w2 weights)
             (params-p2cap params)))
       )))

(sig mget (:a (map :a :b)) => (or :b niltype))

(definecd lookup-gctrs (p :peer gmap :p-gctrs-map) :gctrs
  :try-induct-function-contractp t
  (let ((x (mget p gmap)))
    (match x
      (() (new-gctrs))
      (& x))))

(definecd lookup-tctrs (p :peer top :topic ptmap :pt-tctrs-map) :tctrs
  (let ((x (mget `(,p . ,top) ptmap)))
    (match x
      (() (new-tctrs))
      (& x))))

;;TODO : pull out definitions in a separate files.
(definecd lookup-score (p :peer prmap :peer-rational-map) :rational
  (let ((x (mget p prmap)))
    (match x
      (() 0)
      (& x))))

(definecd calc-glb-score (p :peer gbmap :p-gctrs-map weights :weights)
  :rational
  (let ((gc (lookup-gctrs p gbmap)))
    (+ (* (mget :w5 weights) (mget :apco gc))
       (* (mget :w6 weights) (mget :ipco gc))
       (* (mget :w7 weights) (calcP7 (mget :bhvo gc))))))

;;max glb score possible
(property max-glb-score (p :peer gbmap :p-gctrs-map weights :weights)
   :testing? nil
   (<= (calc-glb-score p gbmap weights)
       (* (mget :w5 weights) (mget :apco (lookup-gctrs p gbmap))))
   :hints (("Goal" :in-theory
            (enable weightsp gctrsp lookup-gctrs p-gctrs-mapp
                    calc-glb-score))))

 ;; armed with the above property, we know max. achievable glb score.
(definecd calc-max-glb-score (p :peer gbmap :p-gctrs-map weights :weights)
  :rational
  :skip-tests t
  (* (mget :w5 weights) (mget :apco (lookup-gctrs p gbmap))))

(definecd calc-pt-scores
  (pt-ctrs :pt-tctrs-map twpm :twp acc :peer-rational-map) :peer-rational-map
  :ic (is-valid-twp twpm)
  (match pt-ctrs
    (() acc)
    ((((p . top) . ctrs) . rst)
     (b* ((tmp (lookup-score p acc))
          (wp (mget top twpm))
          ((when (null wp)) (calc-pt-scores rst twpm acc))
          (new-score (+ (calcScoreTopic ctrs wp) tmp)))
       (calc-pt-scores rst twpm (mset p new-score acc))))))


(definecd add-glb-scores (topic-scores :peer-rational-map gbmap
         :p-gctrs-map weights :weights topiccap :rational) :peer-rational-map
  :skip-tests t
  (match topic-scores
    (() '())
    (((p . tscore) . rst)
     (mset p
           (+ (min topiccap tscore) ;;apply topic cap here
              (calc-glb-score p gbmap weights))
           (add-glb-scores rst gbmap weights topiccap)))))

(definecd peers-from-pt-tctrs-map (map :pt-tctrs-map acc :lop) :lop
  (match map
    (() acc)
    ((((p . &) . &) . rst)
     (peers-from-pt-tctrs-map rst (if (in p acc)
                                      acc
                                    (cons p acc))))))

;; weights for global score counters are common for all topics
(property consp-twpm-weights (twpm :twp)
  (=> (consp twpm)
      (weightsp (cadar twpm))))

(property topiccap-twpm (twpm :twp)
  (=> (consp twpm)
      (rationalp (mget :topiccap (cddr (car twpm)))))
  :hints (("goal" :in-theory (enable twpp wpp))))
  
(definecd calc-nbr-scores-map
  (pt-ctrs :pt-tctrs-map gbmap :p-gctrs-map twpm :twp) :peer-rational-map
  :ic (^ (consp twpm)
         (is-valid-twp twpm))
  :skip-tests t
  :body-contracts-hints (("Goal" :in-theory (enable paramsp twpp wpp)))
  (add-glb-scores (calc-pt-scores pt-ctrs twpm nil)
                  gbmap
                  (cadar twpm)
                  (params-topiccap (cddar twpm))))

(definecd calc-max-topic-scores
  (pt-ctrs :pt-tctrs-map twpm :twp acc :peer-rational-map)
  :peer-rational-map
  :ic (is-valid-twp twpm)
  :skip-tests t
  :body-contracts-hints (("Goal" :in-theory (enable wpp)))
  (match pt-ctrs
    (() acc)
    ((((p . top) . &) . rst)
     (b* ((tmp (lookup-score p acc))
          (wp (mget top twpm))
          ((when (null wp)) (calc-max-topic-scores rst twpm acc))
          (new-score (+ (calcMaxScoreTopic wp) tmp)))
       (calc-max-topic-scores rst twpm (mset p new-score acc))))))

(definecd add-max-glb-scores
  (topic-scores :peer-rational-map gbmap
                :p-gctrs-map weights :weights topiccap :rational)
  :peer-rational-map
  :skip-tests t
  (match topic-scores
    (() '())
    (((p . tscore) . rst)
     (mset p (+ (min topiccap tscore)
                (calc-max-glb-score p gbmap weights))
           (add-max-glb-scores rst gbmap weights topiccap)))))

(definecd calc-max-nbr-scores-map (pt-ctrs :pt-tctrs-map gbmap :p-gctrs-map twpm :twp) :peer-rational-map
  :ic (^ (consp twpm)
         (is-valid-twp twpm))
  :skip-tests t
  :body-contracts-hints (("Goal" :in-theory (enable paramsp twpp wpp)))
  (add-max-glb-scores
   (calc-max-topic-scores pt-ctrs twpm nil)
   gbmap
   (cadar twpm)
   (params-topiccap (cddar twpm))))


;; Properties

;; ------------------------------------------------
;; Some interesting properties about topic-counters
;; ------------------------------------------------

(definecd nth-nneg-rat (n :nat) :nat
  (mod (1+ n) 5))

(defdata-attach non-neg-rational :enumerator nth-nneg-rat)

;;1. Increasing meshTime decreases topic-score. Here is a counter example.
(acl2::must-fail
 (property mesh-time-inc-score
   (imd mmd mt fmd mfp p :non-neg-rational wtpm :wp)
   :check-contracts? nil
   :proofs? nil
   (=> (>= (params-meshMessageDeliveriesCap (cdr wtpm))
           (params-meshMessageDeliveriesThreshold (cdr wtpm)))
       (>= (calcScoreTopic (tctrs imd mmd  (+ p mt) fmd mfp) wtpm)
           (calcScoreTopic (tctrs imd mmd  mt fmd mfp) wtpm)))))

;; 2. Increasing invalidMessageDeliveries decreases score
(encapsulate
 ()
 (local 
   (property inc-calcP4 (imd p :non-neg-rational)
     (=> (< 0 p)
         (< (calcP4 imd)
            (calcP4 (+ p imd))))
     :hints (("Goal" :in-theory (enable calcP4)))
     :rule-classes :linear))

 (local
   (property neg-fifth-weight (wt :weights)
     (> 0 (mget :w4 wt))
     :hints (("Goal" :in-theory (enable weightsp)))
     :rule-classes :linear))
          
 (property imd-dec-score
   (imd mmd mt fmd mfp p :non-neg-rational wtpm :wp)
   :check-contracts? nil
   (=> (^ (>= (params-meshMessageDeliveriesCap (cdr wtpm))
              (params-meshMessageDeliveriesThreshold (cdr wtpm)))
          (< 0 p))
       (>= (calcScoreTopic (tctrs imd mmd  mt fmd mfp) wtpm)
           (calcScoreTopic (tctrs (+ p imd) mmd  mt fmd mfp) wtpm)))
   :hints (("Goal" :in-theory (enable tctrs tctrsp calcScoreTopic calcP4
                                      wpp weightsp paramsp)))))
  

;; 3. Decreasing meshMessageDeliveries below the threshold decreases calcP3 score
(property dec-calcP3
  (meshTime :non-neg-rational
            activationWindow :nat
            meshMessageDeliveries :non-neg-rational
            meshMessageDeliveriesCap 
            meshMessageDeliveriesThreshold :nat
            p :non-neg-rational)
  (=> (^ (> meshTime activationWindow)
         (< meshMessageDeliveries meshMessageDeliveriesThreshold)
         (<= MESHMESSAGEDELIVERIESTHRESHOLD
             MESHMESSAGEDELIVERIESCAP)
         (< 0 p)
         (< 0 (- meshMessageDeliveries p)))
      (< (calcP3 meshTime activationWindow meshMessageDeliveries
                 meshMessageDeliveriesCap
                 meshMessageDeliveriesThreshold)
         (calcP3 meshTime activationWindow (- meshMessageDeliveries p)
                 meshMessageDeliveriesCap
                 meshMessageDeliveriesThreshold)))
  :hints (("Goal" :in-theory (enable calcP3 calc-deficit))))

;; 4. Decreasing meshMessageDeliveries below the threshold decreases calcP3b score
(property dec-calcP3b
  (meshTime :non-neg-rational
            activationWindow :nat
            meshFailurePenalty 
            meshMessageDeliveries :non-neg-rational
            meshMessageDeliveriesCap 
            meshMessageDeliveriesThreshold :nat
            p :non-neg-rational)
  (=> (^ (> meshTime activationWindow)
         (< meshMessageDeliveries meshMessageDeliveriesThreshold)
         (<= MESHMESSAGEDELIVERIESTHRESHOLD
             MESHMESSAGEDELIVERIESCAP)
         (< 0 p)
         (< 0 (- meshMessageDeliveries p)))
      (< (calcP3b meshTime activationWindow
                  meshFailurePenalty
                  meshMessageDeliveries
                  meshMessageDeliveriesCap
                  meshMessageDeliveriesThreshold)
         (calcP3b meshTime activationWindow
                  meshFailurePenalty
                  (- meshMessageDeliveries p)
                  meshMessageDeliveriesCap
                  meshMessageDeliveriesThreshold)))
  :hints (("Goal" :in-theory (enable calcP3b calc-deficit))))

(property more-less-neg (a b :rational c :neg-rational)
  (=> (< b a)
      (<= (* c a)
          (* c b)))
  :rule-classes :linear)
