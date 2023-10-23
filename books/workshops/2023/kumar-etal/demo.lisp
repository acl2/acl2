
(in-package "ACL2S")

;; To go through this demo, please certify all files by running
;; ./make.sh from this directory

(include-book "network")

"State Definitions"
;; Neighbors and topic subscriptions

;; Counters per topic
(defdata tctrs
  (record (invalidMessageDeliveries . non-neg-rational)
          (meshMessageDeliveries    . non-neg-rational)
          (meshTime                 . non-neg-rational)
          (firstMessageDeliveries   . non-neg-rational)
          (meshFailurePenalty       . non-neg-rational)))

;; Global counters : counters across all topics
;; P5, P6 and P7
;; Pete: make this a record and do for all such types that are lists.
(defdata gctrs
  (record (apco . rational)
          (ipco . non-neg-rational)
          (bhvo . non-neg-rational)))

;; pt-tctrs-map keeps track of tctrs per peer per topic
(defdata pt (cons peer topic))
(defdata pt-tctrs-map (map pt tctrs))

;; Unlike tctrs, P5, P6 and P7 are only per-peer
(defdata p-gctrs-map (map peer gctrs))

;; track topic subscribers
(defdata topic-lop-map (map topic lop))

;; track per peer score
(defdata peer-rational-map (map peer rational))

(definecd lookup-score (p :peer prmap :peer-rational-map) :rational
  (let ((x (mget p prmap)))
    (match x
      (() 0)
      (& x))))

;;The following state deals with neighbours and topics they follow,
;; hence we call it (n)eighbour(t)opic-state or nbr-topic-state
(defdata nbr-topic-state
  (record (nbr-topicsubs . topic-lop-map) ;; peer's neighbours'
          ;; subscriptions, includes peer itself, tokeep track of its own subs
          ;; let's keep this as topic-lop-map, as its convenient, no need to
          ;; invert map
          (topic-fanout  . topic-lop-map) ;; peer doesn't subscribe to these
          ;; topics
          (last-pub      . topic-pos-rat-map) ;; last published time for a topic
          (topic-mesh    . topic-lop-map)))  ;; peer subscribes to these topics
;; and is part of corresponding topic mesh


"Message state"
(defdata-alias pid-type symbol)

;;track who sent the payload/pid
(defdata msg-peer (v (cons payload-type peer)
                     (cons pid-type peer)))

(defdata lomsg-peer (listof msg-peer))
(defdata payload-type (record
                       (content . symbol)
                       (pid . pid-type)
                       (top . topic)
                       (origin . peer)))
(defdata lopid (listof pid-type))
(defdata lopld (listof payload-type))

;; recently seen is a map of message/message id to age
;; consists of all messages seen in the last 120 seconds
(defdata msgpeer-age (map msg-peer rational))
(check= (msgpeer-agep
         `( ((|10| . P2) . 10)
            ((|12| . P3) . 10)
            ((,(payload-type '|100| '|10| 'FM 'AN) . MX) . 2)
            ((,(payload-type '|3lolol| '|10| 'PL 'MX) . P2) . 90)))
        t)

;; cache of message payloads received
(defdata mcache (alistof payload-type peer))
(check= (mcachep `((,(payload-type '|1000| '|10| 'PL 'MX) . P3)
                   (,(payload-type '|2000| '|10| 'NT 'PT) . P4)))
        t)

;;waiting for payload corresponding to pid sent by peer
(defdata msgs-waiting-for (map pid-type peer))

(defdata msgs-state
  (record (recently-seen . msgpeer-age)
          ;; LRU cache of seen message IDs.
          (pld-cache . mcache)
          ;; list of messages
          (hwindows . lon) ;;history windows : each nat is the number of
          ;;messages received in the last HeartBeat interval
          (waitingfor . msgs-waiting-for) ;;received IHAVE, sent IWANT
          ;;waiting for full message
          (served  . msgpeer-age) ;; peers whose IWANT was served. Count
          ;; of servings to avoid spam.
          (ihaves-received . nat)
          (ihaves-sent . nat)))

"Peer State"
(defdata peer-state
  (record (nts . nbr-topic-state)
          (mst . msgs-state)
          (nbr-tctrs . pt-tctrs-map)
          (nbr-gctrs . p-gctrs-map)
          (nbr-scores . peer-rational-map)))

"Network State"
(defdata group (map peer peer-state))


"Event Definitions"
(defdata verb (enum '(SND RCV)))
(defdata rpc (v (list 'CONNECT1 lot)
                (list 'CONNECT2 lot)
                (list 'PRUNE topic)
                (list 'GRAFT topic)
                (list 'SUB topic)
                (list 'UNSUB topic)))
(defdata data (v (list 'IHAVE lopid)
                 (list 'IWANT lopid)
                 (list 'PAYLOAD payload-type)))
(defdata mssg (v rpc data))
(defdata evnt (v (cons peer (cons verb (cons peer mssg)))
                 (list peer 'JOIN topic)
                 (list peer 'LEAVE topic)
                 (list peer verb peer 'CONNECT1 lot)
                 (list peer verb peer 'CONNECT2 lot)
                 (list peer 'HBM pos-rational)
                 (list peer 'APP payload-type)))
(defdata hbm-evnt (list peer 'HBM pos-rational))
(defdata-subtype hbm-evnt evnt)

(defdata loev (listof evnt))


"Params and Weights"
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

(defdata weights
  (record (w1 . non-neg-rational)
          (w2 . non-neg-rational)
          (w3 . non-pos-rational)
          (w3b . non-pos-rational)
          (w4 . neg-rational)
          (w5 . non-neg-rational)
          (w6 . neg-rational)
          (w7 . neg-rational)))

;; Def. of a valid twp
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


"Score Calculation"
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

;; Per topic score calculation
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

;; Limit on max. score achievable in a topic, independent of counters
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

;; Neighbors' score calculation
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



"Transitions"


"nbr-topic-state transition"

(defdata res1
  (record (nts . nbr-topic-state)
          (evs . loev)
          (tcm . pt-tctrs-map)
          (gcm . p-gctrs-map)
          (sc . peer-rational-map)))

(definecd update-nbr-topic-state1
  (nts :nbr-topic-state
       nbr-scores :peer-rational-map
       tcmap :pt-tctrs-map
       gcmap :p-gctrs-map
       evnt :evnt
       twpm :twp
       s :nat)
  :res1
  :skip-tests t
  :timeout 600
  :ic (is-valid-twp twpm)
  :body-contracts-hints (("goal" :do-not-induct t
                          :in-theory (enable nbr-topic-statep evntp twpp wpp)))
  (b* ((topic-subs (nbr-topic-state-nbr-topicsubs nts))
       (topic-meshes (nbr-topic-state-topic-mesh nts))
       (mesh-nbrs (reduce* subscribers nil topic-meshes))
       (defaultres (res1 nts nil tcmap gcmap nbr-scores)))
      (match evnt
	((& 'RCV nbr 'SUB topic)
	 (res1 (update-nbr-topicsubs
		nts
		(add-sub topic-subs nbr topic))
	       nil
	       tcmap
	       gcmap
	       nbr-scores))
	;;UNSUB implies PRUNE, so we also prune the nbr if it is in a mesh
	;;Whenever we prune, we need to reset counters for nbr, but retain meshFailurePenalty
	;;If nbr is not in mesh, then default behaviour
	((& 'RCV nbr 'UNSUB topic)
	 (b* ((new-nts
	       (update-nbr-topicsubs
		nts
		(rem-sub topic-subs nbr topic)))
	      (wp (mget topic twpm))
	      (params (cdr wp))
	      ((when (null params)) defaultres)
	      ((when (in nbr mesh-nbrs)) (res1
					  (update-topic-mesh
					   new-nts
					   (rem-sub topic-meshes nbr topic))
					  nil
					  (retain-mesh-failure-counters
					   tcmap nbr topic
					   (params-meshMessageDeliveriesCap params)
					   (params-meshMessageDeliveriesThreshold
					    params))
					  gcmap
					  nbr-scores)))
	     defaultres))
	;;TODO : need to check for nbr score before grafting, and whether it is
	;;in BACKOFF
	;;GRAFT implies SUB, so we also add nbr subscription
	((p1 'RCV nbr 'GRAFT topic)
	 (cond
	  ((^ (in topic (topics))
	      (! (in p1 (mget topic topic-subs))))
	   (res1 nts
		 ;; p1 not subscribed to topic, send PRUNE
		 `((,p1 SND ,nbr PRUNE ,topic))
		 tcmap gcmap nbr-scores))
	  ((^ (in topic (topics))
	      (>= 0 (lookup-score nbr nbr-scores)))
	   (res1 (update-topic-mesh
		  (update-nbr-topicsubs
		   nts
		   (add-sub topic-subs nbr topic))
		  (add-sub topic-meshes nbr topic))
		 nil
		 tcmap
		 gcmap
		 nbr-scores))
	  (t defaultres)))
	((& 'RCV nbr 'PRUNE topic)
	 (b* ((wp (mget topic twpm))
	      (params (cdr wp))
	      ((when (null params)) defaultres))
	     (res1 (update-topic-mesh
		    nts
		    (rem-sub topic-meshes nbr topic))
		   nil
		   (retain-mesh-failure-counters tcmap
						 nbr
						 topic
						 (params-meshMessageDeliveriesCap
						  params)
						 (params-meshMessageDeliveriesThreshold
						  params))
		   gcmap
		   nbr-scores)))

	((p1 'SND & 'SUB topic)
	 (res1 (update-nbr-topicsubs
		nts
		(add-sub topic-subs p1 topic))
	       nil
	       tcmap
	       gcmap
	       nbr-scores))
	;;UNSUB implies PRUNE, so we also prune the nbr (topic key removed from mesh map)
	;;If nbr is not in mesh, then default behaviour
	;; no need to send PRUNE
	((p1 'SND & 'UNSUB topic)
	 (res1 (update-nbr-topicsubs
		nts
		(rem-sub topic-subs p1 topic))
	       nil
	       tcmap
	       gcmap
	       nbr-scores))
	;;need to check for nbr score before grafting
	((& 'SND nbr 'GRAFT topic)
	 (res1 (update-topic-mesh
		nts
		(add-sub topic-meshes nbr topic))
	       nil
	       tcmap
	       gcmap
	       nbr-scores))
	((& 'SND nbr 'PRUNE topic)
	 (b* ((wp (mget topic twpm))
	      (params (cdr wp))
	      ((when (null params)) defaultres))
	     (res1 (update-topic-mesh
		    nts
		    (rem-sub topic-meshes nbr topic))
		   nil
		   (retain-mesh-failure-counters tcmap
						 nbr
						 topic
						 (params-meshMessageDeliveriesCap
						  params)
						 (params-meshMessageDeliveriesThreshold
						  params))
		   gcmap
		   nbr-scores)))
	((self 'RCV p1 'CONNECT1 tps)
	 (res1 (update-nbr-topicsubs nts (reduce* add-peer-subs topic-subs tps p1))
	       `((,self SND ,p1 CONNECT2 ,(peer-subs topic-subs self)))
	       tcmap
	       gcmap
	       nbr-scores))
	((& 'RCV p1 'CONNECT2 tps)
	 (res1 (update-nbr-topicsubs nts (reduce* add-peer-subs topic-subs tps p1))
	       nil
	       tcmap
	       gcmap
	       nbr-scores))
	(& defaultres))))

(property ltp1 (top :topic ns :lop)
          (lotopicpeerp (dist-cons `(,top . ,ns))))

(property ltp2 (xs :lotopicpeer ys :lotopicpeer)
          (lotopicpeerp (app xs ys)))

(definecd flatten-topic-lop-map-help (ls :topic-lop-map ts :lot) :lotopicpeer
  (match ts
    (() '())
    ((top . rst) (app (dist-cons (cons top (mget top ls)))
                      (flatten-topic-lop-map-help ls rst)))))

(definecd flatten-topic-lop-map (ls :topic-lop-map) :lotopicpeer
  (flatten-topic-lop-map-help ls (acl2::alist-keys ls)))

(definecd update-nbr-topic-state2 (nts :nbr-topic-state
                                       nbr-scores :peer-rational-map
                                       tcmap :pt-tctrs-map
                                       gcmap :p-gctrs-map
                                       evnt :evnt
                                       twpm :twp
                                       s :nat)
  :res1
  :skip-tests t
  :ic (is-valid-twp twpm)
  :body-contracts-hints (("goal" :do-not-induct t
                          :in-theory (enable nbr-topic-statep evntp twpp wpp)))
  (b* ((topic-subs (nbr-topic-state-nbr-topicsubs nts))
       (topic-meshes (nbr-topic-state-topic-mesh nts))
       (nbrs (reduce* subscribers nil topic-subs))
       (defaultres (res1 nts nil tcmap gcmap nbr-scores)))
      (match evnt
	((p1 'JOIN tp) (b* ((wp (mget tp twpm))
			    (params (cdr wp))
			    ((when (null params)) defaultres)
			    (d (params-d params))
			    (tpnbrs (remove p1 (mget tp topic-subs)))
			    (newnbrs (grab d (shuffle tpnbrs s)))
			    (newmesh (mset tp newnbrs topic-meshes)))
			   (res1 (update-topic-mesh
				  (update-nbr-topicsubs nts (add-sub topic-subs p1 tp))
				  newmesh)
				 (app
				  (map* mk-grafts
					(flatten-topic-lop-map (mset tp newnbrs nil)) p1)
				  (map* mk-subs
					(flatten-topic-lop-map (mset tp nbrs nil)) p1))
				 tcmap gcmap nbr-scores)))
	
	((p1 'LEAVE tp) (res1 (update-topic-mesh
			       (update-nbr-topicsubs nts (rem-sub topic-subs p1 tp))
			       (mset tp nil topic-meshes))
			      ;;unsubs imply PRUNE
			      (map* mk-unsubs
				    (flatten-topic-lop-map (mset tp nbrs nil)) p1)
			      tcmap gcmap nbr-scores))
	(& defaultres))))

(defthm twp-dlow-int
  (=> (^ (twpp twpm) twpm)
      (INTEGERP (mget :DLOW (CDDR (CAR TWPM)))))
  :hints (("Goal" :in-theory (enable twpp paramsp))))

(defthm twp-MESHMESSAGEDELIVERIESCAP-nat
  (=> (^ (twpp twpm) twpm)
      (ACL2-NUMBERP (mget :MESHMESSAGEDELIVERIESCAP (CDDR (CAR TWPM)))))
  :hints (("Goal" :in-theory (enable twpp paramsp))))

(defthm twp-cddar-paramsp
  (=> (^ (twpp twpm) twpm)
      (PARAMSP (CDDR (CAR TWPM))))
  :hints (("Goal" :in-theory (enable twpp))))

(defthm dlow-number
  (=> (^ (twpp twpm) twpm)
      (ACL2-NUMBERP (mget :D (CDDR (CAR TWPM)))))
  :hints (("Goal" :in-theory (enable twpp paramsp))))

(defthm dlow-lt-d-twp
  (=> (^ (twpp twpm)
         (is-valid-twp twpm)
         (ACL2-NUMBERP (mget :D (CDDR (CAR TWPM)))))
      (<= (mget :DLOW (CDDR (CAR TWPM)))
          (mget :D (CDDR (CAR TWPM)))))
  :hints (("Goal" :in-theory (enable is-valid-twp wpp paramsp))))

(defthm d-lt-dhigh-twp
  (=> (^ (twpp twpm)
         (is-valid-twp twpm)
         (ACL2-NUMBERP (mget :D (CDDR (CAR TWPM)))))
      (<= (mget :d (cddr (car twpm)))
          (mget :dhigh (cddr (car twpm)))))
  :hints (("Goal" :in-theory (enable is-valid-twp wpp paramsp))))

(defthm mmdt-lt-mmdc-twp
  (=> (^ (twpp twpm)
         (is-valid-twp twpm)
         (ACL2-NUMBERP (mget :D (CDDR (CAR TWPM)))))
      (<= (mget :meshmessagedeliveriesthreshold (cddr (car twpm)))
          (mget :meshmessagedeliveriescap (cddr (car twpm)))))
  :hints (("Goal" :in-theory (enable is-valid-twp wpp paramsp))))

(defthm dlow-gt-0-twp
  (=> (^ (twpp twpm)
         (is-valid-twp twpm)
         (ACL2-NUMBERP (mget :D (CDDR (CAR TWPM)))))
      (<= 0 (mget :DLOW (CDDR (CAR TWPM)))))
  :hints (("Goal" :in-theory (enable is-valid-twp wpp paramsp))))

(property cons-twpm (twpm :twp)
	  (=> (consp twpm)
	      (wpp (cdar twpm)))
	  :hints (("Goal" :in-theory (enable twpp))))

(property extract-cars-mesh (m :topic-lop-map)
          (lotp (strip-cars m)))

(definecd update-nbr-topic-state3 (nts :nbr-topic-state
                                       nbr-scores :peer-rational-map
                                       tcmap :pt-tctrs-map
                                       gcmap :p-gctrs-map
                                       evnt :evnt
                                       twpm :twp
                                       s :nat)
  :res1
  :skip-tests t
  :timeout 60
  :ic (is-valid-twp twpm)
  :body-contracts-hints (("Goal" :DO-NOT-INDUCT T
                          :in-theory (enable nbr-topic-statep evntp twpp wpp)))
  (b* ((topic-subs (nbr-topic-state-nbr-topicsubs nts))
       (topic-meshes (nbr-topic-state-topic-mesh nts))
       (mesh-nbrs (reduce* subscribers nil topic-meshes))
       (defaultres (res1 nts nil tcmap gcmap nbr-scores)))
      (match evnt
	((p1 'HBM elapsed) (b* ((wp (cdar twpm))
				(params (cdr wp))
				((when (null params)) defaultres)
				(nbr-scores (calc-nbr-scores-map tcmap gcmap twpm))
				(remvd (strip-cars (lt-0-filter nbr-scores)))
				;;score based removal
				(mesh1 (reduce* remove-subbed-peers topic-meshes
						remvd))
				
				;;removal due to dhigh
				(mesh2 (remove-excess-mesh mesh1
							   (params-dhigh params)
							   (params-d params)
							   s))
				
				;; these can not be added to mesh
				(disqualified-mesh-nbrs (app mesh-nbrs
							     (cons p1 remvd)))
				
				;; addition due to dlow
				;; only one of these 2 will happen, addition or
				;; reduction
				;; new peers to be added in the mesh will come
				;; from the map of topic-subs\disqualified-nbrs
				(mesh3 (add-mesh-nbrs mesh2
						      (rem-peers-topic-lop-map topic-subs
									       disqualified-mesh-nbrs
									       nil)
						      (params-dlow params)
						      (params-d params)))
				;;topic-peer alist which is to be pruned
				(tps-rem (app (filter* remvd-topic-nbr
						       (flatten-topic-lop-map topic-meshes)
						       remvd) ;; score
					      (set-difference-equal
					       (flatten-topic-lop-map mesh1)
					       (flatten-topic-lop-map mesh2)))) ;;extras
				;;topic-peer alist which is to be grafted
				(tps-gr (set-difference-equal
					 (flatten-topic-lop-map mesh3)
					 (flatten-topic-lop-map mesh2)))
				(newnts (update-topic-mesh nts mesh3))
				(newnts (fanout-maintenance newnts
							    topic-subs
							    elapsed
							    (params-fanoutTTL
							     params)
							    (params-d params))))
			       (res1 newnts
				     (app (map* mk-prunes tps-rem p1)
					  (map* mk-grafts tps-gr p1)
					  (opportunistic-grafting
					   p1
					   (strip-cars topic-meshes)
					   nts 
					   nbr-scores
					   params))
				     (update-mesh-times-counters
				      tcmap
				      (flatten-topic-lop-map topic-meshes)
				      elapsed)
				     gcmap
				     nbr-scores)))
	(& defaultres))))

;; Broke this huge function into 3 smaller functions
(definecd update-nbr-topic-state (nts :nbr-topic-state nbr-scores
                                      :peer-rational-map tcmap :pt-tctrs-map
                                      gcmap :p-gctrs-map evnt :evnt twpm :twp s
                                      :nat)
  :res1
  :skip-tests t
  :ic (is-valid-twp twpm)
  :body-contracts-hints (("Goal" :DO-NOT-INDUCT T
                          :in-theory (enable evntp twpp wpp)))
  ;;add all components here
  (cond
   ((in (second evnt) '(RCV SND))
    (update-nbr-topic-state1 nts nbr-scores tcmap gcmap evnt twpm s))
   ((in (second evnt) '(JOIN LEAVE))
    (update-nbr-topic-state2 nts nbr-scores tcmap gcmap evnt twpm s))
   (t (update-nbr-topic-state3 nts nbr-scores tcmap gcmap evnt twpm s))))



"Messages State Transition"


(defdata res2
  (record (mst . msgs-state)
          (evs . loev)
          (tcm . pt-tctrs-map)
          (gcm . p-gctrs-map)))


(definecd update-msgs-state1 (mst :msgs-state evnt :evnt
                                  pcmap :pt-tctrs-map
                                  gcmap :p-gctrs-map
                                  twpm :twp)
  :res2
  :skip-tests t
  :timeout 2000
  :function-contract-hints (("Goal" :DO-NOT-INDUCT T
                             :in-theory (enable evntp)))
  :body-contracts-hints (("Goal" :DO-NOT-INDUCT T
                          :in-theory (enable evntp)))
  (b* ((rs      (msgs-state-recently-seen mst))
       (mcache  (msgs-state-pld-cache mst))
       (hwins   (msgs-state-hwindows mst))
       (waiting (msgs-state-waitingfor mst))
       (servd   (msgs-state-served mst))
       (ihr     (msgs-state-ihaves-received mst))
       (ihs     (msgs-state-ihaves-sent mst))
       (default-res (res2 mst nil pcmap gcmap)))
      (match evnt
	((p1 'APP & pld)
	 (res2 (msgs-state (add-to-recentlyseen pld p1 rs)
			   (cons `(,pld . ,p1) mcache)
			   (increment-car hwins)
			   waiting
			   servd
			   ihr
			   ihs)
	       nil
	       pcmap
	       gcmap))
	((p1 'RCV nbr 'PAYLOAD pld)
	 (b* ((top (payload-type-top pld))
	      (cs (lookup-tctrs nbr top pcmap)))
	     ;; don't update firstMessageDeliveries everytime, check mcache
	     (if (isValidPayload pld)
		 (res2 (msgs-state (add-to-recentlyseen pld nbr rs)
				   (add-ppm-mcache pld p1 mcache)
				   (if (in-mcache (payload2pid pld) mcache)
				       hwins
				     (increment-car hwins))
				   waiting
				   servd
				   ihr
				   ihs)
		       nil
		       (mset `(,nbr . ,top)
			     (increment-firstMessageDeliveries
			      (increment-meshMessageDeliveries cs))
			     pcmap)
		       gcmap)
	       (res2 mst
		     nil
		     (mset `(,nbr . ,top)
			   (increment-invalidMessageDeliveries cs)
			   pcmap)
		     gcmap))))
	((p1 'RCV nbr 'IHAVE pids)
	 (b* (((unless (< ihr *max-ihaves*)) default-res)
	      (dont-haves
	       (remove-duplicates-equal
		(set-difference-equal
		 (set-difference-equal pids (map* rs->pids (strip-cars rs)))
		 (map* get-pids mcache))))
	      ((unless (consp dont-haves)) default-res))
	     (res2 (increase-ihaves-received
		    (update-waitingfor mst dont-haves nbr)
		    (len (remove-duplicates-equal pids)))
		   `((,p1 SND ,nbr IWANT ,dont-haves))
		   pcmap
		   gcmap)))
	((p1 'RCV nbr 'IWANT pids)
	 (b* ((pds (pids-to-serve nbr pids servd))
	      ((unless (consp pds)) default-res)
	      (tsrv (intersection-equal (map* get-pids mcache) pds))
	      ((unless (consp tsrv)) default-res))
	     (res2 (msgs-state rs
			       mcache
			       hwins
			       waiting
			       (update-served nbr tsrv servd)
			       ihr
			       ihs)
		   (map* send-plds (remove-duplicates-equal (get-plds tsrv mcache)) p1 nbr)
		   pcmap
		   gcmap)))
	(& default-res))))


(definecd update-msgs-state2 (mst :msgs-state evnt :evnt
				  pcmap :pt-tctrs-map
				  gcmap :p-gctrs-map
				  twpm :twp)
  :res2
  :skip-tests t
  :timeout 2000
  :function-contract-hints (("Goal" :DO-NOT-INDUCT T
			     :in-theory (enable evntp paramsp)))
  :body-contracts-hints (("Goal" :DO-NOT-INDUCT T
			  :in-theory (enable evntp twpp)))
  (b* ((rs      (msgs-state-recently-seen mst))
       (mcache  (msgs-state-pld-cache mst))
       (hwins   (msgs-state-hwindows mst))
       (waiting (msgs-state-waitingfor mst))
       (servd   (msgs-state-served mst))
       (ihr     (msgs-state-ihaves-received mst))
       (ihs     (msgs-state-ihaves-sent mst))
       (default-res (res2 mst nil pcmap gcmap)))
      (match evnt
	((p1 'HBM elapsed)
	 (b*  ((wp (cdar twpm))
	       (params (cdr wp))
	       ((when (null params)) default-res)
	       (mcl     (params-mcacheLen params))
	       (new-hwins (grab mcl (cons 0 hwins)))
	       (new-mcache (grab (reduce* + 0 new-hwins)
				 mcache))
	       (seenttl (params-seenTTL params))
	       (new-mst (msgs-state (update-m-age rs elapsed seenttl)
				    new-mcache
				    new-hwins
				    waiting
				    servd
				    0    ;; reset ihaves received 
				    0))) ;;reset ihaves sent.
	      (if (and (consp waiting)
		       (< *waittime* elapsed))
		  (let ((senders (get-ihave-senders waiting)))
		    (res2 new-mst
			  nil
			  ;;,(increment-badbehaviours pcmap senders 'FM)))
			  pcmap
			  gcmap))
					;TODO : IHAVE PIDS must also be sent with their topic
		(res2 new-mst
		      nil
		      pcmap
		      gcmap))))
	(& default-res)))))

(definecd update-msgs-state (mst :msgs-state evnt :evnt pcmap :pt-tctrs-map
                                 gcmap :p-gctrs-map twpm :twp)
  :res2
  :skip-tests t
  (match evnt
    ((_ 'HBM _) (update-msgs-state2 mst evnt pcmap gcmap twpm))
    (& (update-msgs-state1 mst evnt pcmap gcmap twpm))))


"Peer State Transition"
(defdata res4
  (record (pst . peer-state)
          (evs . loev)))

(definecd transition
  (self :peer pstate :peer-state evnt :evnt twpm :twp s :nat) :res4
  :skip-tests t
  :timeout 2000
  :function-contract-hints (("Goal" :in-theory (enable evntp forward-emission
                                                    update-nbr-topic-state
                                                    update-nbr-topic-state1
                                                    update-nbr-topic-state2
                                                    update-nbr-topic-state3
                                                    update-msgs-state
                                                    update-msgs-state1
                                                    update-msgs-state2)))
  :body-contracts-hints (("Goal" :in-theory (enable evntp forward-emission
						    forward-emission-help
                                                    update-nbr-topic-state
                                                    update-nbr-topic-state1
                                                    update-nbr-topic-state2
                                                    update-nbr-topic-state3
                                                    update-msgs-state
                                                    update-msgs-state1
                                                    update-msgs-state2)))
  :ic (is-valid-twp twpm)
  (b* ((defaultres (res4 pstate nil))
       (ntstate (peer-state-nts pstate))
       (params (cddar twpm))
       ((when (null params)) defaultres)
       (nbr-tctrs (peer-state-nbr-tctrs pstate))
       (nbr-gctrs (peer-state-nbr-gctrs pstate))
       (scores (if (hbm-evntp evnt)
                   (calc-nbr-scores-map nbr-tctrs nbr-gctrs twpm)
                 (peer-state-nbr-scores pstate)))
       (d (params-d params))
       (msgstate (peer-state-mst pstate))
       (rs (msgs-state-recently-seen msgstate))
       (gossips (if (hbm-evntp evnt)
                    (gossip-emission (car evnt) pstate d params s)
                  ()))
       ((res3 ntstate forwards) (forward-emission self evnt ntstate rs s d))
       ((res1 ntstate evnts tctrs gctrs scores)
        (update-nbr-topic-state ntstate scores nbr-tctrs nbr-gctrs evnt twpm
                                s))
       ((res2 msgstate evnts2 tctrs gctrs)
        (update-msgs-state msgstate evnt tctrs gctrs twpm))
       (tctrs (if (hbm-evntp evnt)
                  (decay-ctrs (strip-cars tctrs) (third evnt) twpm tctrs)
                tctrs)))
    (res4 (peer-state ntstate
                      msgstate
                      tctrs
                      gctrs ;; TODO : will need to decay this as well
                      scores)
          (app evnts
               evnts2
               forwards
               gossips))))


;; Network transition, on a list of events
(definecd run-network (gr :group evnts :loev i :nat twpm :twp s :nat) :egl
    :ic (is-valid-twp twpm)
    :skip-tests t
    (if (v (zp i)
           (endp evnts))
        '()
      (b* (((mv k s) (defdata::genrandom-seed
                       (1- (expt 2 31))
                       (mod s (expt 2 31))))
           (actor (caar evnts))
           (actor-state (lookup-state actor gr))
           ((res4 next-actor-state evs) (transition actor actor-state (car evnts)
                                                    twpm k))
           (next-actor-events (network-propagator evs nil))
           (newgrp (mset actor next-actor-state gr)))
        (cons `(,(car evnts) . ,newgrp)
              (run-network
               newgrp
               ;;mix generated events with remaining events
               (app
		;;
		;; let's see what happens if we ignore these events. Times won't depend on grp size
		(cdr evnts)
		next-actor-events
		)
               (1- i)
               twpm
               s)))))


