;; PETE: Use maps everywhere you want maps and only use mset/mget to
;; modify records and maps.

(in-package "ACL2S")

(include-book "nbrs-topics-state")
(include-book "msgs-state")

(defdata peer-state
  (record (nts . nbr-topic-state)
          (mst . msgs-state)
          (nbr-tctrs . pt-tctrs-map)
          (nbr-gctrs . p-gctrs-map)
          (nbr-scores . peer-rational-map)))

;;initializes a new peer state if we need one, or don't have one already in the network
(definecd new-peer-state () :peer-state
  (peer-state (new-nbr-topic-state)
              (new-msgs-state)
              '()
              '()
              '()))

(property snd-ihave-evnt (p1 p2 :peer pids :lopid)
  (EVNTP (LIST P1 'SND P2 'IHAVE pids))
  :hints (("Goal" :in-theory (enable evntp))))

(create-map* (lambda (nbr p pids) `(,p SND ,nbr IHAVE ,pids))
             lopp
             loevp
             (:fixed-vars ((peerp p) (lopidp pids)))
             (:name mapgossips))

(sig grab (nat (listof :a)) => (listof :a))
(sig shuffle ((listof :a) nat) => (listof :a))
(sig remove-duplicates-equal ((listof :a)) => (listof :a))

(property flatten-cdrs-tlm (tlm :topic-lop-map)
  (lopp (flatten (strip-cdrs tlm))))

(sig set-difference-equal ((listof :a) (listof :a)) => (listof :a))

(property grab-mcache (mc :mcache n :nat)
          (mcachep (grab n mc)))

;;emit gossip to d random nbrs
(definecd gossip-emission (p :peer ps :peer-state d :nat params :params s :nat) :loev
  :skip-tests t
  (b* (((mv k &) (defdata::genrandom-seed
                   (1- (expt 2 31))
                   (mod s (expt 2 31))))
       (ms (peer-state-mst ps))
       (mcache  (msgs-state-pld-cache ms))
       (hwins   (msgs-state-hwindows ms))
       (mcg     (floor (* (reduce* + 0 hwins) (params-mcacheGsp params)) 1))
       (gsp-cache (grab (reduce* + 0
                                 (grab mcg hwins))
                        mcache))
       ((unless (consp gsp-cache)) nil)
       (pids (remove-duplicates-equal (map* get-pids gsp-cache)))
       (ntst (peer-state-nts ps))
       (allnbrs (flatten (strip-cdrs (nbr-topic-state-nbr-topicsubs ntst))))
       (mesh-nbrs (flatten (strip-cdrs (nbr-topic-state-topic-mesh ntst))))
       (fanout-nbrs (flatten (strip-cdrs (nbr-topic-state-topic-fanout ntst))))
       (mf (append mesh-nbrs fanout-nbrs))
       (no-mf (remove-duplicates-equal (remove p (set-difference-equal allnbrs mf))))
       (gossip-nbrs (grab d (shuffle no-mf k))))
    (map* mapgossips gossip-nbrs p pids)))

(create-map* (lambda (nbr p pld) `(,p SND ,nbr PAYLOAD ,pld))
             lopp
             loevp
             (:fixed-vars ((peerp p) (payload-typep pld)))
             (:name mapforwards))

(in-theory (disable map*-*mapforwards))
(sig remove-assoc-equal (:a (alistof :a :b)) => (alistof :a :b))
(defdata res3
  (record (nts . nbr-topic-state)
          (evs . loev)))

(in-theory (enable res3p))
(definecd forward-emission-help
  (self source :peer ntst :nbr-topic-state payload :payload-type d k :nat)
  :res3
  :skip-tests t
  :body-contracts-hints (("Goal" :DO-NOT-INDUCT T
                          :in-theory (enable nbr-topic-statep)))
  (b* ((ms (nbr-topic-state-topic-mesh ntst))
       (fout (nbr-topic-state-topic-fanout ntst))
       (top (payload-type-top payload))
       (orig (payload-type-origin payload))
       (nsubs (nbr-topic-state-nbr-topicsubs ntst))
       (fwd-nbrs (set-difference-equal
                  (mget top nsubs)
                  `(,orig ,self)))
       (lp (nbr-topic-state-last-pub ntst))
       (newlp (mset top 0 lp))
       (fout-nbrs (mget top fout))
       (msubs (strip-cars ms)))
    (cond ((^ (in top msubs)
              (consp (mget top ms)))
           (res3 ntst
                 (map* mapforwards (set-difference-equal
                                    (mget top ms)
                                    `(,self ,source ,orig))
                       self
                       payload)))
          ((consp fout-nbrs) (res3 (update-last-pub ntst newlp)
                                   (map* mapforwards fout-nbrs self
                                         payload)))
          (t (b* ((new-fout-nbrs
                   (grab d (shuffle fwd-nbrs k)))
                  ((when (endp new-fout-nbrs)) (res3 ntst nil)))
               (res3 (update-topic-fanout
                      (update-last-pub ntst newlp)
                      (mset top new-fout-nbrs fout))
                     (map* mapforwards (set-difference-equal
                                        (mget top ms)
                                        `(,self ,source ,orig))
                           self
                           payload)))))))

(definecd decay-mult (f :frac e :integer x :non-neg-rational d :frac)
  :non-neg-rational
  :ic (<= 0 e)
  (let ((r (* (expt f (1+ e))
              x)))
    (if (< r d)
        0
      r)))

; PETE: why do you need this?
(property assoc-twpm-ptc (twpm :twp top :topic)
  (=> (cdr (mget top twpm))
      (paramsp (cdr (mget top twpm)))))

(property pos-rational-check (x :all)
  (=> (pos-rationalp x)
      (^ (rationalp x)
         (> x 0))))


(encapsulate
 ()
    
 (local
   (property pos-rational-check (x :all)
     (=> (pos-rationalp x)
         (^ (rationalp x)
            (> x 0)))))

 (local
   (defthm lt-0-not-0
     (=> (< 0 x)
         (!= 0 x))))

 (local
   (defthm hbmint-twp2
     (=> (^ (twpp twpm)
            (cddr (assoc-equal (cdr (car (car ptc))) twpm))
            (pt-tctrs-mapp ptc)
            ptc)
         (!= 0 (mget :decayinterval
                     (cddr (assoc-equal (cdr (car (car ptc))) twpm)))))))

 (local
   (defthm floor-pos-rational
     (=> (^ (pos-rationalp a)
            (pos-rationalp b))
         (^ (integerp (floor a b))
            (<= 0 (floor a b))))))
     
 (property extract-cars-pttctrs-map (ptc :pt-tctrs-map)
           (loptp (strip-cars ptc))
           :hints (("Goal" :in-theory (enable pt-tctrs-mapp))))

 (property mget-pttctrs-map (ptc :pt-tctrs-map x :pt)
           (v (null (mget x ptc))
              (tctrsp (mget x ptc)))
           :hints (("Goal" :in-theory (enable pt-tctrs-mapp ptp))))

 ;; TODO : add all other decays as well, including global decays
 (definecd decay-ctrs (pts :lopt hbmint :pos-rational twpm :twp ptc :pt-tctrs-map ) :pt-tctrs-map
   :skip-tests t
   :function-contract-hints (("Goal" :in-theory (enable pt-tctrs-mapp)))
   :body-contracts-hints (("Goal" :in-theory (enable pt-tctrs-mapp)))
   (match pts
     (() ptc)
     ((pt . rst)
      (b* ((params (cdr (mget (cdr pt) twpm)))
           ((when (null params)) (decay-ctrs rst hbmint twpm ptc))
           (d20 (params-decayToZero params))
           (e (floor hbmint (params-decayInterval params)))
           (tctrs (mget pt ptc))
           ((when (null tctrs)) (decay-ctrs rst hbmint twpm ptc))
           (decay-mmd (decay-mult (params-meshMessageDeliveriesDecay params)
                                  e
                                  (tctrs-meshMessageDeliveries tctrs)
                                  d20))
           (decay-fmd (decay-mult (params-firstMessageDeliveriesDecay params)
                                  e
                                  (tctrs-firstMessageDeliveries tctrs)
                                  d20)))
      (decay-ctrs rst hbmint twpm (mset pt (update-firstMessageDeliveries
                                            (update-meshMessageDeliveries
                                             tctrs
                                             decay-mmd)
                                            decay-fmd)
                                        ptc)))))))

(property cdar-twpm (twpm :twp)
  (=> (cdar twpm)
      (wpp (cdar twpm)))
  :rule-classes :forward-chaining)

(property cddar-twpm (twpm :twp)
  (=> (cddar twpm)
      (paramsp (cddar twpm)))
  :rule-classes :forward-chaining)

(sig strip-cars ((alistof :a :b)) => (listof :a))

(property app-loev (xs ys :loev)
          (loevp (app xs ys)))

(property evnt-payload-rcv (e :evnt)
  :check-contracts? nil
  (=> (== (fourth e) 'PAYLOAD)
      (^ (payload-typep (fifth e))
         (peerp (car e))
         (peerp (third e))))
  :hints (("Goal" :in-theory (enable evntp))))

(property evnt-app (e :evnt)
  :check-contracts? nil
  (=> (== (second e) 'APP)
      (^ (peerp (car e))
         (payload-typep (third e))))
  :hints (("Goal" :in-theory (enable evntp))))

(definecd forward-emission
  (self :peer evnt :evnt ntstate :nbr-topic-state rs :msgpeer-age s d :nat)
  :res3
  :body-contracts-hints (("Goal" :in-theory (enable evntp)))
  :skip-tests t
  (match evnt
    ((!self 'RCV p 'PAYLOAD pld)
     (if (^ (!= self (payload-type-origin pld)) ;;if not the publisher
            (! (in (payload2pid pld)
                   (map* rs->pids (strip-cars rs)))))
         (forward-emission-help self p ntstate pld d s)
       (res3 ntstate nil)))
    ((!self 'APP pld)
     (forward-emission-help self self ntstate pld d s))
    (& (res3 ntstate '()))))


(property fwd-emission-help-thm
          (p1 :peer p2 :peer ntstate :nbr-topic-state pld :payload-type s d :nat)
          :check-contracts? nil
          (loevp (res3-evs (forward-emission-help p1 p2 ntstate pld d s)))
          :hints (("Goal" :in-theory (enable forward-emission-help))))

(property fwd-emission-thm1
  (self :peer evnt :evnt ntstate :nbr-topic-state rs :msgpeer-age s d :nat)
  (nbr-topic-statep (res3-nts (forward-emission self evnt ntstate rs s d))))

(property fwd-emission-thm2
  (self :peer evnt :evnt ntstate :nbr-topic-state rs :msgpeer-age s d :nat)
  (loevp (res3-evs (forward-emission self evnt ntstate rs s d))))


; why?
(defthm mget-d
  (=> (^ (twpp twpm)
         twpm)
      (natp (mget :d (cddr (car twpm)))))
  :rule-classes :forward-chaining)

(in-theory (disable peer-state-nts peer-state-mst peer-state-nbr-tctrs
                    peer-state-nbr-gctrs peer-state-nbr-scores))

(defdata res4
  (record (pst . peer-state)
          (evs . loev)))
(in-theory (enable res4p))

(property bind-update-nbr-topic-state
  (nts :nbr-topic-state nbr-scores
       :peer-rational-map tcmap :pt-tctrs-map
       gcmap :p-gctrs-map evnt :evnt twpm :twp s
       :nat)
  :check-contracts? nil
  (b* (((res1 a b c d e)
        (update-nbr-topic-state nts nbr-scores tcmap
                                gcmap evnt twpm s)))
    (^ (nbr-topic-statep a)
       (loevp b)
       (pt-tctrs-mapp c)
       (p-gctrs-mapp d)
       (peer-rational-mapp e)))
  :hints (("Goal" :in-theory (enable update-nbr-topic-state))))

(property bind-update-msgs-state
  (mst :msgs-state tcmap :pt-tctrs-map
       gcmap :p-gctrs-map evnt :evnt twpm :twp)
  :check-contracts? nil
  (b* (((res2 a b c d)
        (update-msgs-state mst evnt tcmap gcmap twpm)))
    (^ (msgs-statep a)
       (loevp b)
       (pt-tctrs-mapp c)
       (p-gctrs-mapp d)))
  :hints (("Goal" :in-theory (enable update-msgs-state update-msgs-state1 evntp))))

(definecd transition
  (self :peer pstate :peer-state evnt :evnt twpm :twp s :nat) :res4
  :skip-tests t
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
