(in-package "ACL2S")

(include-book "std/alists/top" :dir :system)

(include-book "higher-order")
(include-book "scoring")
(include-book "nbrs-topics-state")
(include-book "msgs-state")
(include-book "peer-state")
(include-book "network")

;;example factors
(defconst *factors* (cons
		     (params 1 1 3 5 2 1 5 -3 4 3 5 6 1 60 5 3 120 2)
		     '((FM . (1 ;; time in mesh
                              1 ;; first message deliveries
                              -1 ;; mesh message delivery rate
                              -1 ;; mesh message delivery failures
                              -1 ;; invalid messages
                              1 ;; app specific
                              -1 ;; IP colocation factor
                              -1))
                       (PL . (1 ;; time in mesh
                              1 ;; first message deliveries
                              -1 ;; mesh message delivery rate
                              -1 ;; mesh message delivery failures
                              -1 ;; invalid messages
                              1 ;; app specific
                              -1 ;; IP colocation factor
                              -1))))) ;; behaviour penalty

(set-ignore-ok t)


;;----------------------------------------------------------------------------
;;Topic tests
;;----------------------------------------------------------------------------

(skip-proofs
 (definec init-grp-nbrs-help (peers :lop allpeers :lop d :nat) :group
   :ic (<= (len peers) (len allpeers))
  (match peers
    (() '())
    ((p . rst)
     (let ((n (- (len allpeers) (len peers))))
     `((,p . ,(peer-state
               (nbr-topic-state
                (pairlis$ (grab d (app (nthcdr n allpeers)
				       (take n allpeers)))
			  nil)
		nil nil nil)
               (new-msgs-state) nil nil))
       . ,(init-grp-nbrs-help rst allpeers d)))))))

(definec init-grp-nbrs (peers :lop d :nat) :group
  (init-grp-nbrs-help peers peers d))

(definec p1-subbed=>p2-subbed (p1 :peer p2 :peer top :topic st :peer-state) :boolean
  (b* ((tpsubs (nbr-topic-state-nbr-topicsubs
                (peer-state-nts st)))
       (p1tops (cdr (assoc-equal p1 tpsubs)))
       (p2tops (cdr (assoc-equal p2 tpsubs))))
    (v (not (in top p1tops))
       (in top p2tops))))

;;1. on subscribing, there is no error
;;2. if MX sub is received before TI and TI is subbed then MX is
;; subbed

;; JOIN triggers SUB evnts.., LEAVE triggers UNSUB
(check= t
        (b* ((peers '(AN MX TI))
             (grp (init-grp-nbrs peers 3))
             (pld '(FULLMSG100 PID100 FM MX))
             (evnts
              (network-propagator `((AN JOIN FM)
                                    (MX SND AN SUB FM)
                                    (TI SND AN SUB FM))
                                  nil))
             (res (run-network grp evnts 1000 *factors* 40 nil))
             (final-grp (cdar (last res))))
          (p1-subbed=>p2-subbed 'TI 'MX 'FM (cdr (assoc-equal 'AN final-grp)))))

;;1. on unsubscribing, there is no error
;;2. if MX unsub is received before TI and TI is unsubbed then MX is
;; unsubbed

(definec p1-unsubbed=>p2-unsubbed (p1 :peer p2 :peer top :topic st :peer-state) :boolean
  (b* ((tpsubs (nbr-topic-state-nbr-topicsubs
                (peer-state-nts st)))
       (p1tops (cdr (assoc-equal p1 tpsubs)))
       (p2tops (cdr (assoc-equal p2 tpsubs))))
    (v (in top p1tops)
       (not (in top p2tops)))))

;; LEAVE triggers UNSUB evnts..
(check= t
        (b* ((peers '(AN MX TI))
             (grp (init-grp-nbrs peers 3))
             (pld '(FULLMSG100 PID100 FM MX))
             (evnts
              (network-propagator `((AN JOIN FM)
                                    (MX JOIN FM)
                                    (TI JOIN FM)
                                    (MX LEAVE FM)
                                    (CHRISTINA LEAVE FM))
                                  nil))
             (res (run-network grp evnts 1000 *factors* 40 nil))
             (final-grp (cdar (last res))))
          (p1-unsubbed=>p2-unsubbed 'TI 'MX 'FM (cdr (assoc-equal 'AN final-grp)))))


;;3. Given Linear Mesh : 
;; MX - AN - PT - TI - P1 - P2 - P3 - P4
;; pld produced at MX is received at P4
(check= t
        (b* ((peers '(AN MX PT TI P1 P2 P3 P4))
             (grp (init-grp-nbrs peers 8))
             (pld '(FULLMSG100 PID100 FM MX))
             (evnts
              (network-propagator `((MX JOIN FM)
                                    (AN JOIN FM)
                                    (PT JOIN FM)
                                    (TI JOIN FM)
                                    (P1 JOIN FM)
                                    (P2 JOIN FM)
                                    (P3 JOIN FM)
                                    (P4 JOIN FM)
                                    (AN SND MX GRAFT FM)
                                    (PT SND AN GRAFT FM)
                                    (TI SND PT GRAFT FM)
                                    (P1 SND TI GRAFT FM)
                                    (P2 SND P1 GRAFT FM)
                                    (P3 SND P2 GRAFT FM)
                                    (P4 SND P3 GRAFT FM)
                                    (MX APP FM ,pld))
                                  nil))
             (res (run-network grp evnts 1000 *factors* 40 nil))
             (final-grp (cdar (last res)))  
             (p4-state (cdr (assoc-equal 'P4 final-grp)))
             (mcache (msgs-state-pld-cache
                      (peer-state-mst p4-state))))
          (in-mcache (payload2pid pld) mcache)))
        


(definec msg-with-peers-in-grp (pld :payload-type grp :group) :boolean
  (if (endp grp)
      t
    (^ (in-mcache (payload2pid pld)
                  (msgs-state-pld-cache
                   (peer-state-mst (cdar grp))))
       (msg-with-peers-in-grp pld (cdr grp)))))



;; 4. Given mesh in configuration shown, everyone received a full message
;;   AN   \           / P2
;;   MX -----PT-----P1-- P3
;;   TI/           \ P4
;; 5. After a message was sent in a star topology, nobody got pruned
(check= t
        (b* ((peers '(AN MX PT TI P1 P2 P3 P4))
             (grp (init-grp-nbrs peers 8))
             (pld '(FULLMSG100 PID100 FM MX))
             (evnts
              (network-propagator `((MX JOIN FM)
                                    (AN JOIN FM)
                                    (PT JOIN FM)
                                    (TI JOIN FM)
                                    (P1 JOIN FM)
                                    (P2 JOIN FM)
                                    (P3 JOIN FM)
                                    (P4 JOIN FM)
                                    (AN SND PT GRAFT FM)
                                    (MX SND PT GRAFT FM)
                                    (TI SND PT GRAFT FM)
                                    (PT SND P1 GRAFT FM)
                                    (P2 SND P1 GRAFT FM)
                                    (P3 SND P1 GRAFT FM)
                                    (P4 SND P1 GRAFT FM)
                                    (MX APP FM ,pld))
                                  nil))
             (res (run-network grp evnts 1000 *factors* 40 nil))
             (final-grp (cdar (last res))))
          (^ (msg-with-peers-in-grp pld final-grp)
             (endp
              (set-difference-equal
               peers (acl2::flatten (topic-mesh-graph final-grp 'FM)))))))


(create-map* (lambda (p) `(,p HBM 1))
             lopp
             loevp
             (:name mk-hbms))

(skip-proofs
(definec multiple-hbms (ps :lop n :nat) :loev
  (if (endp ps)
      nil
    (acl2::flatten
     (acl2::repeat n (map* mk-hbms ps))))))


;; 4. Given mesh in configuration shown
;;   AN   \           / P2
;;   MX -----PT-----P1-- P3
;;   TI/           \ P4

;; PT prunes P1

;;   AN   \           / P2
;;   MX -----PT     P1-- P3
;;   TI/           \ P4

;; After 2 HBMs, connection is reformed and MX publishes a message that is
;; received by everyone.
;; After the message was sent, nobody got pruned

(check= t
        (b* ((peers '(AN MX PT TI P1 P2 P3 P4))
             (grp (init-grp-nbrs peers 8))
             (pld '(FULLMSG100 PID100 FM MX))
             (evnts
              (network-propagator
               (app '((MX JOIN FM)
                      (AN JOIN FM)
                      (PT JOIN FM)
                      (TI JOIN FM)
                      (P1 JOIN FM)
                      (P2 JOIN FM)
                      (P3 JOIN FM)
                      (P4 JOIN FM)
                      (AN SND PT GRAFT FM)
                      (MX SND PT GRAFT FM)
                      (TI SND PT GRAFT FM)
                      (PT SND P1 GRAFT FM)
                      (P2 SND P1 GRAFT FM)
                      (P3 SND P1 GRAFT FM)
                      (P4 SND P1 GRAFT FM)
                      (PT SND P1 PRUNE FM)) ;;disconnected mesh
                    (multiple-hbms peers 2)   ;; wait for 2 HBMs
                    `((MX APP FM ,pld)))
               nil))
             (res (run-network grp evnts 1000 *factors* 40 nil))
             (final-grp (cdar (last res))))
          (^ (msg-with-peers-in-grp pld final-grp)
             (endp 
              (set-difference-equal  ;; check if all peers in mesh
               peers (acl2::flatten (topic-mesh-graph final-grp 'FM)))))))




;; Spin up a network, with 8 peers, with mesh degree = 3.
;; Let peers connect among themselves after HBM events.
;; 6. Check if message sent from one peer is received by all
;; 7. Check if no peer got pruned
(check= t
        (b* ((peers '(AN MX PT TI P1 P2 P3 P4))
             (grp (init-grp-nbrs peers 3))
             (pld '(FULLMSG100 PID100 FM MX))
             (evnts
              (network-propagator
	       (app `((MX JOIN FM)
		      (AN JOIN FM)
		      (PT JOIN FM)
		      (TI JOIN FM)
		      (P1 JOIN FM)
		      (P2 JOIN FM)
		      (P3 JOIN FM)
		      (P4 JOIN FM))
		    (multiple-hbms peers 2)
		    `((MX APP FM ,pld)))
	       nil))
             (res (run-network grp evnts 1000 *factors* 40 nil))
             (final-grp (cdar (last res))))
	  (^ (msg-with-peers-in-grp pld final-grp)
             (endp (set-difference-equal
		    peers
		    (acl2::flatten (topic-mesh-graph final-grp 'FM)))))))


(create-map* (lambda (p tp) `(,p JOIN ,tp))
             lopp
             loevp
             (:name mk-joins)
	     (:fixed-vars ((topicp tp))))
  

;; Spin up a network, with 1000 peers, mesh degree = 3.
;; Let peers connect among themselves after HBM events.
;; 6. Check if message sent from one peer is received by all
;; 7. Check if no peer got pruned
(check= t
        (b* ((peers (map* mk-peers (natlist 1000)))
             (grp (init-grp-nbrs peers 3))
	     (p 'P100)
             (pld `(FULLMSG100 PID100 FM ,p))
             (evnts
              (network-propagator
	       (app (map* mk-joins peers 'FM)
		    (multiple-hbms peers 3)
		    `((,p APP FM ,pld)))
	       nil))
             (res (run-network grp evnts 100000 *factors* 40 nil))
             (final-grp (cdar (last res))))
	  ;(topic-mesh-graph final-grp 'FM))
	  (^ (msg-with-peers-in-grp pld final-grp)
             (endp (set-difference-equal
		    peers
		    (acl2::flatten (topic-mesh-graph final-grp 'FM)))))))


;;------------------------------------------------------------------------------------
;; Fanout tests
;;------------------------------------------------------------------------------------



;; Spin up the following network
;;     AN  \         / P2
;;   MX -----PT-----P1-- P3
;;   TI/          \ P4
;; Left peers all subscribe to FM, right peers to PL
;; PT produces a message in PL, then adds P1 to its fanout and forwards it.
;; Right peers have all formed a mesh and the message eventually reaches
;; everyone on the right.

(check= t
        (b* ((peers1 '(AN MX PT TI))
             (grp1 (init-grp-nbrs peers1 4))
             (peers2 '(P1 P2 P3 P4))
             (grp2 (init-grp-nbrs peers2 4))
             (pld '(FULLMSG100 PID100 PL PT))
             (evnts
              (network-propagator
	       (app `((MX JOIN FM)
		      (AN JOIN FM)
		      (PT JOIN FM)
		      (TI JOIN FM)
		      (P1 JOIN PL)
		      (P2 JOIN PL)
		      (P3 JOIN PL)
		      (P4 JOIN PL))
		    (multiple-hbms (app peers1 peers2) 2)
                    `((PT SND P1 CONNECT1 (FM))
		      (PT APP PL ,pld))) ;;PT produces a PL message, will
               ;;need to forward it to the only PL subscribed nbr P1, adding it
               ;;to its fanout.
	       nil))
             (res (run-network (app grp1 grp2) evnts 1000 *factors* 40 nil))
             (final-grp (cdar (last res)))
             (pt-state (cdr (assoc-equal 'PT final-grp)))
             (pt-fanout (nbr-topic-state-topic-fanout
                           (peer-state-nts pt-state)))
             (pt-mesh (nbr-topic-state-topic-mesh
                           (peer-state-nts pt-state)))
             ((unless (in 'P1 (cdr (assoc-equal 'PL pt-fanout)))) nil)
             ;; P1 is in PT Fanout of PL
             (pl-grp (acl2::fal-extract peers2 final-grp)))
	  (^ (msg-with-peers-in-grp pld pl-grp)
             (endp (set-difference-equal
		    peers2
		    (acl2::flatten (topic-mesh-graph pl-grp 'PL))))
             (< (params-dlow (car *factors*))
                (+ (len (cdr (assoc-equal 'PL pt-fanout)))
                   (len (cdr (assoc-equal 'FM pt-mesh))))))))

;; wait for HBM to add fanout
(check= t
        (b* ((peers '(P1 P2 P3 P4))
             (grp (init-grp-nbrs peers 4)) ;; grp doesn't have PT
             (pld '(FULLMSG100 PID100 PL PT))
             (evnts
              (network-propagator
	       (app `((PT JOIN FM) ;; grp peers don't know about PT
		      (P1 JOIN PL)
		      (P2 JOIN PL)
		      (P3 JOIN PL)
		      (P4 JOIN PL)
                      (PT SND P1 CONNECT1 (FM))
	              (PT APP PL ,pld)
                      ;;PT produces a PL message, will
                      ;;need to forward it to all only PL subscribed nbr P1, adding it
                      ;;to its fanout.
                      (P2 SND PT CONNECT1 (PL))
                      (P3 SND PT CONNECT1 (PL))
                      (P4 SND PT CONNECT1 (PL)))
                    (multiple-hbms (cons 'PT peers) 2))
               ;;after HBMs, we expect all peers to be in Pt's fanout due to
               ;;fanout maintenance.
	       nil))
             (res (run-network grp evnts 1000 *factors* 40 nil))
             (final-grp (cdar (last res)))
             (pt-state (cdr (assoc-equal 'PT final-grp)))
             (pt-fanout (nbr-topic-state-topic-fanout
                           (peer-state-nts pt-state)))
             (pt-mesh (nbr-topic-state-topic-mesh
                           (peer-state-nts pt-state))))
          (^ (endp (set-difference-equal
                    '(P1 P2 P3 P4)
                    (cdr (assoc-equal 'PL pt-fanout))))
             (< (params-dlow (car *factors*))
                (+ (len (cdr (assoc-equal 'PL pt-fanout)))
                   (len (cdr (assoc-equal 'FM pt-mesh))))))))

(defconst *high-fanout-ttl* 100)

;; wait for HBM to add fanout, then wait for FANOUTTTL to remove fanout
(check= t
        (b* ((peers '(P1 P2 P3 P4))
             (grp (init-grp-nbrs peers 4)) ;; grp doesn't have PT
             (pld '(FULLMSG100 PID100 PL PT))
             (evnts
              (network-propagator
	       (app `((PT JOIN FM) ;; grp peers don't know about PT
		      (P1 JOIN PL)
		      (P2 JOIN PL)
		      (P3 JOIN PL)
		      (P4 JOIN PL)
                      (PT SND P1 CONNECT1 (FM))
	              (PT APP PL ,pld)
                      ;;PT produces a PL message, will
                      ;;need to forward it to all only PL subscribed nbr P1, adding it
                      ;;to its fanout.
                      (P2 SND PT CONNECT1 (PL))
                      (P3 SND PT CONNECT1 (PL))
                      (P4 SND PT CONNECT1 (PL)))
                    (multiple-hbms (cons 'PT peers) 2)
                    ;; by now PX are all in PT's fanout
                    (multiple-hbms (cons 'PT peers) *high-fanout-ttl*))
                    ;; 100 > fanoutttl, so fanout should get removed)
	       nil))
             (res (run-network grp evnts 1000 *factors* 40 nil))
             (final-grp (cdar (last res)))
             (pt-state (cdr (assoc-equal 'PT final-grp)))
             (pt-fanout (nbr-topic-state-topic-fanout
                           (peer-state-nts pt-state))))
          (endp (cdr (assoc-equal 'PL pt-fanout)))))


(create-map* (lambda (p tp) `(,p APP ,tp (FULL PID ,tp ,p)))
             lopp
             loevp
             (:name mk-app-msgs)
	     (:fixed-vars ((topicp tp))))
  

;; Opportunistic grafting

;; (check= t
;;         (b* ((peers (map* mk-peers (natlist 50)))
;;              (grp (init-grp-nbrs peers 50)) ;; super densely connected, so
;;              ;; peers can choose who to add in mesh
;;              (evnts
;;               (network-propagator
;; 	       (app (map* mk-joins peers 'FM) ;; all 50 peers subscribed to FM
;;                     (multiple-hbms peers 3)
;;                     ;;wait for 3 HBMs to form
;;                     ;;random meshes
;;                     (map* mk-app-msgs (grab 10 (reverse peers)) 'FM)
;;                     ;;P1 to P10 publish messages, while the others are
;;                     ;;squatting sybils
;;                     (multiple-hbms peers 3)
;;                     (multiple-hbms peers 3)
;;                     (multiple-hbms peers 3)
;;                     (multiple-hbms peers 3)
;;                     (multiple-hbms peers 3))
;; 	       nil))
;;              (res (run-network grp evnts 100000 *factors* 40 nil))
;;              (final-grp (cdar (last res))))
;;           final-grp)
;;              (pt-state (cdr (assoc-equal 'PT final-grp)))
;;              (pt-fanout (nbr-topic-state-topic-fanout
;;                            (peer-state-nts pt-state))))
;;           (endp (cdr (assoc-equal 'PL pt-fanout)))))


;;------------------------------------------------------------------------------------
;; Cache tests
;;------------------------------------------------------------------------------------

(check= t
        (b* ((peers '(AN MX))
             (grp (init-grp-nbrs peers 2))
             (pld '(FULLMSG100 PID100 FM MX))
             (evnts
              (network-propagator
	       (app '((AN JOIN FM)
		      (MX JOIN FM))
		    (multiple-hbms peers 2)
		    '((AN APP FM (FULLMSG100 PID100 FM AN))
                      (AN APP FM (FULLMSG101 PID101 FM AN))
                      (AN APP FM (FULLMSG102 PID102 FM AN))
                      (AN APP FM (FULLMSG103 PID103 FM AN))
                      (AN APP FM (FULLMSG104 PID104 FM AN)))
                    (multiple-hbms peers 1)
                    '((AN APP FM (FULLMSG105 PID105 FM AN))
                      (AN APP FM (FULLMSG106 PID106 FM AN)))
                    (multiple-hbms peers 1)
                    '((AN APP FM (FULLMSG107 PID107 FM AN))
                      (AN APP FM (FULLMSG108 PID108 FM AN))
                      (AN APP FM (FULLMSG109 PID109 FM AN))
                      (AN APP FM (FULLMSG110 PID110 FM AN))))
	       nil))
             (res (run-network grp evnts 1000 *factors* 40 nil))
             (final-grp (cdar (last res)))
             (max-msgs-state (peer-state-mst
                              (cdr (assoc-equal 'MX final-grp))))
             (max-pld-cache (msgs-state-pld-cache max-msgs-state))
             (max-hwindows  (msgs-state-hwindows max-msgs-state)))
          (and  (= (len max-pld-cache) 11)
                (equal (car max-hwindows) 4))))
