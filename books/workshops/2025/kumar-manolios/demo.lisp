(in-package "ACL2S")
(include-book "f2b-sim-ref")

;;---------------------------------------------------
;; Broadcast Network state and transition relations
;;---------------------------------------------------

;; A Broadcastnet state is a map from peers to their states
(defdata s-bn (map peer ps-bn))

;; Peers are natural numbers
;; Topics are variables
(defdata-alias peer nat)
(defdata-alias topic var)

;; A Broadcastnet peer state tracks topics it publishes in,
;; topics it subscribes to, and messages it has seen.
(defdata ps-bn (record
                (pubs . lot)
                (subs . lot)
                (seen . lom)))

(defdata lot (listof topic))
(defdata lom (listof mssg))

;; A message contains a payload,
;; topic and an originating peer
(defdata mssg (record
               (pld . string)
               (tp . topic)
               (or . peer)))

;; We define the transition relation rel-step-bn as follows : Given Broadcastnet
;; (s-bn) states s and u, peer p, lists of topics pubs, subs and topics,
;; and message m, (rel-step-bn p pubs subs topics m s u) iff one of the
;; several s-bn transitions holds.

(definec rel-step-bn (s u :s-bn) :bool
  (v (rel-skip-bn s u)
     (rel-broadcast-partial-bn s u)
     (rel-subscribe-bn s u)
     (rel-unsubscribe-bn s u)
     (rel-leave-bn s u)
     (rel-join-bn s u)))

(definecd rel-skip-bn (s u :s-bn) :bool
  (== u s))

(definecd rel-broadcast-partial-bn (s u :s-bn) :bool
  (^ (br-mssg-witness s u)
     (new-bn-mssgp (br-mssg-witness s u) s)
     (== u (broadcast-partial (br-mssg-witness s u)
                              (brd-receivers-bn (br-mssg-witness s u) u)
                              s))))

(definecd rel-broadcast-bn (s u :s-bn) :bool
  (^ (br-mssg-witness s u)
     (broadcast-bn-pre (br-mssg-witness s u) s)
     (== u (broadcast (br-mssg-witness s u) s))))

(defdata maybe-mssg (v nil mssg))
;; Finds the message that was broadcast in state s.
(definec br-mssg-witness (s u :s-bn) :maybe-mssg
  (cond
   ((v (endp s) (endp u)) nil)
   ((== (car s) (car u)) (br-mssg-witness (cdr s) (cdr u)))
   (t (car (set-difference-equal (mget :seen (cdar u))
                                 (mget :seen (cdar s)))))))


(definec broadcast-bn-pre (m :mssg s :s-bn) :bool
  (b* ((origin (mget :or m))
       (origin-st (mget origin s)))
    (^ (new-bn-mssgp m s)
       origin-st
       (in (mget :tp m)
           (mget :pubs origin-st)))))

;; A message is broadcast if it is new i.e. not already in the network.
(definecd new-bn-mssgp (m :mssg s :s-bn) :bool
  (v (endp s)
     (^ (nin m (mget :seen (cdar s)))
        (new-bn-mssgp m (cdr s)))))

;; Broadcast m to all peers in ps
(definecd broadcast-partial (m :mssg ps :lop s :s-bn) :s-bn
  :ic (new-bn-mssgp m s)
  (broadcast-partial-help m ps s))

(definecd broadcast-partial-help (m :mssg ps :lop st :s-bn) :s-bn
  (match st
    (() nil)
    (((p . pst) . rst)
     (cons `(,p . ,(if (== p (car ps))
                       (mset :seen
                             (insert-unique m (mget :seen pst))
                             pst)
                     pst))
           (broadcast-partial-help m
                                   (if (== p (car ps))
                                       (cdr ps)
                                     ps)
                                   rst)))))



(definecd broadcast (m :mssg s :s-bn) :s-bn
  :ic (broadcast-bn-pre m s)
  (broadcast-help m s))

(definecd broadcast-help (m :mssg st :s-bn) :s-bn
  (match st
    (() nil)
    (((p . pst) . rst)
     (cons `(,p . ,(if (v (in (mget :tp m)
                              (mget :subs pst))
                          (== p (mget :or m)))
                       (mset :seen
                             (insert-unique m (mget :seen pst))
                             pst)
                     pst))
           (broadcast-help m rst)))))

(definecd rel-subscribe-bn (s u :s-bn) :bool
  (^ (bn-topics-witness s u)
     (mget (car (bn-topics-witness s u)) s)
     (== u (subscribe-bn (car (bn-topics-witness s u))
                         (cdr (bn-topics-witness s u))
                         s))))

(defdata maybe-ptops (v nil (cons peer lot)))
(definec bn-topics-witness (s u :s-bn) :maybe-ptops
  (cond
   ((v (endp s) (endp u)) nil)
   ((== (car s) (car u)) (bn-topics-witness (cdr s) (cdr u)))
   ((^ (== (caar s)
           (caar u))
       (set-difference-equal (mget :subs (cdar u))
                             (mget :subs (cdar s))))
    (cons (caar s)
          (set-difference-equal (mget :subs (cdar u))
                                (mget :subs (cdar s)))))
   (t nil)))

(definecd subscribe-bn (p :peer topics :lot s :s-bn) :s-bn
  :ic (mget p s)
  (let ((pst (mget p s)))
    (mset p
          (mset :subs (union-equal (mget :subs pst) topics) pst)
          s)))


;; Notice that to find the topics unsubscribed, we simply flip the args to
;; bn-topics-witness
(definecd rel-unsubscribe-bn (s u :s-bn) :bool
  (^ (bn-topics-witness u s)
     (mget (car (bn-topics-witness u s)) s)
     (== u (unsubscribe-bn (car (bn-topics-witness u s))
                           (cdr (bn-topics-witness u s))
                           s))))

(definecd unsubscribe-bn (p :peer topics :lot s :s-bn) :s-bn
  :ic (mget p s)
  (let ((pst (mget p s)))
    (mset p
          (mset :subs (set-difference-equal (mget :subs pst) topics) pst)
          s)))



(definecd rel-join-bn (s u :s-bn) :bool
  (^ (bn-join-witness s u)
     (b* ((p (car (bn-join-witness s u)))
          (pst (cdr (bn-join-witness s u))))
       (^ (! (mget p s))
          (== u (join-bn p
                         (mget :pubs pst)
                         (mget :subs pst)
                         s))))))

(definec bn-join-witness (s u :s-bn) :maybe-ppsbn
  (match (list s u)
    ((() ((q . qst) . &)) `(,q . ,qst))
    ((((p . pst) . rs1)
      ((q . qst) . rs2))
     (cond
      ((== `(,p . ,pst)
           `(,q . ,qst))
       (bn-join-witness rs1 rs2))
      ((!= q p)
       `(,q . ,qst))
      (t nil)))
    (& nil)))

(definecd join-bn (p :peer pubs subs :lot st :s-bn) :s-bn
  :ic (! (mget p st))
  (mset p (ps-bn pubs subs '()) st))


;; Notice that to find the peer that left, we simply flip the args to
;; bn-topics-witness
(definecd rel-leave-bn (s u :s-bn) :bool
  (^ (bn-join-witness u s)
     (mget (car (bn-join-witness u s)) s)
     (== u (leave-bn (car (bn-join-witness u s)) s))))

(definecd leave-bn (p :peer s :s-bn) :s-bn
  :ic (mget p s)
  (match s
    (((!p . &) . rst) rst)
    ((r . rst) (cons r (leave-bn p rst)))))

;;---------------------------------------------------
;; Floods Network state and transition relations
;;---------------------------------------------------

;; A Floodnet state is a map from peers to their states
(defdata s-fn (map peer ps-fn))

;; A Floodnet peer state tracks topics it publishes in, topics it subscribes
;; to, neighboring peer subscriptions, pending messages (that are yet to be
;; processed), and messages it has seen.
(defdata ps-fn
  (record  (pubs . lot)
           (subs . lot)            ;; self subscriptions
           (nsubs . topic-lop-map) ;; nbr topic subscriptions
           (pending . lom)
           (seen . lom)))

(defdata topic-lop-map (map topic lop))
(defdata-alias lop nat-list)

;; The FN step relation
(definec rel-step-fn (s u :s-fn) :bool
  (v (rel-skip-fn s u)
     (rel-produce-fn s u)
     (rel-forward-fn s u)
     (rel-subscribe-fn s u)
     (rel-unsubscribe-fn s u)
     (rel-leave-fn s u)
     (rel-join-fn s u)))

(definecd rel-skip-fn (s u :s-fn) :bool
  (== u s))

(definecd rel-produce-fn (s u :s-fn) :bool
  (rel-produce-help-fn s u (fn-pending-mssgs u)))

(definec rel-produce-help-fn (s u :s-fn ms :lom) :bool
  (match ms
    (() nil)
    ((m . rst)
     (v (^ (produce-fn-pre m s)
           (== u (produce-fn m s)))
        (rel-produce-help-fn s u rst)))))

(definec produce-fn-pre (m :mssg s :s-fn) :bool
  (b* ((origin (mget :or m))
       (origin-st (mget origin s)))
    (^ (new-fn-mssgp m s)
       origin-st
       (in (mget :tp m)
           (mget :pubs origin-st)))))

;; A message is produced if it is new i.e. not already in the network.
(definecd new-fn-mssgp (m :mssg s :s-fn) :bool
  (v (endp s)
     (^ (nin m (mget :seen (cdar s)))
        (nin m (mget :pending (cdar s)))
        (new-fn-mssgp m (cdr s)))))

(definecd produce-fn (m :mssg s :s-fn) :s-fn
  :ic (produce-fn-pre m s)
  (mset (mget :or m)
        (add-pending-psfn m
                          (mget (mget :or m) s))
        s))

(definecd add-pending-psfn (m :mssg pst :ps-fn) :ps-fn
  ;; A message already seen is not forwarded.
  ;; We assume that each messages is augmented with a timestamp such that no
  ;; two messages are the same.
  (if (v (in m (mget :pending pst))
         (in m (mget :seen pst)))
      pst
    (mset :pending
          (cons m (mget :pending pst))
          pst)))




(definecd rel-forward-fn (s u :s-fn) :bool
    (rel-forward-help-fn s u (fn-pending-mssgs s)))

(definec rel-forward-help-fn (s u :s-fn ms :lom) :bool
  (match ms
    (() nil)
    ((m . rst)
     (v (^ (in m (fn-pending-mssgs s))
           (== u (forward-fn (find-forwarder s m) m s)))
        (rel-forward-help-fn s u rst)))))


;; find-forwarder is a witness generating function that finds
;; some peer that forwards the pending message m.
(definec find-forwarder (s :s-fn m :mssg) :peer
    :ic (in m (fn-pending-mssgs s))
    :oc (^ (mget (find-forwarder s m) s)
           (in m (mget :pending (mget (find-forwarder s m) s)))
           (! (new-fn-mssgp m s)))
    (match s
      (((p . &)) p)
      (((p . pst) . rst)
       (if (in m (mget :pending pst))
           p
         (find-forwarder rst m)))))

(definecd forward-fn (p :peer m :mssg s :s-fn) :s-fn
  :ic (^ (mget p s)
         (in m (mget :pending (mget p s))))
  (b* ((tp (mssg-tp m))
       (pst (mget p s))
       (nsubs (mget :nsubs pst))
       (fwdnbrs (mget tp nsubs)))
    (forward-help-fn (update-forwarder-fn p m s)
                     fwdnbrs m)))

(definec update-forwarder-fn (p :peer m :mssg s :s-fn) :s-fn
  (match s
    (() '())
    (((!p . pst) . rst)
     (cons `(,p . ,(forwarder-new-pst pst m)) rst))
    ((r . rst)
     (cons r (update-forwarder-fn p m rst)))))

(definecd forwarder-new-pst (pst :ps-fn m :mssg) :ps-fn
  (mset :seen
        (insert-unique m (mget :seen pst))
        (mset :pending
              (remove-equal m (mget :pending pst))
              pst)))

(definecd forward-help-fn (s :s-fn nbrs :lop m :mssg) :s-fn
  (match s
    (() '())
    (((q . qst) . rst)
     (cons (if (in q nbrs)
               `(,q . ,(add-pending-psfn m qst))
             `(,q . ,qst))
           (forward-help-fn rst nbrs m)))))

(definecd rel-subscribe-fn (s u :s-fn) :bool
  (^ (fn-topics-witness s u)
     (mget (car (fn-topics-witness s u)) s)
     (== u (subscribe-fn (car (fn-topics-witness s u))
                         (cdr (fn-topics-witness s u))
                         s))))

(definecd subscribe-fn (p :peer topics :lot s :s-fn) :s-fn
  :ic (mget p s)
  (let ((pst (mget p s)))
    (set-subs-sfn (ps-fn-nbrs pst)
                  topics
                  p
                  (mset p 
                        (mset :subs (union-equal
                                     (mget :subs pst)
                                     topics)
                              pst)
                        s))))

(definecd set-subs-sfn (nbrs :lop topics :lot p :peer s :s-fn) :s-fn
  (match s
    (() '())
    (((n . pst) . rst)
     (cons `(,n . ,(set-subs-psfn nbrs topics n p pst))
           (set-subs-sfn nbrs topics p rst)))))

(definecd rel-unsubscribe-fn (s u :s-fn) :bool
  (^ (fn-topics-witness u s)
     (mget (car (fn-topics-witness u s)) s)
     (== u (unsubscribe-fn (car (fn-topics-witness u s))
                           (cdr (fn-topics-witness u s))
                           s))))

(definecd unsubscribe-fn (p :peer topics :lot s :s-fn) :s-fn
  :ic (mget p s)
  (let ((pst (mget p s)))
    (set-subs-sfn (ps-fn-nbrs pst)
                  topics
                  p
                  (mset p (mset :subs (set-difference-equal
                                       (mget :subs pst)
                                       topics)
                                pst)
                        s))))

(definecd rel-join-fn (s u :s-fn) :bool
  (^ (fn-join-witness s u)
     (b* ((p (car (fn-join-witness s u)))
          (pst (cdr (fn-join-witness s u)))
          (nbrs (topic-lop-map->lop (mget :nsubs pst))))
       (^ (! (mget p s))
          (nin p nbrs)
          (== u (join-fn p
                         (mget :pubs pst)
                         (mget :subs pst)
                         nbrs
                         s))))))


(defdata maybe-ppsfn (v nil (cons peer ps-fn)))

(definecd join-fn (p :peer pubs subs :lot nbrs :lop s :s-fn) :s-fn
  :ic (^ (! (mget p s))
	 (nin p nbrs))
  (set-subs-sfn nbrs
                subs
                p
                (mset p
                      (new-joinee-st-fn pubs subs nbrs s)
                      s)))


(definecd rel-leave-fn (s u :s-fn) :bool
  (^ (fn-join-witness u s)
     (mget (car (fn-join-witness u s)) s)
     (endp (mget :pending (mget (car (fn-join-witness u s)) s)))
     (== u (leave-fn (car (fn-join-witness u s)) s))))

(definecd leave-fn (p :peer s :s-fn) :s-fn
  :ic (mget p s)
  (match s
    (() '())
    (((!p . &) . rst) rst)
    ((r . rst) (cons r (leave-fn p rst)))))

;;---------------------------------------------------
;; Commitment refinement map
;; from Floodnetwork State to Broadcastnetwork State
;;---------------------------------------------------

;; peer state refinement map
(definecd f2b-st (ps :ps-fn ms :lom) :ps-bn
  (ps-bn (mget :pubs ps)
         (mget :subs ps)
         (set-difference-equal (mget :seen ps) ms)))

(definec f2b-help (s :s-fn ms :lom) :s-bn
  (if (endp s)
      '()
    (cons `(,(caar s) . ,(f2b-st (cdar s) ms))
          (f2b-help (cdr s) ms))))

;; refinement map f2b : s-fn -> s-bn
(definec f2b (s :s-fn) :s-bn
  (f2b-help s (fn-pending-mssgs s)))


;;---------------------------------------------------
;; Combined States and Transition Relations
;;---------------------------------------------------

;; Combined State
(defdata borf (v s-bn s-fn))

;; Intersection of s-bn and s-fn states is the empty map.
(property prop=s-sb-s-fn-nil (x :s-bn :s-fn)
  (null x))

;;---------------------------------------------------
;; B relation between borf states
;;---------------------------------------------------

;; We define the rel-B relation on a union of s-fn and s-bn states as
;; follows.
(definec rel-B (x y :borf) :boolean
  (v (rel-wf x y)
     (== x y)))

(definec rel-wf (x y :borf) :boolean
  (^ (s-fnp x)
     (s-bnp y)
     (good-s-fnp x)
     (== y (f2b x))))

;;---------------------------------------------------
;; Combined Transition relation
;;---------------------------------------------------

;; Relation rel-> is a union of good-rel-step-fn and
;; rel-step-bn relations
(definec rel-> (s u :borf) :bool
  (v (^ (s-fnp s)
        (s-fnp u)
        (good-rel-step-fn s u))
     (^ (s-bnp s)
        (s-bnp u)
        (rel-step-bn s u))))

(definec good-rel-step-fn (s u :s-fn) :bool
  (^ (good-s-fnp s)
     (good-s-fnp u)
     (rel-step-fn s u)))

(definec good-s-fnp (s :s-fn) :bool
  (^ (p!in-nsubs-s-fn s)
     (ordered-seenp s)))

(definec p!in-nsubs-s-fn (s :s-fn) :bool
  (match s
    (() t)
    (((p . pst) . rst)
     (^ (p!in-nsubs-ps-fn p pst)
        (p!in-nsubs-s-fn rst)))))

(definec p!in-nsubs-ps-fn-help (p :peer nsubs :topic-lop-map) :bool
  (match nsubs
    (() t)
    (((& . ps) . rst)
     (^ (! (in p ps))
        (p!in-nsubs-ps-fn-help p rst)))))

(definec ordered-seenp (s :s-fn) :boolean
  (match s
    (() t)
    (((& . pst) . rst)
     (^ (orderedp (mget :seen pst))
        (ordered-seenp rst)))))

(property prop=ordered-seenp-cdar (s :s-fn)
  :h (^ s (ordered-seenp s))
  :b (orderedp (mget :seen (cdar s))))

(definec orderedp (x :tl) :boolean
  (match x
    (() t)
    ((&) t)
    ((a . (b . &)) (^ (<< a b)
                      (orderedp (cdr x))))))

;; We are now ready to prove refinement.
;;---------------------------------------------------
;; WFS 1
;;---------------------------------------------------

(property b-maps-f2b (s :s-fn)
  :h (good-s-fnp s)
  :b (rel-B s (f2b s)))

;;---------------------------------------------------
;; WFS 2
;;---------------------------------------------------

(definec L (s :borf) :borf
  (match s
    (:s-bn s)
    (:s-fn (f2b s))))

(property wfs2 (s w :borf)
  :h (rel-B s w)
  :b (== (L s)
         (L w)))

;;---------------------------------------------------
;; WFS 3
;;---------------------------------------------------

;; exists-v is a witness to the existence of v in our refinement
;; theorem. Given the empty state s, and given (rel-B s w), w is empty
;; as well. So, the only possible transitions from empty w are either
;; skip (producing nil) or join.
;; Otherwise, s and w are non-empty maps.

(definec exists-v (s u w :borf) :borf
  :ic (^ (rel-B s w)
         (rel-> s u))
  (if (null s)
      (if (null u)
          nil
        (exists-nil-v u))
    (exists-cons-v s u w)))

(definec exists-nil-v (u :borf) :borf
  :ic (^ u (rel-> nil u))
  (match u
    (:s-fn (exists-v1 nil u))
    (:s-bn u)))

(definec exists-cons-v (s u w :borf) :borf
  :ic (^ s
         (rel-B s w)
         (rel-> s u))
  (cond
   ((^ (s-bnp s) (s-bnp w)) u)
   ((^ (s-fnp s) (s-bnp w)) (exists-v1 s u))
   ((^ (s-fnp s) (s-fnp w)) u)))

;; Following functions are witnesses to the existence of v in case of
;; non-empty s and w.
(definec exists-v1 (s u :s-fn) :s-bn
  :ic (good-s-fnp s)
  (cond
   ((rel-skip-fn s u) (f2b s))
   ((^ (rel-forward-fn s u)
       (!= (f2b s) (f2b u)))
    (broadcast-partial (br-mssg-witness (f2b s) (f2b u))
                       (brd-receivers-bn
                        (br-mssg-witness (f2b s) (f2b u))
                        (f2b u))
                       (f2b s)))
   (t (f2b u))))


;; Finally, our refinement theorem.

(defun-sk exists-v-wfs (s u w)
  (exists (v)
    (^ (rel-> w v)
       (rel-B u v))))

(property wfs3 (s w u :borf)
  :check-contracts? nil
  :h (^ (rel-B s w)
        (rel-> s u))
  :b (exists-v-wfs s u w))
