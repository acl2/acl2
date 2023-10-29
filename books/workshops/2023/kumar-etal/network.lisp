(in-package "ACL2S")
(include-book "peer-state")

;;group of peers
(defdata group (map peer peer-state))

(definecd lookup-state (p :peer g :group ) :peer-state
  (b* ((res (mget p g))
       ((when (null res)) (new-peer-state)))
    res))

(defdata egl (alistof evnt group))

(property egl-loevs (egl :egl)
  :testing? nil
  (loevp (strip-cars egl)))

(property egl-cadr (egl :egl)
  :testing? nil
  (groupp (cdar egl)))

(property egl-lastgrp (egl :egl)
  :testing? nil
  (groupp (cdar (last egl))))

(property snd-rcv-evnt (p1 p2 x y :all)
  (=> (evntp `(,p1 SND ,p2 ,x ,y))
      (loevp (app `((,p2 RCV ,p1 ,x ,y)
                    (,p1 SND ,p2 ,x ,y)))))
  :hints (("Goal" :in-theory (enable evntp))))

(definecd network-propagator (evnts acc :loev) :loev
  :skip-tests t
  :body-contracts-hints (("Goal" :in-theory (enable evntp)))
  :timeout 2000
  (match evnts
    (() (reverse acc))
    (((p1 'SND p2 x y) . rst)
     ;; we assume instantaneous message transmissions, with SND
     ;; followed immediately by RCV
     (network-propagator
      rst
      (app `((,p2 RCV ,p1 ,x ,y)
             (,p1 SND ,p2 ,x ,y))
           acc)))
    ((evnt . rst)
     (network-propagator rst (cons evnt acc)))))

;; weaving list of events 
(definecd splice (x y :loev) :loev
  (match (list x y)
    ((() ()) '())
    ((() y) y)
    ((x ()) x)
    (((a . xs) (b . ys))
     (append `(,a ,b) (splice xs ys)))))

(encapsulate
  ()
  (local
   (defthm car-evntp
     (=> (evntp ev)
         (peerp (car ev)))
     :hints (("Goal" :in-theory (enable evntp)))))
  (local
   (defthm cons-evntp
     (=> (evntp ev)
         (consp ev))
     :hints (("Goal" :in-theory (enable evntp)))))

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
               s))))))

(definecd run-network-gr (gr :group evnts :loev i :nat twpm :twp s :nat) :group
  :ic (is-valid-twp twpm)
  :body-contracts-hints
  (("Goal" :do-not-induct t :in-theory (enable transition)))
  :timeout 600
  :skip-tests t
  (cdr (car (reverse (run-network gr evnts i twpm s)))))

