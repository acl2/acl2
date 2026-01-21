(in-package "ACL2S")
(include-book "utils")

;; peer state in a Broadcast Network
(defdata ps-bn (record
               (pubs . lot)
               (subs . lot)
               (seen . lom)))

;; a broadcast network state maps peers to their states
(defdata s-bn (map peer ps-bn))

(property s-bn-check (st :s-bn i :nat)
          (=> (mget i st)
              (ps-bnp (mget i st)))
          :rule-classes :forward-chaining)


(definecd new-bn-mssgp (m :mssg s :s-bn) :bool
  :function-contract-hints
  (("Goal" :in-theory (enable acl2::maximal-records-theory)))
  (v (endp s)
     (^ (nin m (mget :seen (cdar s)))
        (new-bn-mssgp m (cdr s)))))

;; Broadcast conditions
(definec broadcast-bn-pre (m :mssg s :s-bn) :bool
  (b* ((origin (mget :or m))
       (origin-st (mget origin s)))
    (^ (new-bn-mssgp m s)
       origin-st
       (in (mget :tp m)
           (mget :pubs origin-st)))))

(definecd broadcast-help (m :mssg st :s-bn) :s-bn
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
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

(definecd broadcast (m :mssg s :s-bn) :s-bn
  :ic (broadcast-bn-pre m s)
  (broadcast-help m s))

(definecd broadcast-partial-help (m :mssg ps :lop st :s-bn) :s-bn
  :function-contract-hints (("Goal" :in-theory (enable
                                                acl2::maximal-records-theory)))
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

(definecd broadcast-partial (m :mssg ps :lop s :s-bn) :s-bn
  :ic (new-bn-mssgp m s)
  (broadcast-partial-help m ps s))

(definecd join-bn (p :peer pubs subs :lot st :s-bn) :s-bn
  :function-contract-hints (("Goal" :in-theory (enable ps-bnp)))
  :ic (! (mget p st))
  (mset p (ps-bn pubs subs '()) st))


(property leave-bn-helper (p :peer s :s-bn)
  :h (^ (mget p s)
        (!= p (car (car s))))
  (mget p (cdr s))
  :hints
  (("Goal" :in-theory
    (enable acl2::maximal-records-theory))))

(definecd leave-bn (p :peer s :s-bn) :s-bn
  :function-contract-hints
  (("Goal" :in-theory (enable acl2::maximal-records-theory)))
  :ic (mget p s)
  (match s
    (((!p . &) . rst) rst)
    ((r . rst) (cons r (leave-bn p rst)))))


(property union-tops (ts1 ts2 :lot)
  (lotp (union-equal ts1 ts2)))

(definecd subscribe-bn (p :peer topics :lot s :s-bn) :s-bn
  :ic (mget p s)
  (let ((pst (mget p s)))
    (mset p
          (mset :subs (union-equal (mget :subs pst) topics) pst)
          s)))

(definecd unsubscribe-bn (p :peer topics :lot s :s-bn) :s-bn
  :ic (mget p s)
  (let ((pst (mget p s)))
    (mset p
          (mset :subs (set-difference-equal (mget :subs pst) topics) pst)
          s)))





(check=
  (b* ((ts '(FM DS SEC PL))
       ;; add peers
       (st (join-bn 3 ts ts
                    (join-bn 2 ts ts
                             (join-bn 1 ts ts '()))))
       ;; broadcast messages
       (st (broadcast (mssg "Hisss" 'FM 1)
                      (broadcast (mssg "Meow" 'FM 3)
                                 (broadcast (mssg "Woof" 'FM 1)
                                            (broadcast (mssg "Grrr" 'FM 2) st)))))
       ;; 2 leaves and then rejoins, forgetting its seen cache, simulating a hard reset
       (st (join-bn 2 ts ts
                    (leave-bn 2 st)))
       (st (broadcast (mssg "Mooo" 'FM 3)
                      st)))
    st)
  '((1 (:0tag . ps-bn)
    (:pubs fm ds sec pl)
    (:seen ((:0tag . mssg)
            (:or . 1)
            (:pld . "Hisss")
            (:tp . fm))
           ((:0tag . mssg)
            (:or . 1)
            (:pld . "Woof")
            (:tp . fm))
           ((:0tag . mssg)
            (:or . 2)
            (:pld . "Grrr")
            (:tp . fm))
           ((:0tag . mssg)
            (:or . 3)
            (:pld . "Meow")
            (:tp . fm))
           ((:0tag . mssg)
            (:or . 3)
            (:pld . "Mooo")
            (:tp . fm)))
    (:subs fm ds sec pl))
 (2 (:0tag . ps-bn)
    (:pubs fm ds sec pl)
    (:seen ((:0tag . mssg)
            (:or . 3)
            (:pld . "Mooo")
            (:tp . fm)))
    (:subs fm ds sec pl))
 (3 (:0tag . ps-bn)
    (:pubs fm ds sec pl)
    (:seen ((:0tag . mssg)
            (:or . 1)
            (:pld . "Hisss")
            (:tp . fm))
           ((:0tag . mssg)
            (:or . 1)
            (:pld . "Woof")
            (:tp . fm))
           ((:0tag . mssg)
            (:or . 2)
            (:pld . "Grrr")
            (:tp . fm))
           ((:0tag . mssg)
            (:or . 3)
            (:pld . "Meow")
            (:tp . fm))
           ((:0tag . mssg)
            (:or . 3)
            (:pld . "Mooo")
            (:tp . fm)))
    (:subs fm ds sec pl))))
