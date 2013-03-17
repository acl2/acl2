

(in-package "AIGNET$A")

(include-book "aignet-logic")
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable sets::double-containment)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           sets::double-containment
                           sets::sets-are-true-lists
                           make-list-ac
                           acl2::duplicity-when-non-member-equal)))

(local (in-theory (disable true-listp-update-nth
                           acl2::nth-with-large-index)))


(define aignet-well-formedp (aignet)
  :enabled t
  (and (node-listp aignet)
       (aignet-nodes-ok aignet)))

(define num-nodes ((aignet aignet-well-formedp))
  (+ 1 (len aignet))
  :enabled t)

(define num-ins ((aignet aignet-well-formedp))
  (duplicity :pi (tags aignet))
  :enabled t)

(define num-regs ((aignet aignet-well-formedp))
  :enabled t
  (reg-count aignet))

(define num-outs ((aignet aignet-well-formedp))
  (duplicity :po (tags aignet))
  :enabled t)

(define num-regins ((aignet aignet-well-formedp))
  (duplicity :ri (tags aignet))
  :enabled t)

(define num-gates ((aignet aignet-well-formedp))
  (duplicity :gate (tags aignet))
  :enabled t)

(define innum->id ((n natp)
                   (aignet aignet-well-formedp))
  :guard (< n (num-ins aignet))
  :returns (id idp)
  :enabled t
  (to-id (1- (num-nodes (lookup-pi n aignet))))
  ;; ///
  ;; (defcong nat-equiv equal (innum->id n aignet) 1)
  ;; (defthm lookup-node-of-innum->id-exists
  ;;   (iff (lookup-node (innum->id n aignet) aignet)
  ;;        (< (nfix n) (num-ins aignet))))
  ;; (defthm car-lookup-node-of-innum->id
  ;;   (implies (< (nfix n) (num-ins aignet))
  ;;            (equal (tag (car (lookup-node
  ;;                              (innum->id n aignet)
  ;;                              aignet)))
  ;;                   :pi))
  ;;   :hints(("Goal" :in-theory (enable lookup-pi
  ;;                                     lookup-node
  ;;                                     tags))))
  ;; (defthm num-ins-of-lookup-node-of-innum->id
  ;;   (implies (< (nfix n) (num-ins aignet))
  ;;            (equal (duplicity :pi (tags (cdr (lookup-node
  ;;                                              (innum->id n aignet)
  ;;                                              aignet))))
  ;;                   (nfix n)))
  ;;   :hints(("Goal" :in-theory (enable lookup-pi
  ;;                                     lookup-node
  ;;                                     tags))))
  )

(define outnum->id ((n natp)
                   (aignet aignet-well-formedp))
  :guard (< n (num-outs aignet))
  :returns (id idp)
  :enabled t
  (to-id (1- (num-nodes (lookup-po n aignet))))
  ;; ///
  ;; (defcong nat-equiv equal (outnum->id n aignet) 1)
  ;; (defthm lookup-node-of-outnum->id-exists
  ;;   (iff (lookup-node (outnum->id n aignet) aignet)
  ;;        (< (nfix n) (num-outs aignet))))
  ;; (defthm car-lookup-node-of-outnum->id
  ;;   (implies (< (nfix n) (num-outs aignet))
  ;;            (equal (tag (car (lookup-node
  ;;                              (outnum->id n aignet)
  ;;                              aignet)))
  ;;                   :po))
  ;;   :hints(("Goal" :in-theory (enable lookup-po
  ;;                                     lookup-node
  ;;                                     tags))))
  ;; (defthm num-outs-of-lookup-node-of-outnum->id
  ;;   (implies (< (nfix n) (num-outs aignet))
  ;;            (equal (duplicity :po (tags (cdr (lookup-node
  ;;                                              (outnum->id n aignet)
  ;;                                              aignet))))
  ;;                   (nfix n)))
  ;;   :hints(("Goal" :in-theory (enable lookup-po
  ;;                                     lookup-node
  ;;                                     tags))))
  )

(define regnum->ri ((n natp)
                   (aignet aignet-well-formedp))
  :guard (< n (num-regs aignet))
  :returns (id idp)
  :enabled t
  (to-id (1- (num-nodes (lookup-ri n aignet))))
  ;; ///
  ;; (defcong nat-equiv equal (regnum->ri n aignet) 1)
  ;; (defthm lookup-node-of-regnum->ri-exists
  ;;   (iff (lookup-node (regnum->ri n aignet) aignet)
  ;;        (< (nfix n) (num-regins aignet))))
  ;; (defthm car-lookup-node-of-regnum->ri
  ;;   (implies (< (nfix n) (num-regins aignet))
  ;;            (equal (tag (car (lookup-node
  ;;                              (regnum->ri n aignet)
  ;;                              aignet)))
  ;;                   :ri))
  ;;   :hints(("Goal" :in-theory (enable lookup-ri
  ;;                                     lookup-node
  ;;                                     tags))))
  ;; (defthm num-regins-of-lookup-node-of-regnum->ri
  ;;   (implies (< (nfix n) (num-regins aignet))
  ;;            (equal (duplicity :ri (tags (cdr (lookup-node
  ;;                                              (regnum->ri n aignet)
  ;;                                              aignet))))
  ;;                   (nfix n)))
  ;;   :hints(("Goal" :in-theory (enable lookup-ri
  ;;                                     lookup-node
  ;;                                     tags))))
  )

(define regnum->ro ((n natp)
                   (aignet aignet-well-formedp))
  :guard (< n (num-regs aignet))
  :returns (id idp)
  :enabled t
  (to-id (1- (num-nodes (lookup-ro n aignet))))
  ;; ///
  ;; (defcong nat-equiv equal (regnum->ro n aignet) 1)
  ;; (defthm car-lookup-node-of-regnum->ro
  ;;   (implies (lookup-node (regnum->ro n aignet) aignet)
  ;;            (equal (tag (car (lookup-node
  ;;                              (regnum->ro n aignet)
  ;;                              aignet)))
  ;;                   :ro))
  ;;   :hints(("Goal" :in-theory (enable lookup-ro
  ;;                                     lookup-node
  ;;                                     tags))))
  ;; (defthm reg-count-of-lookup-node-of-regnum->ro
  ;;   (implies (lookup-node (regnum->ro n aignet) aignet)
  ;;            (equal (reg-count (cdr (lookup-node
  ;;                                  (regnum->ro n aignet)
  ;;                                  aignet)))
  ;;                   (nfix n)))
  ;;   :hints(("Goal" :in-theory (enable lookup-ro
  ;;                                     lookup-node
  ;;                                     tags))))
  )


(define id->type ((id idp)
                  (aignet aignet-well-formedp))
  :guard (< (id-val id) (num-nodes aignet))
  :enabled t
  (node->type (car (lookup-node id aignet))))

(define io-id->regp ((id idp)
                     (aignet aignet-well-formedp))
  :guard (and (< (id-val id) (num-nodes aignet))
              (or (int= (id->type id aignet) (in-type))
                  (int= (id->type id aignet) (out-type))))
  :enabled t
  (io-node->regp (car (lookup-node id aignet))))

(define co-id->fanin ((id idp)
                      (aignet aignet-well-formedp))
  :guard (and (< (id-val id) (num-nodes aignet))
              (int= (id->type id aignet) (out-type)))
  :enabled t
  (co-node->fanin (car (lookup-node id aignet))))

(define gate-id->fanin0 ((id idp)
                        (aignet aignet-well-formedp))
  :guard (and (< (id-val id) (num-nodes aignet))
              (int= (id->type id aignet) (gate-type)))
  :enabled t
  (gate-node->fanin0 (car (lookup-node id aignet))))

(define gate-id->fanin1 ((id idp)
                        (aignet aignet-well-formedp))
  :guard (and (< (id-val id) (num-nodes aignet))
              (int= (id->type id aignet) (gate-type)))
  :enabled t
  (gate-node->fanin1 (car (lookup-node id aignet))))

(define io-id->ionum ((id idp) (aignet aignet-well-formedp))
  :guard (and (< (id-val id) (num-nodes aignet))
              (or (int= (id->type id aignet) (in-type))
                  (int= (id->type id aignet) (out-type))))
  :enabled t
  (b* (((cons node rest) (lookup-node id aignet)))
    (io-node->ionum node rest)))

(define fanout-litp ((lit litp) (aignet aignet-well-formedp))
  :enabled t
  (aignet-litp lit aignet))
  


(defsection id->phase
  (mutual-recursion
   (defun lit->phase (lit aignet)
     (declare (xargs :guard (and (aignet-well-formedp aignet)
                                 (litp lit)
                                 (fanout-litp lit aignet))
                     :verify-guards nil
                     :measure (acl2::two-nats-measure
                               (id-val (lit-id lit)) 1)))
     (b-xor (lit-neg lit)
            (id->phase (lit-id lit) aignet)))

   (defun id->phase (id aignet)
     (declare (Xargs :guard (and (aignet-well-formedp aignet)
                                 (idp id)
                                 (< (id-val id) (num-nodes aignet)))
                     :measure (acl2::two-nats-measure
                               (id-val id) 0)
                     :hints (("goal" :in-theory (enable co-orderedp
                                                        gate-orderedp)))))
     (let ((type (id->type id aignet)))
       (cond ((int= type (out-type))
              (if (co-orderedp id aignet)
                  (lit->phase (co-id->fanin id aignet) aignet)
                0))
             ((int= type (gate-type))
              (if (gate-orderedp id aignet)
                  (b-and (lit->phase (gate-id->fanin0 id aignet) aignet)
                         (lit->phase (gate-id->fanin1 id aignet) aignet))
                0))
             (t 0)))))

  (in-theory (disable lit->phase id->phase))

  (defthm bitp-of-lit->phase
    (bitp (lit->phase lit aignet))
    :hints (("goal" :expand (lit->phase lit aignet))))

  (defthm bitp-of-id->phase
    (bitp (id->phase id aignet))
    :hints (("goal" :expand (id->phase id aignet))))

  (verify-guards id->phase)

  (flag::make-flag phase-flg id->phase
                   :hints (("goal" :in-theory (enable co-orderedp
                                                      gate-orderedp))))

  (defthm-phase-flg
    (defthm id->phase-of-suffix
      (implies (and (suffixp aignet new)
                    (<= (id-val id) (len aignet)))
               (equal (id->phase id new)
                      (id->phase id aignet)))
      :hints ('(:expand ((:free (aignet)
                          (id->phase id aignet)))
                :in-theory (enable gate-orderedp
                                   co-orderedp)))
      :flag id->phase)
    (defthm lit->phase-of-suffix
      (implies (and (suffixp aignet new)
                    (<= (id-val (lit-id lit)) (len aignet)))
               (equal (lit->phase lit new)
                      (lit->phase lit aignet)))
      :hints ('(:expand ((:free (aignet)
                          (lit->phase lit aignet)))))
      :flag lit->phase))

  (defthm id->phase-of-cons
    (implies (<= (id-val id) (len aignet))
             (equal (id->phase id (cons node aignet))
                    (id->phase id aignet)))
    :hints (("goal" :use ((:instance id->phase-of-suffix
                           (new (cons node aignet))
                           (aignet aignet)))
             :expand ((:free (a b)
                       (suffixp a (cons b a)))))))

  (defthm lit->phase-of-cons
    (implies (<= (id-val (lit-id lit)) (len aignet))
             (equal (lit->phase lit (cons node aignet))
                    (lit->phase lit aignet)))
    :hints (("goal" :use ((:instance lit->phase-of-suffix
                           (new (cons node aignet))
                           (aignet aignet)))
             :expand ((:free (a b)
                       (suffixp a (cons b a))))))))

(define aignet-add-in ((aignet aignet-well-formedp))
  (cons (pi-node) aignet)
  :enabled t
  ///
  (defthm aignet-well-formedp-of-aignet-add-in
    (implies (aignet-nodes-ok aignet)
             (aignet-nodes-ok (cons '(:pi) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet-add-reg ((aignet aignet-well-formedp))
  (cons (ro-node) aignet)
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-reg
    (implies (aignet-nodes-ok aignet)
             (aignet-nodes-ok (cons '(:ro) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet-add-gate ((f0 litp)
                         (f1 litp)
                         (aignet aignet-well-formedp))
  :guard (and (fanout-litp f0 aignet)
              (fanout-litp f1 aignet))
  (cons (gate-node f0 f1) aignet)
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-gate
    (implies (and (aignet-nodes-ok aignet)
                  (fanout-litp f0 aignet)
                  (fanout-litp f1 aignet))
             (aignet-nodes-ok (cons (gate-node f0 f1) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet-add-out ((f litp)
                        (aignet aignet-well-formedp))
  :guard (fanout-litp f aignet)
  (cons (po-node f) aignet)
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-out
    (implies (and (aignet-nodes-ok aignet)
                  (fanout-litp f aignet))
             (aignet-nodes-ok (cons (po-node f) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet-add-regin ((f litp)
                          (aignet aignet-well-formedp))
  :guard (fanout-litp f aignet)
  (cons (ri-node f) aignet)
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-regin
    (implies (and (aignet-nodes-ok aignet)
                  (fanout-litp f aignet))
             (aignet-nodes-ok (cons (ri-node f) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet-clear (aignet)
  :enabled t
  (declare (ignore aignet))
  nil)

(define aignet-init ((max-outs natp)
                     (max-regs natp)
                     (max-ins natp)
                     (max-nodes posp)
                     aignet)
  :enabled t
  (declare (ignore max-outs max-regs max-ins max-nodes aignet))
  nil)
