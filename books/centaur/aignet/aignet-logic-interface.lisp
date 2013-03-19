

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
  (duplicity :ro (tags aignet)))

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
  (to-id (len (lookup-pi n aignet))))

(define outnum->id ((n natp)
                   (aignet aignet-well-formedp))
  :guard (< n (num-outs aignet))
  :returns (id idp)
  :enabled t
  (to-id (len (lookup-po n aignet))))

(define regnum->ro ((n natp)
                    (aignet aignet-well-formedp))
  :guard (< n (num-regs aignet))
  :returns (id idp)
  :enabled t
  (to-id (len (lookup-ro n aignet))))

(define id-existsp ((id idp) (aignet aignet-well-formedp))
  :enabled t
  (aignet-idp id aignet))

(define id->type ((id idp)
                  (aignet aignet-well-formedp))
  :guard (id-existsp id aignet)
  :enabled t
  (node->type (car (lookup-node id aignet))))

(define io-id->regp ((id idp)
                     (aignet aignet-well-formedp))
  :guard (and (id-existsp id aignet)
              (or (eql (id->type id aignet) (in-type))
                  (eql (id->type id aignet) (out-type))))
  :enabled t
  (io-node->regp (car (lookup-node id aignet))))

(define co-id->fanin ((id idp)
                      (aignet aignet-well-formedp))
  :guard (and (id-existsp id aignet)
              (eql (id->type id aignet) (out-type)))
  :enabled t
  (co-node->fanin (car (lookup-node id aignet))))

(define gate-id->fanin0 ((id idp)
                        (aignet aignet-well-formedp))
  :guard (and (id-existsp id aignet)
              (eql (id->type id aignet) (gate-type)))
  :enabled t
  (gate-node->fanin0 (car (lookup-node id aignet))))

(define gate-id->fanin1 ((id idp)
                        (aignet aignet-well-formedp))
  :guard (and (id-existsp id aignet)
              (eql (id->type id aignet) (gate-type)))
  :enabled t
  (gate-node->fanin1 (car (lookup-node id aignet))))

(define io-id->ionum ((id idp) (aignet aignet-well-formedp))
  :guard (and (id-existsp id aignet)
              (or (eql (id->type id aignet) (in-type))
                  (and (eql (id->type id aignet) (out-type))
                       (eql (io-id->regp id aignet) 0))))
  :enabled t
  (b* (((cons node rest) (lookup-node id aignet)))
    (io-node->ionum node rest)))

(define reg-id->ri ((id idp)
                    (aignet aignet-well-formedp))
  :guard (and (id-existsp id aignet)
              (eql (id->type id aignet) (in-type))
              (eql (io-id->regp id aignet) 1))
  :returns (id idp)
  :enabled t
  (to-id (len (lookup-reg->ri id aignet))))

(define ri-id->reg ((id idp)
                    (aignet aignet-well-formedp))
  :guard (and (id-existsp id aignet)
              (eql (id->type id aignet) (out-type))
              (eql (io-id->regp id aignet) 1))
  :returns (id idp)
  :enabled t
  (id-fix ;; so that the result is an ID regardless of malformed input
   (ri-node->reg (car (lookup-node id aignet)))))



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
                                 (id-existsp id aignet))
                     :measure (acl2::two-nats-measure
                               (id-val id) 0)
                     :hints (("goal" :in-theory (enable co-orderedp
                                                        gate-orderedp)))))
     (let ((type (id->type id aignet)))
       (cond ((eql type (out-type))
              (if (co-orderedp id aignet)
                  (lit->phase (co-id->fanin id aignet) aignet)
                0))
             ((eql type (gate-type))
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
  (cons (gate-node (aignet-lit-fix f0 aignet)
                   (aignet-lit-fix f1 aignet))
        aignet)
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
  (cons (po-node (aignet-lit-fix f aignet))
        aignet)
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-out
    (implies (and (aignet-nodes-ok aignet)
                  (fanout-litp f aignet))
             (aignet-nodes-ok (cons (po-node f) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet-add-regin ((f litp)
                          (regid idp)
                          (aignet aignet-well-formedp))
  :guard (and (fanout-litp f aignet)
              (id-existsp regid aignet)
              (eql (id->type regid aignet) (in-type))
              (eql (io-id->regp regid aignet) 1))
  (cons (ri-node (aignet-lit-fix f aignet)
                 (aignet-id-fix regid aignet))
        aignet)
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-regin
    (implies (and (aignet-nodes-ok aignet)
                  (fanout-litp f aignet)
                  (aignet-idp regid aignet))
             (aignet-nodes-ok (cons (ri-node f regid) aignet)))
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
