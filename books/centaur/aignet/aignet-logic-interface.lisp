

(in-package "AIGNET")

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
                           make-list-ac)))

(local (in-theory (disable true-listp-update-nth
                           acl2::nth-with-large-index)))


(define aignet$a::aignet-well-formedp (aignet)
  :enabled t
  (and (node-listp aignet)
       (aignet-nodes-ok aignet)))

(define aignet$a::num-nodes ((aignet aignet$a::aignet-well-formedp))
  (+ 1 (len aignet))
  :enabled t)

(define aignet$a::num-ins ((aignet aignet$a::aignet-well-formedp))
  (stype-count (pi-stype) aignet)
  :enabled t)

(define aignet$a::num-regs ((aignet aignet$a::aignet-well-formedp))
  :enabled t
  (stype-count (reg-stype) aignet))

(define aignet$a::num-outs ((aignet aignet$a::aignet-well-formedp))
  (stype-count (po-stype) aignet)
  :enabled t)

(define aignet$a::num-nxsts ((aignet aignet$a::aignet-well-formedp))
  (stype-count (nxst-stype) aignet)
  :enabled t)

(define aignet$a::num-gates ((aignet aignet$a::aignet-well-formedp))
  (stype-count (gate-stype) aignet)
  :enabled t)

(define aignet$a::innum->id ((n natp)
                             (aignet aignet$a::aignet-well-formedp))
  :guard (< n (aignet$a::num-ins aignet))
  :returns (id idp)
  :enabled t
  (to-id (len (lookup-stype n (pi-stype) aignet))))

(define aignet$a::outnum->id ((n natp)
                              (aignet aignet$a::aignet-well-formedp))
  :guard (< n (aignet$a::num-outs aignet))
  :returns (id idp)
  :enabled t
  (to-id (len (lookup-stype n (po-stype) aignet))))

(define aignet$a::regnum->id ((n natp)
                              (aignet aignet$a::aignet-well-formedp))
  :guard (< n (aignet$a::num-regs aignet))
  :returns (id idp)
  :enabled t
  (to-id (len (lookup-stype n (reg-stype) aignet))))

(define aignet$a::id-existsp ((id idp) (aignet aignet$a::aignet-well-formedp))
  :enabled t
  (aignet-idp id aignet))

(define aignet$a::id->type ((id idp)
                            (aignet aignet$a::aignet-well-formedp))
  :guard (aignet$a::id-existsp id aignet)
  :enabled t
  (node->type (car (lookup-id id aignet))))

(define aignet$a::io-id->regp ((id idp)
                               (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (or (eql (aignet$a::id->type id aignet) (in-type))
                  (eql (aignet$a::id->type id aignet) (out-type))))
  :enabled t
  (io-node->regp (car (lookup-id id aignet))))

(define aignet$a::co-id->fanin ((id idp)
                                (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (eql (aignet$a::id->type id aignet) (out-type)))
  :enabled t
  (aignet-lit-fix
   (co-node->fanin (car (lookup-id id aignet)))
   (cdr (lookup-id id aignet))))

(define aignet$a::gate-id->fanin0 ((id idp)
                                   (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (eql (aignet$a::id->type id aignet) (gate-type)))
  :enabled t
  (aignet-lit-fix
   (gate-node->fanin0 (car (lookup-id id aignet)))
   (cdr (lookup-id id aignet))))

(define aignet$a::gate-id->fanin1 ((id idp)
                                   (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (eql (aignet$a::id->type id aignet) (gate-type)))
  :enabled t
  (aignet-lit-fix
   (gate-node->fanin1 (car (lookup-id id aignet)))
   (cdr (lookup-id id aignet))))

(define aignet$a::io-id->ionum ((id idp) (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (or (eql (aignet$a::id->type id aignet) (in-type))
                  (and (eql (aignet$a::id->type id aignet) (out-type))
                       (eql (aignet$a::io-id->regp id aignet) 0))))
  :enabled t
  (let ((look (lookup-id id aignet)))
    (stype-count (stype (car look)) (cdr look)) ))

(define aignet$a::reg-id->nxst ((id idp)
                              (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (eql (aignet$a::id->type id aignet) (in-type))
              (eql (aignet$a::io-id->regp id aignet) 1))
  :returns (id idp)
  :enabled t
  (to-id (len (lookup-reg->nxst id aignet))))

(define aignet$a::nxst-id->reg ((id idp)
                    (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (eql (aignet$a::id->type id aignet) (out-type))
              (eql (aignet$a::io-id->regp id aignet) 1))
  :returns (id idp)
  :enabled t
  (aignet-id-fix ;; so that the result is an ID regardless of malformed input
   (nxst-node->reg (car (lookup-id id aignet)))
   (cdr (lookup-id id aignet))))



(define aignet$a::fanout-litp ((lit litp) (aignet aignet$a::aignet-well-formedp))
  :enabled t
  (aignet-litp lit aignet))



(defsection aignet$a::id->phase
  (mutual-recursion
   (defun aignet$a::lit->phase (lit aignet)
     (declare (xargs :guard (and (aignet$a::aignet-well-formedp aignet)
                                 (litp lit)
                                 (aignet$a::fanout-litp lit aignet))
                     :verify-guards nil
                     :measure (acl2::two-nats-measure
                               (id-val (lit-id lit)) 1)))
     (b-xor (lit-neg lit)
            (aignet$a::id->phase (lit-id lit) aignet)))

   (defun aignet$a::id->phase (id aignet)
     (declare (Xargs :guard (and (aignet$a::aignet-well-formedp aignet)
                                 (idp id)
                                 (aignet$a::id-existsp id aignet))
                     :measure (acl2::two-nats-measure
                               (id-val id) 0)))
     (let ((type (aignet$a::id->type id aignet)))
       (cond ((eql type (out-type))
              (aignet$a::lit->phase (aignet$a::co-id->fanin id aignet) aignet))
             ((eql type (gate-type))
              (b-and (aignet$a::lit->phase (aignet$a::gate-id->fanin0 id aignet) aignet)
                     (aignet$a::lit->phase (aignet$a::gate-id->fanin1 id aignet) aignet)))
             (t 0)))))

  (in-theory (disable aignet$a::lit->phase aignet$a::id->phase))

  (defthm bitp-of-lit->phase
    (bitp (aignet$a::lit->phase lit aignet))
    :hints (("goal" :expand (aignet$a::lit->phase lit aignet))))

  (defthm bitp-of-id->phase
    (bitp (aignet$a::id->phase id aignet))
    :hints (("goal" :expand (aignet$a::id->phase id aignet))))

  (verify-guards aignet$a::id->phase)

  (flag::make-flag phase-flg aignet$a::id->phase)

  (defthm-phase-flg
    (defthm aignet$a::id->phase-of-suffix
      (implies (and (aignet-extension-p new aignet)
                    (<= (id-val id) (len aignet)))
               (equal (aignet$a::id->phase id new)
                      (aignet$a::id->phase id aignet)))
      :hints ('(:expand ((:free (aignet)
                          (aignet$a::id->phase id aignet)))))
      :flag aignet$a::id->phase)
    (defthm aignet$a::lit->phase-of-suffix
      (implies (and (aignet-extension-p new aignet)
                    (<= (id-val (lit-id lit)) (len aignet)))
               (equal (aignet$a::lit->phase lit new)
                      (aignet$a::lit->phase lit aignet)))
      :hints ('(:expand ((:free (aignet)
                          (aignet$a::lit->phase lit aignet)))))
      :flag aignet$a::lit->phase))

  (defthm aignet$a::id->phase-of-cons
    (implies (<= (id-val id) (len aignet))
             (equal (aignet$a::id->phase id (cons node aignet))
                    (aignet$a::id->phase id aignet)))
    :hints (("goal" :use ((:instance aignet$a::id->phase-of-suffix
                           (new (cons node aignet))
                           (aignet aignet)))
             :expand ((:free (a b)
                       (aignet-extension-p (cons b a) a))))))

  (defthm aignet$a::lit->phase-of-cons
    (implies (<= (id-val (lit-id lit)) (len aignet))
             (equal (aignet$a::lit->phase lit (cons node aignet))
                    (aignet$a::lit->phase lit aignet)))
    :hints (("goal" :use ((:instance aignet$a::lit->phase-of-suffix
                           (new (cons node aignet))
                           (aignet aignet)))
             :expand ((:free (a b)
                       (aignet-extension-p (cons b a) a)))))))




(define aignet$a::aignet-add-in ((aignet aignet$a::aignet-well-formedp))
  (cons (pi-node) aignet)
  :enabled t
  ///
  (defthm aignet$a::aignet-well-formedp-of-aignet-add-in
    (implies (aignet-nodes-ok aignet)
             (aignet-nodes-ok (cons (list (pi-stype)) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-add-reg ((aignet aignet$a::aignet-well-formedp))
  (cons (reg-node) aignet)
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-reg
    (implies (aignet-nodes-ok aignet)
             (aignet-nodes-ok (cons (list (reg-stype)) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-add-gate ((f0 litp)
                         (f1 litp)
                         (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::fanout-litp f0 aignet)
              (aignet$a::fanout-litp f1 aignet))
  (cons (gate-node (aignet-lit-fix f0 aignet)
                   (aignet-lit-fix f1 aignet))
        aignet)
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-gate
    (implies (and (aignet-nodes-ok aignet)
                  (aignet$a::fanout-litp f0 aignet)
                  (aignet$a::fanout-litp f1 aignet))
             (aignet-nodes-ok (cons (gate-node f0 f1) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-add-out ((f litp)
                        (aignet aignet$a::aignet-well-formedp))
  :guard (aignet$a::fanout-litp f aignet)
  (cons (po-node (aignet-lit-fix f aignet))
        aignet)
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-out
    (implies (and (aignet-nodes-ok aignet)
                  (aignet$a::fanout-litp f aignet))
             (aignet-nodes-ok (cons (po-node f) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-set-nxst ((f litp)
                          (regid idp)
                          (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::fanout-litp f aignet)
              (aignet$a::id-existsp regid aignet)
              (eql (aignet$a::id->type regid aignet) (in-type))
              (eql (aignet$a::io-id->regp regid aignet) 1))
  (cons (nxst-node (aignet-lit-fix f aignet)
                 (aignet-id-fix regid aignet))
        aignet)
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-set-nxst
    (implies (and (aignet-nodes-ok aignet)
                  (aignet$a::fanout-litp f aignet)
                  (aignet-idp regid aignet))
             (aignet-nodes-ok (cons (nxst-node f regid) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-clear (aignet)
  :enabled t
  (declare (ignore aignet))
  nil)

(define aignet$a::aignet-init ((max-outs natp)
                               (max-regs natp)
                               (max-ins natp)
                               (max-nodes posp)
                               aignet)
  :enabled t
  (declare (ignore max-outs max-regs max-ins max-nodes aignet))
  nil)

(define aignet$a::create-aignet ()
  nil)
