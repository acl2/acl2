; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")
(include-book "aignet-logic")
(include-book "snodes")
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
;; (local (in-theory (disable set::double-containment)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           ;; set::double-containment
                           ;; set::sets-are-true-lists
                           make-list-ac)))

(local (in-theory (disable true-listp-update-nth
                           acl2::nth-with-large-index)))
(local (std::add-default-post-define-hook :fix))

(define aignet$a::aignet-well-formedp (aignet)
  :enabled t
  (and (node-listp aignet)
       (< (node-count aignet) #x1fffffff)
       (aignet-nodes-ok aignet)))

(local (fty::deffixtype aignet$a :pred aignet$a::aignet-well-formedp :fix node-list-fix :equiv node-list-equiv))

(define aignet$a::num-nodes ((aignet aignet$a::aignet-well-formedp))
  (1+ (node-count aignet))
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

(define aignet$a::max-fanin ((aignet aignet$a::aignet-well-formedp))
  (node-count (find-max-fanin aignet))
  :enabled t)

(define aignet$a::innum->id ((n natp)
                             (aignet aignet$a::aignet-well-formedp))
  :guard (< n (aignet$a::num-ins aignet))
  :returns (id natp)
  :enabled t
  (node-count (lookup-stype n (pi-stype) aignet)))

(define aignet$a::outnum->id ((n natp)
                              (aignet aignet$a::aignet-well-formedp))
  :guard (< n (aignet$a::num-outs aignet))
  :returns (id natp)
  :enabled t
  (node-count (lookup-stype n (po-stype) aignet)))

(define aignet$a::regnum->id ((n natp)
                              (aignet aignet$a::aignet-well-formedp))
  :guard (< n (aignet$a::num-regs aignet))
  :returns (id natp)
  :enabled t
  (node-count (lookup-stype n (reg-stype) aignet)))

(define aignet$a::id-existsp ((id natp) (aignet aignet$a::aignet-well-formedp))
  :enabled t
  (aignet-idp id aignet))

(define aignet$a::id->type ((id natp)
                            (aignet aignet$a::aignet-well-formedp))
  :guard (aignet$a::id-existsp id aignet)
  :enabled t
  (node->type (car (lookup-id id aignet))))

(define aignet$a::io-id->regp ((id natp)
                               (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (or (eql (aignet$a::id->type id aignet) (in-type))
                  (eql (aignet$a::id->type id aignet) (out-type))))
  :enabled t
  (io-node->regp (car (lookup-id id aignet))))

(define aignet$a::co-id->fanin ((id natp)
                                (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (eql (aignet$a::id->type id aignet) (out-type)))
  :enabled t
  (fanin :co (lookup-id id aignet)))

(define aignet$a::gate-id->fanin0 ((id natp)
                                   (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (eql (aignet$a::id->type id aignet) (gate-type)))
  :enabled t
  (fanin :gate0 (lookup-id id aignet)))

(define aignet$a::gate-id->fanin1 ((id natp)
                                   (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (eql (aignet$a::id->type id aignet) (gate-type)))
  :enabled t
  (fanin :gate1 (lookup-id id aignet)))

(define aignet$a::io-id->ionum ((id natp) (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (or (eql (aignet$a::id->type id aignet) (in-type))
                  (and (eql (aignet$a::id->type id aignet) (out-type))
                       (eql (aignet$a::io-id->regp id aignet) 0))))
  :enabled t
  (let ((look (lookup-id id aignet)))
    (stype-count (stype (car look)) (cdr look)) ))

(define aignet$a::reg-id->nxst ((id natp)
                              (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (eql (aignet$a::id->type id aignet) (in-type))
              (eql (aignet$a::io-id->regp id aignet) 1))
  :returns (id natp)
  :enabled t
  (node-count (lookup-reg->nxst id aignet)))

(define aignet$a::nxst-id->reg ((id natp)
                    (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp id aignet)
              (eql (aignet$a::id->type id aignet) (out-type))
              (eql (aignet$a::io-id->regp id aignet) 1))
  :returns (id natp)
  :enabled t
  (aignet-id-fix ;; so that the result is an ID regardless of malformed input
   (nxst-node->reg (car (lookup-id id aignet)))
   (cdr (lookup-id id aignet))))

(define aignet$a::fanin-litp ((lit litp) (aignet aignet$a::aignet-well-formedp))
  :enabled t
  (aignet-litp lit aignet))



(defines aignet$a::id->phase
  (define aignet$a::lit->phase ((lit litp)
                                (aignet aignet$a::aignet-well-formedp))
    :guard (aignet$a::fanin-litp lit aignet)
    :verify-guards nil
    :measure (acl2::two-nats-measure
              (lit-id lit) 1)
    (b-xor (lit-neg lit)
           (aignet$a::id->phase (lit-id lit) aignet)))

  (define aignet$a::id->phase ((id natp)
                               (aignet aignet$a::aignet-well-formedp))
    :guard (aignet$a::id-existsp id aignet)
    :measure (acl2::two-nats-measure
              (nfix id) 0)
    (let ((type (aignet$a::id->type id aignet)))
      (cond ((eql type (out-type))
             (aignet$a::lit->phase (aignet$a::co-id->fanin id aignet) aignet))
            ((eql type (gate-type))
             (b-and (aignet$a::lit->phase (aignet$a::gate-id->fanin0 id aignet) aignet)
                    (aignet$a::lit->phase (aignet$a::gate-id->fanin1 id aignet) aignet)))
            (t 0))))
  ///

  (in-theory (disable aignet$a::lit->phase aignet$a::id->phase))

  (defthm bitp-of-lit->phase
    (bitp (aignet$a::lit->phase lit aignet))
    :hints (("goal" :expand (aignet$a::lit->phase lit aignet))))

  (defthm bitp-of-id->phase
    (bitp (aignet$a::id->phase id aignet))
    :hints (("goal" :expand (aignet$a::id->phase id aignet))))

  (verify-guards aignet$a::id->phase)

  (aignet$a::defthm-id->phase-flag
    (defthm aignet$a::id->phase-of-suffix
      (implies (and (aignet-extension-p new aignet)
                    (<= (nfix id) (node-count aignet)))
               (equal (aignet$a::id->phase id new)
                      (aignet$a::id->phase id aignet)))
      :hints ('(:expand ((:free (aignet)
                          (aignet$a::id->phase id aignet)))))
      :flag aignet$a::id->phase)
    (defthm aignet$a::lit->phase-of-suffix
      (implies (and (aignet-extension-p new aignet)
                    (<= (lit-id lit) (node-count aignet)))
               (equal (aignet$a::lit->phase lit new)
                      (aignet$a::lit->phase lit aignet)))
      :hints ('(:expand ((:free (aignet)
                          (aignet$a::lit->phase lit aignet)))))
      :flag aignet$a::lit->phase))

  (defthm aignet$a::id->phase-of-cons
    (implies (<= (nfix id) (node-count aignet))
             (equal (aignet$a::id->phase id (cons node aignet))
                    (aignet$a::id->phase id aignet)))
    :hints (("goal" :use ((:instance aignet$a::id->phase-of-suffix
                           (new (cons node aignet))
                           (aignet aignet)))
             :expand ((:free (a b)
                       (aignet-extension-p (cons b a) a))))))

  (defthm aignet$a::lit->phase-of-cons
    (implies (<= (lit-id lit) (node-count aignet))
             (equal (aignet$a::lit->phase lit (cons node aignet))
                    (aignet$a::lit->phase lit aignet)))
    :hints (("goal" :use ((:instance aignet$a::lit->phase-of-suffix
                           (new (cons node aignet))
                           (aignet aignet)))
             :expand ((:free (a b)
                       (aignet-extension-p (cons b a) a))))))

  (fty::deffixequiv-mutual aignet$a::id->phase))




(define aignet$a::aignet-add-in^ ((aignet aignet$a::aignet-well-formedp))
  :guard (< (aignet$a::num-nodes aignet) #x1fffffff)
  (cons (pi-node) (node-list-fix aignet))
  :enabled t
  ///
  (defthm aignet$a::aignet-well-formedp-of-aignet-add-in
    (implies (aignet-nodes-ok aignet)
             (aignet-nodes-ok (cons (list (pi-stype)) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-add-reg^ ((aignet aignet$a::aignet-well-formedp))
  :guard (< (aignet$a::num-nodes aignet) #x1fffffff)
  (cons (reg-node) (node-list-fix aignet))
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-reg
    (implies (aignet-nodes-ok aignet)
             (aignet-nodes-ok (cons (list (reg-stype)) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-add-gate^ ((f0 litp)
                                    (f1 litp)
                                    (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::fanin-litp f0 aignet)
              (aignet$a::fanin-litp f1 aignet)
              (< (aignet$a::num-nodes aignet) #x1fffffff))
  (cons (gate-node (aignet-lit-fix f0 aignet)
                   (aignet-lit-fix f1 aignet))
        (node-list-fix aignet))
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-gate
    (implies (and (aignet-nodes-ok aignet)
                  (aignet$a::fanin-litp f0 aignet)
                  (aignet$a::fanin-litp f1 aignet))
             (aignet-nodes-ok (cons (gate-node f0 f1) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-add-out^ ((f litp)
                        (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::fanin-litp f aignet)
              (< (aignet$a::num-nodes aignet) #x1fffffff))
  (cons (po-node (aignet-lit-fix f aignet))
        (node-list-fix aignet))
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-out
    (implies (and (aignet-nodes-ok aignet)
                  (aignet$a::fanin-litp f aignet))
             (aignet-nodes-ok (cons (po-node f) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-set-nxst^ ((f litp)
                                    (regid natp)
                                    (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::fanin-litp f aignet)
              (aignet$a::id-existsp regid aignet)
              (eql (aignet$a::id->type regid aignet) (in-type))
              (eql (aignet$a::io-id->regp regid aignet) 1)
              (< (aignet$a::num-nodes aignet) #x1fffffff))
  (cons (nxst-node (aignet-lit-fix f aignet)
                   (aignet-id-fix regid aignet))
        (node-list-fix aignet))
  :enabled t
  ///
  (local (defthm equal-reg-when-stype-is-reg
           (implies (node-p x)
                    (equal (equal (stype x) :reg)
                           (equal x '(:reg))))
           :hints(("Goal" :in-theory (enable node-p stype)))))
  
  (defthm aignet-nodes-ok-of-aignet-set-nxst
    (implies (and (aignet-nodes-ok aignet)
                  (aignet$a::fanin-litp f aignet)
                  (aignet-idp regid aignet)
                  (eql (aignet$a::id->type regid aignet) (in-type))
                  (eql (aignet$a::io-id->regp regid aignet) 1))
             (aignet-nodes-ok (cons (nxst-node f regid) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))


(define aignet$a::aignet-rollback ((id posp "the num-nodes of the resulting network")
                                   (aignet aignet$a::aignet-well-formedp))
  :guard (and (<= id (aignet$a::num-nodes aignet))
              (equal (aignet$a::num-nxsts aignet)
                     (non-exec (aignet$a::num-nxsts (lookup-id (1- id) aignet))))
              (equal (aignet$a::num-ins aignet)
                     (non-exec (aignet$a::num-ins (lookup-id (1- id) aignet))))
              (equal (aignet$a::num-outs aignet)
                     (non-exec (aignet$a::num-outs (lookup-id (1- id) aignet))))
              (equal (aignet$a::num-regs aignet)
                     (non-exec (aignet$a::num-regs (lookup-id (1- id) aignet)))))
  (lookup-id (1- (lposfix id)) aignet))


(define aignet$a::aignet-clear (aignet)
  :enabled t
  (declare (ignore aignet))
  nil)

(define aignet$a::aignet-init^ ((max-outs :type (unsigned-byte 29))
                                (max-regs :type (unsigned-byte 29))
                                (max-ins :type (unsigned-byte 29))
                                (max-nodes posp :type (unsigned-byte 29))
                                aignet)
  :enabled t
  (declare (ignore max-outs max-regs max-ins max-nodes aignet))
  nil)

(define aignet$a::create-aignet ()
  nil)


(define id-slots ((id natp)
                  (aignet aignet$a::aignet-well-formedp))
  :guard (aignet$a::id-existsp id aignet)
  :guard-debug t
  :returns (mv (slot0 natp :rule-classes :type-prescription)
               (slot1 natp :rule-classes :type-prescription))
  (aignet-seq-case
   (aignet$a::id->type id aignet)
   (aignet$a::io-id->regp id aignet)
   :const (mk-snode (const-type) 0 0 0 0)
   :pi    (mk-snode (in-type) 0 0 0 (aignet$a::io-id->ionum id aignet))
   :reg   (mk-snode (in-type) 1 0
                    (aignet$a::reg-id->nxst id aignet)
                    (aignet$a::io-id->ionum id aignet))
   :gate  (mk-snode (gate-type)
                    0 (aignet$a::id->phase id aignet)
                    (lit-fix (aignet$a::gate-id->fanin0 id aignet))
                    (lit-fix (aignet$a::gate-id->fanin1 id aignet)))
   :po    (mk-snode (out-type)
                    0
                    (aignet$a::id->phase id aignet)
                    (lit-fix (aignet$a::co-id->fanin id aignet))
                    (aignet$a::io-id->ionum id aignet))
   :nxst  (mk-snode (out-type) 1
                    (aignet$a::id->phase id aignet)
                    (lit-fix (aignet$a::co-id->fanin id aignet))
                    (aignet$a::nxst-id->reg id aignet)))
  ///
  (defthm snode->type-of-id-slot
    (equal (snode->type (mv-nth 0 (id-slots id aignet)))
           (aignet$a::id->type id aignet))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable stype stype-fix stypep)))))


  (defthm snode->regp-of-id-slot
    (equal (snode->regp (mv-nth 1 (id-slots id aignet)))
           (aignet$a::io-id->regp id aignet))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable stype stype-fix stypep regp)))))

  (defthm snode->phase-of-id-slot
    (equal (snode->phase (mv-nth 1 (id-slots id aignet)))
           (aignet$a::id->phase id aignet))
    :hints(("Goal" :in-theory (enable aignet$a::id->phase))))

  (defthm snode->fanin-of-gate-slot
    (implies (equal (aignet$a::id->type id aignet) (gate-type))
             (and (equal (snode->fanin (mv-nth 0 (id-slots id aignet)))
                         (aignet$a::gate-id->fanin0 id aignet))
                  (equal (snode->fanin (mv-nth 1 (id-slots id aignet)))
                         (aignet$a::gate-id->fanin1 id aignet)))))

  (defthm snode->fanin-of-co-slot
    (implies (equal (aignet$a::id->type id aignet) (out-type))
             (equal (snode->fanin (mv-nth 0 (id-slots id aignet)))
                    (aignet$a::co-id->fanin id aignet))))

  (defthm snode->ionum-of-io
    (implies (or (equal (aignet$a::id->type id aignet) (in-type))
                 (and (equal (aignet$a::id->type id aignet) (out-type))
                      (equal (aignet$a::io-id->regp id aignet) 0)))
             (equal (snode->ionum (mv-nth 1 (id-slots id aignet)))
                    (aignet$a::io-id->ionum id aignet))))

  (defthm snode->regid-of-reg
    (implies (and (equal (aignet$a::id->type id aignet) (in-type))
                  (equal (aignet$a::io-id->regp id aignet) 1))
             (equal (snode->regid (mv-nth 0 (id-slots id aignet)))
                    (aignet$a::reg-id->nxst id aignet))))

  (defthm snode->regid-of-nxst
    (implies (and (equal (aignet$a::id->type id aignet) (out-type))
                  (equal (aignet$a::io-id->regp id aignet) 1))
             (equal (snode->regid (mv-nth 1 (id-slots id aignet)))
                    (aignet$a::nxst-id->reg id aignet)))))


(define aignet$a::id->slot ((id natp) (slot bitp) aignet)
  :guard (and (aignet$a::aignet-well-formedp aignet)
              (aignet$a::id-existsp id aignet))
  :enabled t
  (mv-let (slot0 slot1)
    (id-slots id aignet)
    (if (eql (acl2::lbfix slot) 1)
        slot1
      slot0)))
