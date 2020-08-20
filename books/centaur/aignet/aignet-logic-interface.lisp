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
       (< (fanin-count aignet) #x1fffffff)
       (<= (stype-count :po aignet) #x1fffffff)
       (<= (stype-count :nxst aignet) #x1fffffff)
       (aignet-nodes-ok aignet)))

(local (fty::deffixtype aignet$a :pred aignet$a::aignet-well-formedp :fix node-list-fix :equiv node-list-equiv))

(define aignet$a::num-fanins ((aignet aignet$a::aignet-well-formedp))
  (1+ (fanin-count aignet))
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
  (+ (stype-count (and-stype) aignet)
     (stype-count (xor-stype) aignet))
  :enabled t)

(define aignet$a::innum->id ((n natp)
                             (aignet aignet$a::aignet-well-formedp))
  :guard (< n (aignet$a::num-ins aignet))
  :returns (id natp)
  :enabled t
  (fanin-count (lookup-stype n (pi-stype) aignet)))

;; (define aignet$a::outnum->id ((n natp)
;;                               (aignet aignet$a::aignet-well-formedp))
;;   :guard (< n (aignet$a::num-outs aignet))
;;   :returns (id natp)
;;   :enabled t
;;   (fanin-count (lookup-stype n (po-stype) aignet)))

(define aignet$a::regnum->id ((n natp)
                              (aignet aignet$a::aignet-well-formedp))
  :guard (< n (aignet$a::num-regs aignet))
  :returns (id natp)
  :enabled t
  (fanin-count (lookup-stype n (reg-stype) aignet)))

(define aignet$a::outnum->fanin ((out natp)
                                 (aignet aignet$a::aignet-well-formedp))
  :guard (< out (aignet$a::num-outs aignet))
  :enabled t
  (fanin 0 (lookup-stype out :po aignet)))

(define aignet$a::id-existsp ((id natp) (aignet aignet$a::aignet-well-formedp))
  :enabled t
  (aignet-idp id aignet))

;; (define aignet$a::id->type ((id natp)
;;                             (aignet aignet$a::aignet-well-formedp))
;;   :guard (aignet$a::id-existsp id aignet)
;;   :enabled t
;;   (node->type (car (lookup-id id aignet))))

;; (define aignet$a::id->regp ((id natp)
;;                                (aignet aignet$a::aignet-well-formedp))
;;   :guard (and (aignet$a::id-existsp id aignet)
;;               (not (eql (aignet$a::id->type id aignet) (const-type))))
;;   :enabled t
;;   (node->regp (car (lookup-id id aignet))))



;; (define aignet$a::gate-id->fanin0 ((id natp)
;;                                    (aignet aignet$a::aignet-well-formedp))
;;   :guard (and (aignet$a::id-existsp id aignet)
;;               (eql (aignet$a::id->type id aignet) (gate-type)))
;;   :enabled t
;;   (fanin 0 (lookup-id id aignet)))

;; (define aignet$a::gate-id->fanin1 ((id natp)
;;                                    (aignet aignet$a::aignet-well-formedp))
;;   :guard (and (aignet$a::id-existsp id aignet)
;;               (eql (aignet$a::id->type id aignet) (gate-type)))
;;   :enabled t
;;   (fanin 1 (lookup-id id aignet)))

;; (define aignet$a::ci-id->ionum ((id natp) (aignet aignet$a::aignet-well-formedp))
;;   :guard (and (aignet$a::id-existsp id aignet)
;;               (or (eql (aignet$a::id->type id aignet) (in-type))
;;                   (and (eql (aignet$a::id->type id aignet) (out-type))
;;                        (eql (aignet$a::id->regp id aignet) 0))))
;;   :enabled t
;;   (let ((look (lookup-id id aignet)))
;;     (stype-count (stype (car look)) (cdr look)) ))

;; (define aignet$a::regnum->nxst ((reg natp)
;;                                 (aignet aignet$a::aignet-well-formedp))
;;   :guard (< reg (aignet$a::num-regs aignet))
;;   :returns (nxst litp :rule-classes :type-prescription)
;;   :enabled t
;;   (lookup-reg->nxst reg aignet))



;; (defines aignet$a::id->phase
;;   (define aignet$a::lit->phase ((lit litp)
;;                                 (aignet aignet$a::aignet-well-formedp))
;;     :guard (aignet$a::id-existsp (lit->var lit) aignet)
;;     :verify-guards nil
;;     :measure (acl2::two-nats-measure
;;               (lit-id lit) 1)
;;     (b-xor (lit-neg lit)
;;            (aignet$a::id->phase (lit-id lit) aignet)))

;;   (define aignet$a::id->phase ((id natp)
;;                                (aignet aignet$a::aignet-well-formedp))
;;     :guard (aignet$a::id-existsp id aignet)
;;     :measure (acl2::two-nats-measure
;;               (nfix id) 0)
;;     (let ((type (aignet$a::id->type id aignet)))
;;       (cond ((eql type (gate-type))
;;              (b* ((ph0 (aignet$a::lit->phase (aignet$a::gate-id->fanin0 id aignet) aignet))
;;                   (ph1 (aignet$a::lit->phase (aignet$a::gate-id->fanin1 id aignet) aignet)))
;;                (if (eql 1 (aignet$a::id->regp id aignet))
;;                    ;; xor
;;                    (b-xor ph0 ph1)
;;                  (b-and ph0 ph1))))
;;             (t 0))))
;;   ///

;;   (in-theory (disable aignet$a::lit->phase aignet$a::id->phase))

;;   (defthm bitp-of-lit->phase
;;     (bitp (aignet$a::lit->phase lit aignet))
;;     :hints (("goal" :expand (aignet$a::lit->phase lit aignet))))

;;   (defthm bitp-of-id->phase
;;     (bitp (aignet$a::id->phase id aignet))
;;     :hints (("goal" :expand (aignet$a::id->phase id aignet))))

;;   (verify-guards aignet$a::id->phase)

;;   (aignet$a::defthm-id->phase-flag
;;     (defthm aignet$a::id->phase-of-suffix
;;       (implies (and (aignet-extension-p new aignet)
;;                     (<= (nfix id) (fanin-count aignet)))
;;                (equal (aignet$a::id->phase id new)
;;                       (aignet$a::id->phase id aignet)))
;;       :hints ('(:expand ((:free (aignet)
;;                           (aignet$a::id->phase id aignet)))))
;;       :flag aignet$a::id->phase)
;;     (defthm aignet$a::lit->phase-of-suffix
;;       (implies (and (aignet-extension-p new aignet)
;;                     (<= (lit-id lit) (fanin-count aignet)))
;;                (equal (aignet$a::lit->phase lit new)
;;                       (aignet$a::lit->phase lit aignet)))
;;       :hints ('(:expand ((:free (aignet)
;;                           (aignet$a::lit->phase lit aignet)))))
;;       :flag aignet$a::lit->phase))

;;   (defthm aignet$a::id->phase-of-cons
;;     (implies (<= (nfix id) (fanin-count aignet))
;;              (equal (aignet$a::id->phase id (cons node aignet))
;;                     (aignet$a::id->phase id aignet)))
;;     :hints (("goal" :use ((:instance aignet$a::id->phase-of-suffix
;;                            (new (cons node aignet))
;;                            (aignet aignet)))
;;              :expand ((:free (a b)
;;                        (aignet-extension-p (cons b a) a))))))

;;   (defthm aignet$a::lit->phase-of-cons
;;     (implies (<= (lit-id lit) (fanin-count aignet))
;;              (equal (aignet$a::lit->phase lit (cons node aignet))
;;                     (aignet$a::lit->phase lit aignet)))
;;     :hints (("goal" :use ((:instance aignet$a::lit->phase-of-suffix
;;                            (new (cons node aignet))
;;                            (aignet aignet)))
;;              :expand ((:free (a b)
;;                        (aignet-extension-p (cons b a) a))))))

;;   (fty::deffixequiv-mutual aignet$a::id->phase))

(defines id-phase
  (define lit-phase ((lit litp)
                     (aignet node-listp))
    :guard (aignet-idp (lit->var lit) aignet)
    :verify-guards nil
    :measure (acl2::two-nats-measure
              (lit-id lit) 1)
    (b-xor (lit-neg lit)
           (id-phase (lit-id lit) aignet)))

  (define id-phase ((id natp)
                    (aignet node-listp))
    :guard (aignet-idp id aignet)
    :measure (acl2::two-nats-measure
              (nfix id) 0)
    (let ((suff (lookup-id id aignet)))
      (case (stype (car suff))
        (:and (b-and (lit-phase (fanin 0 suff) aignet)
                     (lit-phase (fanin 1 suff) aignet)))
        (:xor (b-xor (lit-phase (fanin 0 suff) aignet)
                     (lit-phase (fanin 1 suff) aignet)))
        (t 0))))
  ///

  (in-theory (disable lit-phase id-phase))

  (defthm bitp-of-lit-phase
    (bitp (lit-phase lit aignet))
    :hints (("goal" :expand (lit-phase lit aignet))))

  (defthm bitp-of-id-phase
    (bitp (id-phase id aignet))
    :hints (("goal" :expand (id-phase id aignet))))

  (verify-guards id-phase)

  (defthm-id-phase-flag
    (defthm id-phase-of-suffix
      (implies (and (aignet-extension-p new aignet)
                    (<= (nfix id) (fanin-count aignet)))
               (equal (id-phase id new)
                      (id-phase id aignet)))
      :hints ('(:expand ((:free (aignet)
                          (id-phase id aignet)))))
      :flag id-phase)
    (defthm lit-phase-of-suffix
      (implies (and (aignet-extension-p new aignet)
                    (<= (lit-id lit) (fanin-count aignet)))
               (equal (lit-phase lit new)
                      (lit-phase lit aignet)))
      :hints ('(:expand ((:free (aignet)
                          (lit-phase lit aignet)))))
      :flag lit-phase))

  (defthm id-phase-of-cons
    (implies (<= (nfix id) (fanin-count aignet))
             (equal (id-phase id (cons node aignet))
                    (id-phase id aignet)))
    :hints (("goal" :use ((:instance id-phase-of-suffix
                           (new (cons node aignet))
                           (aignet aignet)))
             :expand ((:free (a b)
                       (aignet-extension-p (cons b a) a))))))

  (defthm lit-phase-of-cons
    (implies (<= (lit-id lit) (fanin-count aignet))
             (equal (lit-phase lit (cons node aignet))
                    (lit-phase lit aignet)))
    :hints (("goal" :use ((:instance lit-phase-of-suffix
                           (new (cons node aignet))
                           (aignet aignet)))
             :expand ((:free (a b)
                       (aignet-extension-p (cons b a) a))))))

  (fty::deffixequiv-mutual id-phase))




(define aignet$a::aignet-add-in^ ((aignet aignet$a::aignet-well-formedp))
  :guard (< (aignet$a::num-fanins aignet) #x1fffffff)
  (cons (pi-node) (node-list-fix aignet))
  :enabled t
  ///
  (defthm aignet$a::aignet-well-formedp-of-aignet-add-in
    (implies (aignet-nodes-ok aignet)
             (aignet-nodes-ok (cons (list (pi-stype)) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-add-reg^ ((aignet aignet$a::aignet-well-formedp))
  :guard (< (aignet$a::num-fanins aignet) #x1fffffff)
  (cons (reg-node) (node-list-fix aignet))
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-reg
    (implies (aignet-nodes-ok aignet)
             (aignet-nodes-ok (cons (list (reg-stype)) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-add-and^ ((f0 litp)
                                    (f1 litp)
                                    (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp (lit->var f0) aignet)
              (aignet$a::id-existsp (lit->var f1) aignet)
              (< (aignet$a::num-fanins aignet) #x1fffffff))
  (cons (and-node (aignet-lit-fix f0 aignet)
                   (aignet-lit-fix f1 aignet))
        (node-list-fix aignet))
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-and
    (implies (and (aignet-nodes-ok aignet)
                  (aignet$a::id-existsp (lit->var f0) aignet)
                  (aignet$a::id-existsp (lit->var f1) aignet))
             (aignet-nodes-ok (cons (and-node f0 f1) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-add-xor^ ((f0 litp)
                                    (f1 litp)
                                    (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp (lit->var f0) aignet)
              (aignet$a::id-existsp (lit->var f1) aignet)
              (< (aignet$a::num-fanins aignet) #x1fffffff))
  (cons (xor-node (aignet-lit-fix f0 aignet)
                   (aignet-lit-fix f1 aignet))
        (node-list-fix aignet))
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-xor
    (implies (and (aignet-nodes-ok aignet)
                  (aignet$a::id-existsp (lit->var f0) aignet)
                  (aignet$a::id-existsp (lit->var f1) aignet))
             (aignet-nodes-ok (cons (xor-node f0 f1) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-add-out^ ((f litp)
                        (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp (lit->var f) aignet)
              (< (aignet$a::num-outs aignet) #x1ffffffe))
  (cons (po-node (aignet-lit-fix f aignet))
        (node-list-fix aignet))
  :enabled t
  ///
  (defthm aignet-nodes-ok-of-aignet-add-out
    (implies (and (aignet-nodes-ok aignet)
                  (aignet$a::id-existsp (lit->var f) aignet))
             (aignet-nodes-ok (cons (po-node f) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))

(define aignet$a::aignet-set-nxst^ ((f litp)
                                    (reg natp)
                                    (aignet aignet$a::aignet-well-formedp))
  :guard (and (aignet$a::id-existsp (lit->var f) aignet)
              (< reg (aignet$a::num-regs aignet))
              (< (aignet$a::num-nxsts aignet) #x1fffffff))
  (cons (nxst-node (aignet-lit-fix f aignet)
                   reg)
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
                  (aignet$a::id-existsp (lit->var f) aignet)
                  (< (nfix reg) (aignet$a::num-regs aignet)))
             (aignet-nodes-ok (cons (nxst-node f reg) aignet)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok)))))


(define aignet$a::aignet-rollback ((id posp "the num-fanins of the resulting network")
                                   (aignet aignet$a::aignet-well-formedp))
  :guard (and (<= id (aignet$a::num-fanins aignet))
              (equal (aignet$a::num-nxsts aignet) 0)
              (equal (aignet$a::num-ins aignet)
                     (non-exec (aignet$a::num-ins (lookup-id (1- id) aignet))))
              (equal (aignet$a::num-outs aignet) 0)
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


(defthm stype-cases-of-lookup-id
  (or (equal (stype (car (lookup-id id aignet))) :const)
      (equal (stype (car (lookup-id id aignet))) :pi)
      (equal (stype (car (lookup-id id aignet))) :reg)
      (equal (stype (car (lookup-id id aignet))) :and)
      (equal (stype (car (lookup-id id aignet))) :xor))
  :hints(("Goal" :in-theory (enable lookup-id)))
  :rule-classes ((:forward-chaining :trigger-terms ((stype (car (lookup-id id aignet)))))))

(define id-slots ((id natp)
                  (aignet aignet$a::aignet-well-formedp))
  :guard (aignet$a::id-existsp id aignet)
  :guard-debug t
  :returns (mv (slot0 natp :rule-classes :type-prescription)
               (slot1 natp :rule-classes :type-prescription))
  (b* ((suff (lookup-id id aignet)))
    (case (stype (car suff))
      (:pi    (mk-snode (in-type) 0 0 0 (stype-count :pi (cdr suff))))
      (:reg   (mk-snode (in-type) 1 0
                       (lookup-reg->nxst (stype-count :reg (cdr suff)) aignet)
                       (stype-count :reg (cdr suff))))
      (:and  (mk-snode (gate-type) 0
                      (id-phase id aignet)
                      (fanin 0 suff)
                      (fanin 1 suff)))
      (:xor  (mk-snode (gate-type) 1
                       (id-phase id aignet)
                       (fanin 0 suff)
                       (fanin 1 suff)))
      (t ;; :const
       (mk-snode (const-type) 0 0 0 0))))
  ///
  

  (defthm snode->type-of-id-slot
    (equal (snode->type (mv-nth 0 (id-slots id aignet)))
           (typecode (ctype (stype (car (lookup-id id aignet))))))
    ;; :hints ((and stable-under-simplificationp
    ;;              '(:in-theory (enable stype-fix stypep))))
    )


  (defthm snode->regp-of-id-slot
    (equal (snode->regp (mv-nth 1 (id-slots id aignet)))
           (regp (stype (car (lookup-id id aignet)))))
    ;; :hints ((and stable-under-simplificationp
    ;;              '(:in-theory (enable stype-fix stypep regp))))
    )

  (defthm snode->phase-of-id-slot
    (equal (snode->phase (mv-nth 1 (id-slots id aignet)))
           (id-phase id aignet))
    :hints(("Goal" :in-theory (enable id-phase))))

  (defthm snode->fanin-of-gate-slot
    (implies (equal (ctype (stype (car (lookup-id id aignet)))) :gate)
             (and (equal (snode->fanin (mv-nth 0 (id-slots id aignet)))
                         (fanin 0 (lookup-id id aignet)))
                  (equal (snode->fanin (mv-nth 1 (id-slots id aignet)))
                         (fanin 1 (lookup-id id aignet))))))

  (defthm snode->ionum-of-input
    (implies (equal (ctype (stype (car (lookup-id id aignet)))) :input)
             (equal (snode->ionum (mv-nth 1 (id-slots id aignet)))
                    (stype-count (stype (car (lookup-id id aignet)))
                                 (cdr (lookup-id id aignet))))))

  (defthm snode->fanin-of-reg
    (implies (equal (stype (car (lookup-id id aignet))) :reg)
             (equal (snode->fanin (mv-nth 0 (id-slots id aignet)))
                    (lookup-reg->nxst (stype-count :reg (cdr (lookup-id id aignet)))
                                      aignet))))

  (local (defthmd unsigned-byte-p-29-by-bound
           (implies (and (natp x)
                         (<= x #x1fffffff))
                    (unsigned-byte-p 29 x))))

  (local (defthmd unsigned-byte-30-of-lit
           (implies (and (unsigned-byte-p 29 (lit->var lit))
                         (litp lit))
                    (unsigned-byte-p 30 lit))
           :hints(("Goal" :in-theory (enable lit->var)))))

  (local (defthm unsigned-byte-30-of-aignet-lit-fix
           (implies (< (fanin-count aignet) #x1fffffff)
                    (unsigned-byte-p 30 (aignet-lit-fix lit aignet)))
           :hints(("Goal" :in-theory (enable fanin
                                             unsigned-byte-30-of-lit
                                             unsigned-byte-p-29-by-bound)))))

  (local (defthm unsigned-byte-30-of-fanin
           (implies (< (fanin-count aignet) #x1fffffff)
                    (unsigned-byte-p 30 (fanin ftype (lookup-id id aignet))))
           :hints(("Goal" :in-theory (e/d (fanin) (unsigned-byte-p))))))

  (local (defthm unsigned-byte-30-of-lookup-reg->nxst
           (implies (< (fanin-count aignet) #x1fffffff)
                    (unsigned-byte-p 30 (lookup-reg->nxst reg aignet)))
           :hints(("Goal" :in-theory (e/d (lookup-reg->nxst
                                           unsigned-byte-30-of-lit
                                           unsigned-byte-p-29-by-bound)
                                          (unsigned-byte-p))))))

  (local (defthm stype-count-less-than-fanin-count
           (implies (not (equal (ctype stype) :output))
                    (<= (stype-count stype aignet) (fanin-count aignet)))
           :hints(("Goal" :in-theory (enable stype-count fanin-count fanin-node-p)))
           :rule-classes :linear))

  (local (defthm unsigned-byte-30-of-stype-count
           (implies (and (< (fanin-count aignet) #x1fffffff)
                         (not (equal (ctype stype) :output)))
                    (unsigned-byte-p 30 (stype-count stype aignet)))
           :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

  (defret id-slots-unsigned-byte-p
    (implies (aignet$a::aignet-well-formedp aignet)
             (and (unsigned-byte-p 32 slot0)
                  (unsigned-byte-p 32 slot1)))
    :hints(("Goal" :in-theory (disable unsigned-byte-p)))))


(define aignet$a::id->slot0 ((id natp) aignet)
  :guard (and (aignet$a::aignet-well-formedp aignet)
              (aignet$a::id-existsp id aignet))
  :enabled t
  (mv-let (slot0 slot1)
    (id-slots id aignet)
    (declare (ignore slot1))
    slot0))

(define aignet$a::id->slot1 ((id natp) aignet)
  :guard (and (aignet$a::aignet-well-formedp aignet)
              (aignet$a::id-existsp id aignet))
  :enabled t
  (mv-let (slot0 slot1)
    (id-slots id aignet)
    (declare (ignore slot0))
    slot1))
