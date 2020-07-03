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
(include-book "semantics")
(include-book "centaur/aig/aig-base" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)
(include-book "std/alists/alist-keys" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (disable nth update-nth set::double-containment)))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(local (in-theory (disable ;acl2::update-nth-update-nth
                           ;acl2::nth-with-large-index
                           acl2::nth-with-large-index)))

(local (defthm nfix-equal-posp
         (implies (and (syntaxp (quotep x))
                       (posp x))
                  (equal (equal (nfix n) x)
                         (equal n x)))
         :hints(("Goal" :in-theory (enable nfix)))))

(acl2::def-1d-arr aigtrans
                  :slotname aig
                  :default-val nil)



(define id-trans-logic ((id :type (integer 0 *))
                        aigtrans aignet)
  :prepwork
  ((defmacro lit-trans-logic (lit aignet-transv aignetv)
     `(let ((lit-trans-logic-lit ,lit))
        (aig-xor (eql 1 (lit-neg lit-trans-logic-lit))
                 (id-trans-logic (lit-id lit-trans-logic-lit)
                                 ,aignet-transv ,aignetv)))))
  :verify-guards nil
  :guard (and (id-existsp id aignet)
              (<= (num-fanins aignet) (aigs-length aigtrans)))
  :measure (nfix id)
  (b* ((slot0 (id->slot id 0 aignet))
       (type (snode->type slot0)))
    (aignet-case
     type
     :gate (b* ((f0 (snode->fanin slot0))
                (slot1 (id->slot id 1 aignet))
                (f1 (snode->fanin slot1))
                (xor (snode->regp slot1))
                (v0 (lit-trans-logic f0 aigtrans aignet))
                (v1 (lit-trans-logic f1 aigtrans aignet)))
             (if (eql xor 1)
                 (aig-xor v0 v1)
               (aig-and v0 v1)))
     :in   (get-aig id aigtrans)
     :const nil))
  ///
  (defcong nat-equiv equal (id-trans-logic id aignet-vals aignet) 1
    :event-name id-trans-logic-nat-equiv-cong)
  (defcong nth-equiv equal (id-trans-logic id aignet-vals aignet) 2
    :event-name id-trans-logic-aignet-eval-nth-equiv-cong)

  (verify-guards id-trans-logic)

  (defthm id-trans-logic-aignet-trans-frame
    (implies (not (equal (id->type m aignet) (in-type)))
             (equal (id-trans-logic id (update-nth m v aigtrans)
                                    aignet)
                    (id-trans-logic id aigtrans aignet)))
    :hints((acl2::just-induct-and-expand
            (id-trans-logic id (update-nth m v aigtrans)
                            aignet))))

  (defthm id-trans-of-update-aignet-trans-greater
    (implies (< (nfix id) (nfix m))
             (equal (id-trans-logic
                     id (update-nth m v aigtrans) aignet)
                    (id-trans-logic
                     id aigtrans aignet)))
    :hints(("Goal" :in-theory (enable id-trans-logic)
            :induct
            (id-trans-logic
             id (update-nth m v aigtrans) aignet)))))


(define aignet-trans-invariant ((n natp) aigtrans aignet)
  :guard (and (<= (num-fanins aignet) (aigs-length aigtrans))
              (<= n (num-fanins aignet)))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (if (zp n)
      t
    (and (or (int= (id->type (1- n) aignet) (out-type))
             (equal (id-trans-logic (1- n) aigtrans aignet)
                    (get-aig (1- n) aigtrans)))
         (aignet-trans-invariant (1- n) aigtrans aignet)))
  ///
  (defcong nat-equiv equal (aignet-trans-invariant n aigtrans aignet) 1)
  (defcong nth-equiv equal (aignet-trans-invariant n aigtrans aignet) 2)

  (defthm aignet-trans-id-when-aignet-trans-invariant
    (implies (and (aignet-trans-invariant n aigtrans aignet)
                  (< (nfix m) (nfix n))
                  (not (equal (ctype (stype (car (lookup-id m aignet)))) :output)))
             (equal (nth m aigtrans)
                    (id-trans-logic m aigtrans aignet))))


  (defthm aignet-trans-gates-invariant-after-out-of-bounds-update
    (implies (<= (nfix n) (nfix m))
             (equal (aignet-trans-invariant
                     n (update-nth m v aigtrans) aignet)
                    (aignet-trans-invariant
                     n aigtrans aignet)))))

(defsection aignet-translate

  (defmacro lit->aig (lit aigtransv)
    `(let ((lit->aig-lit ,lit))
       (aig-xor (eql 1 (lit-neg lit->aig-lit))
                (get-aig (lit-id lit->aig-lit) ,aigtransv))))

  (defiteration aignet-translate (aigtrans aignet)
    (declare (xargs :stobjs (aigtrans aignet)
                    :guard
                    (<= (num-fanins aignet) (aigs-length aigtrans))
                    :guard-hints
                    ('(:in-theory (enable aignet-idp)))))
    (b* ((slot0 (id->slot id 0 aignet))
         (type (snode->type slot0))
         ((when (or (int= type (in-type))
                    (int= type (out-type))))
          aigtrans)
         (aig
          (aignet-case
           type
           :gate (b* ((f0 (snode->fanin slot0))
                      (slot1 (id->slot id 1 aignet))
                      (f1 (snode->fanin slot1))
                      (xor (snode->regp slot1))
                      (aig0 (lit->aig f0 aigtrans))
                      (aig1 (lit->aig f1 aigtrans)))
                   (if (eql xor 1)
                       (aig-xor aig0 aig1)
                     (aig-and aig0 aig1)))
           :otherwise nil)))
      (set-aig id aig aigtrans))
    :returns aigtrans
    :index id
    :first 0
    :last (num-fanins aignet))

  (in-theory (disable aignet-translate))
  (local (in-theory (enable aignet-translate)))

  (defthm aignet-translate-iter-preserves-id-trans-logic
    (equal (id-trans-logic id (aignet-translate-iter n aigtrans aignet)
                           aignet)
           (id-trans-logic id aigtrans aignet))
    :hints((acl2::just-induct-and-expand
            (aignet-translate-iter n aigtrans aignet))))

  (defthm aignet-translate-iter-preserves-input-entries
    (implies (equal (id->type id aignet) (in-type))
             (equal (nth id (aignet-translate-iter n aigtrans aignet))
                    (nth id aigtrans)))
    :hints((acl2::just-induct-and-expand
            (aignet-translate-iter n aigtrans aignet))))

  (defthm aignet-trans-invariant-of-aignet-translate-iter
    (aignet-trans-invariant
     n (aignet-translate-iter n aigtrans aignet) aignet)
    :hints((acl2::just-induct-and-expand
            (aignet-translate-iter n aigtrans aignet))
           (and stable-under-simplificationp
                '(:expand ((:free (aigtrans)
                            (aignet-trans-invariant
                             n aigtrans aignet)))))
           (and stable-under-simplificationp
                '(:expand ((id-trans-logic (+ -1 n) aigtrans aignet)
                           (aignet-trans-invariant 0 aigtrans aignet))))))

  (defthm aignet-aigs-size-of-aignet-translate-iter
    (<= (len aigtrans)
        (len (aignet-translate-iter n aigtrans aignet)))
    :hints((acl2::just-induct-and-expand
            (aignet-translate-iter n aigtrans aignet)))
    :rule-classes :linear)

  (defthm aignet-translate-preserves-id-trans-logic
    (equal (id-trans-logic id (aignet-translate aigtrans aignet)
                           aignet)
           (id-trans-logic id aigtrans aignet)))

  (defthm aignet-translate-preserves-input-entries
    (implies (equal (id->type id aignet) (in-type))
             (equal (nth id (aignet-translate aigtrans aignet))
                    (nth id aigtrans))))

  (defthm aignet-trans-invariant-of-aignet-translate
    (aignet-trans-invariant
     (+ 1 (fanin-count aignet))
     (aignet-translate aigtrans aignet) aignet))

  (defthm aignet-aigs-size-of-aignet-translate
    (<= (len aigtrans)
        (len (aignet-translate aigtrans aignet)))
    :rule-classes :linear))



(define aignet-trans-get-outs-aux ((n :type (integer 0 *))
                                   aigtrans aignet
                                   aig-acc)
  :enabled t
  :guard (and (<= (num-fanins aignet) (aigs-length aigtrans))
              (<= n (num-outs aignet))
              (true-listp aig-acc))
  :guard-hints (("goal" :in-theory (enable LOOKUP-STYPE-IN-BOUNDS)))
  :measure (nfix (- (nfix (num-outs aignet))
                    (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-outs aignet)
                                 (nfix n)))
                   :exec (int= n (num-outs aignet))))
        (reverse aig-acc)))
    (aignet-trans-get-outs-aux
     (1+ (lnfix n)) aigtrans aignet
     (cons (lit->aig (outnum->fanin n aignet) aigtrans)
           aig-acc))))

(define aignet-trans-get-outs ((n :type (integer 0 *))
                               aigtrans aignet)
  :guard (and (<= (num-fanins aignet) (aigs-length aigtrans))
              (<= n (num-outs aignet)))
  :measure (nfix (- (nfix (num-outs aignet))
                    (nfix n)))
  :verify-guards nil
  :returns (outs (equal (len outs)
                        (nfix (- (num-outs aignet) (nfix n)))))
  (mbe :logic
       (b* (((when (mbe :logic (zp (- (num-outs aignet)
                                      (nfix n)))
                        :exec (int= n (num-outs aignet))))
             nil))
         (cons (lit->aig (outnum->fanin n aignet) aigtrans)
               (aignet-trans-get-outs (1+ (lnfix n)) aigtrans aignet)))
       :exec
       (aignet-trans-get-outs-aux n aigtrans aignet nil))
  ///
  (defthm aignet-trans-get-outs-aux-elim
    (implies (true-listp aig-acc)
             (equal (aignet-trans-get-outs-aux n aigtrans aignet aig-acc)
                    (revappend aig-acc
                               (aignet-trans-get-outs n aigtrans aignet)))))
  (verify-guards aignet-trans-get-outs))

(define aignet-trans-get-nxsts ((n :type (integer 0 *))
                                aigtrans aignet)
  :guard (and (<= (num-fanins aignet) (aigs-length aigtrans))
              (<= (nfix n) (num-regs aignet)))
  :guard-hints (("goal" :in-theory (enable LOOKUP-STYPE-IN-BOUNDS)))
  :measure (nfix (- (nfix (num-regs aignet))
                    (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix (num-regs aignet))
                                 (nfix n)))
                   :exec (int= n (num-regs aignet))))
        nil)
       (nxst (regnum->nxst n aignet)))
    (cons (lit->aig nxst aigtrans)
          (aignet-trans-get-nxsts (1+ (lnfix n)) aigtrans aignet))))

(define aignet-trans-set-ins ((n :type (integer 0 *))
                              innames aigtrans aignet)
  :guard (and (<= (num-fanins aignet) (aigs-length aigtrans))
              (<= n (num-ins aignet))
              (equal (len innames) (- (num-ins aignet) n)))
  :measure (nfix (- (nfix (num-ins aignet))
                    (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix (num-ins aignet))
                                 (nfix n)))
                   :exec (int= n (num-ins aignet))))
        aigtrans)
       (aigtrans
        (set-aig (innum->id n aignet) (car innames) aigtrans)))
    (aignet-trans-set-ins (1+ (lnfix n)) (cdr innames) aigtrans aignet))
  ///
  (defthm aignet-aigs-size-of-aignet-trans-set-ins
    (<= (len aigtrans)
        (len (aignet-trans-set-ins n innames aigtrans aignet)))
    :rule-classes :linear))

(define aignet-trans-set-regs ((n :type (integer 0 *))
                               regnames aigtrans aignet)
  :guard (and (<= (num-fanins aignet) (aigs-length aigtrans))
              (<= (nfix n) (num-regs aignet))
              (equal (len regnames) (- (num-regs aignet) n)))
  :measure (nfix (- (nfix (num-regs aignet))
                    (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix (num-regs aignet))
                                 (nfix n)))
                   :exec (int= n (num-regs aignet))))
        aigtrans)
       (reg (regnum->id n aignet))
       (aigtrans
        (set-aig reg (car regnames) aigtrans)))
    (aignet-trans-set-regs (1+ (lnfix n)) (cdr regnames) aigtrans aignet))
  ///
  (defthm aignet-aigs-size-of-aignet-trans-set-regs
    (<= (len aigtrans)
        (len (aignet-trans-set-regs n innames aigtrans aignet)))
    :rule-classes :linear))


(define aignet-to-aigs (innames regnames aignet)
  :guard (and (equal (len innames) (num-ins aignet))
              (equal (len regnames) (num-regs aignet))
              (true-listp innames)
              (true-listp regnames))
  :prepwork ((local (defthm alistp-of-pairlis$
                      (alistp (pairlis$ x y)))))
  :returns (mv (outs (equal (len outs) (num-outs aignet)))
               (regs (and (alistp regs)
                          (equal (acl2::alist-keys regs)
                                 (acl2::list-fix regnames)))))
  (b* (((local-stobjs aigtrans)
        (mv outlist regalist aigtrans))
       (aigtrans (resize-aigs (num-fanins aignet) aigtrans))
       (aigtrans (aignet-trans-set-ins 0 innames aigtrans aignet))
       (aigtrans (aignet-trans-set-regs 0 regnames aigtrans aignet))
       (aigtrans (aignet-translate aigtrans aignet))
       (outlist (aignet-trans-get-outs 0 aigtrans aignet))
       (reglist (aignet-trans-get-nxsts 0 aigtrans aignet)))
    (mv outlist (pairlis$ regnames reglist) aigtrans)))
