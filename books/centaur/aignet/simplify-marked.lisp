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

(include-book "transform-stub")
(include-book "transform-utils")

(local (in-theory (disable w)))

(define count-1s ((x bit-listp))
  :returns (count natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (+ (lbfix (car x))
       (count-1s (cdr x)))))

(define index-of-nth-set-bit ((n natp) (x bit-listp))
  :measure (len x)
  (if (or (atom x)
          (and (zp n)
               (equal (car x) 1)))
      0
    (+ 1 (index-of-nth-set-bit (- (lnfix n) (lbfix (car x))) (cdr x))))
  ///
  (local (in-theory (enable count-1s)))

  (defthm nth-of-index-of-nth-set-bit
    (implies (< (nfix n) (count-1s x))
             (equal (nth (index-of-nth-set-bit n x) x) 1)))

  (defthm count-take-of-index-of-nth-set-bit
    (implies (< (nfix n) (count-1s x))
             (equal (count-1s (take (index-of-nth-set-bit n x) x))
                    (nfix n)))))
      

(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil) nil)))

(local (defthm consp-of-nthcdr
         (iff (consp (nthcdr n x))
              (< (nfix n) (len x)))))

(local (defthm car-of-nthcdr
         (equal (car (nthcdr n x))
                (nth n x))))

(local (defthm cdr-of-nthcdr
         (equal (cdr (nthcdr n x))
                (nthcdr n (cdr x)))))

(define aignet-add-outs-for-marked-ids ((n natp)
                                        bitarr
                                        aignet)
  :guard (and (<= n (bits-length bitarr))
              (<= (bits-length bitarr) (num-fanins aignet)))
  :returns new-aignet
  :measure (nfix (- (bits-length bitarr) (nfix n)))
  (b* (((when (mbe :logic (zp (- (bits-length bitarr) (nfix n)))
                   :exec (eql n (bits-length bitarr))))
        (aignet-fix aignet))
       ((when (eql (get-bit n bitarr) 0))
        (aignet-add-outs-for-marked-ids (1+ (lnfix n)) bitarr aignet))
       (aignet (aignet-add-out (make-lit n 0) aignet)))
    (aignet-add-outs-for-marked-ids (1+ (lnfix n)) bitarr aignet))
  ///
  (local (defthm stype-fix-equal-forward
           (implies (equal (stype-fix stype) x)
                    (stype-equiv stype x))
           :rule-classes :forward-chaining))

  (defret stype-count-of-<fn>
    (equal (stype-count stype new-aignet)
           (if (equal (stype-fix stype) (po-stype))
               (+ (count-1s (nthcdr n bitarr))
                  (stype-count (po-stype) aignet))
             (stype-count stype aignet)))
    :hints(("Goal" :induct <call>
            :expand ((count-1s (nthcdr n bitarr))))))

  (defret aignet-extension-p-of-<fn>
    (aignet-extension-p new-aignet aignet))

  (local (defthm lookup-stype-of-cons-po
           (implies (equal (nfix m) (stype-count :po aignet))
                    (equal (lookup-stype m :po (cons (po-node lit) aignet))
                           (node-list-fix (cons (po-node lit) aignet))))
           :hints(("Goal" :in-theory (enable lookup-stype)))))

  (fty::deffixequiv aignet-add-outs-for-marked-ids)

  (defret lookup-output-of-<fn>
    (implies (<= (bits-length bitarr) (num-fanins aignet))
             (equal (fanin :co (lookup-stype m (po-stype) new-aignet))
                    (cond ((< (nfix m) (num-outs aignet))
                           (fanin :co (lookup-stype m (po-stype) aignet)))
                          ((< (nfix m) (+ (num-outs aignet) (count-1s (nthcdr n bitarr))))
                           (make-lit (+ (nfix n)
                                        (index-of-nth-set-bit (- (nfix m) (num-outs aignet))
                                                              (nthcdr n bitarr)))
                                     0))
                          (t 0))))
    :hints(("Goal" :in-theory (enable index-of-nth-set-bit aignet-lit-fix aignet-id-fix aignet-idp)
            :induct <call>
            :expand ((count-1s (nthcdr n bitarr))
                     (:free (x) (index-of-nth-set-bit x (nthcdr n bitarr)))
                     <call>)
            :do-not-induct t))))


(define aignet-map-outputs-by-bitarr ((n natp "index in bitarr")
                                      (out natp "index in outputs")
                                      aignet bitarr litarr)
  :guard (and (<= n (bits-length bitarr))
              (<= (non-exec (count-1s (nthcdr n bitarr)))
                  (- (num-outs aignet) out))
              (<= (bits-length bitarr) (lits-length litarr)))
  :guard-hints (("goal" :Expand ((count-1s (nthcdr n bitarr)))))
  :measure (nfix (- (bits-length bitarr) (nfix n)))
  :returns (new-litarr)
  (b* (((when (mbe :logic (zp (- (bits-length bitarr) (nfix n)))
                   :exec (eql n (bits-length bitarr))))
        litarr)
       ((unless (eql 1 (get-bit n bitarr)))
        (aignet-map-outputs-by-bitarr (1+ (lnfix n)) out aignet bitarr litarr))
       (litarr (set-lit n (outnum->fanin out aignet) litarr)))
    (aignet-map-outputs-by-bitarr (1+ (lnfix n))
                                  (1+ (lnfix out))
                                  aignet bitarr litarr))
  ///
  (local (include-book "std/lists/nth" :dir :system))
  (local (include-book "std/lists/take" :dir :system))

  (defret lookup-in-aignet-map-outputs-by-bitarr
    (equal (nth-lit m new-litarr)
           (if (or (< (nfix m) (nfix n))
                   (not (equal 1 (nth m bitarr))))
               (nth-lit m litarr)
             (fanin :co (lookup-stype (+ (nfix out)
                                         (count-1s (nthcdr n (take m bitarr))))
                                      (po-stype)
                                      aignet))))
    :hints (("goal" :induct <call>
             :expand (<call>
                      (count-1s (nthcdr n (take m bitarr))))
             :in-theory (enable* arith-equiv-forwarding))))

  (defret litarr-len-of-<fn>
    (implies (<= (len bitarr) (len litarr))
             (equal (len new-litarr) (len litarr)))))

(local (include-book "std/lists/resize-list" :dir :system))

(defthm aignet-idp-of-aignet-fanins
  (equal (aignet-idp x (aignet-fanins aignet))
         (aignet-idp x aignet))
  :hints(("Goal" :in-theory (enable aignet-idp))))

(defthm id-eval-of-aignet-fanins
  (equal (id-eval id invals regvals (aignet-fanins aignet))
         (id-eval id invals regvals aignet))
  :hints (("goal" :induct (id-eval-ind id aignet)
           :expand ((:free (aignet) (id-eval id invals regvals aignet)))
           :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))))

(defthm lit-eval-of-aignet-fanins
  (equal (lit-eval lit invals regvals (aignet-fanins aignet))
         (lit-eval lit invals regvals aignet))
  :hints(("Goal"
           :expand ((:free (aignet) (lit-eval lit invals regvals aignet))))))

(local (defthm lit-eval-of-fanin-equals-output-eval
         (implies (< (nfix n) (stype-count :po aignet))
                  (equal (lit-eval (fanin :co (lookup-stype n :po aignet))
                                   invals regvals aignet)
                         (output-eval n invals regvals aignet)))
         :hints(("Goal" :in-theory (enable output-eval)
                 :expand ((:free (invals regvals aignet)
                           (id-eval (fanin-count (lookup-stype n :po aignet))
                                    invals regvals aignet)))))))

(local (defthm count-1s-of-take
         (<= (count-1s (take n x))
             (count-1s x))
         :hints(("Goal" :in-theory (enable count-1s take)
                 :induct (take n x)))
         :rule-classes :linear))

(local (defthm count-1s-of-take-strict
         (implies (equal 1 (nth n x))
                  (< (count-1s (take n x))
                     (count-1s x)))
         :hints(("Goal" :in-theory (enable count-1s take)
                 :induct (take n x)))
         :rule-classes :linear))


(local (defthm plus-minus
         (equal (+ x (- x) y)
                (fix y))))

(local (defthm index-of-count-1s-of-take
         (implies (equal 1 (nth n bitarr))
                  (equal (index-of-nth-set-bit (count-1s (take n bitarr)) bitarr)
                         (nfix n)))
         :hints(("Goal" :in-theory (enable take nth index-of-nth-set-bit count-1s)
                 :expand ((:free (a b) (index-of-nth-set-bit (+ a b) bitarr)))
                 :induct (take n bitarr)))))

(define aignet-simplify-marked (aignet
                                bitarr
                                litarr
                                config
                                state)
  :guard (<= (bits-length bitarr) (num-fanins aignet))
  :returns (mv new-aignet new-litarr new-state)
  (b* (((acl2::local-stobjs aignet2)
        (mv aignet2 aignet litarr state))
       (aignet2 (aignet-raw-copy-fanins-top aignet aignet2))
       (aignet2 (aignet-add-outs-for-marked-ids 0 bitarr aignet2))
       ((mv aignet2 state) (aignet-comb-transform!-stub aignet2 config state))
       (litarr (resize-lits (bits-length bitarr) litarr))
       (litarr (aignet-map-outputs-by-bitarr 0 0 aignet2 bitarr litarr))
       (aignet (aignet-raw-copy-fanins-top aignet2 aignet)))
    (mv aignet2 aignet litarr state))
  ///
  (defret stype-count-of-<fn>
    (and (equal (stype-count :pi new-aignet)
                (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet)
                (stype-count :reg aignet))
         (equal (stype-count :po new-aignet) 0)
         (equal (stype-count :nxst new-aignet) 0)))

  (local (defthm nth-implies-less-than-len
           (implies (nth n x)
                    (< (nfix n) (len x)))
           :rule-classes :forward-chaining))

  (local (in-theory (enable aignet-idp)))

  (defret eval-of-<fn>
    (implies (and (equal 1 (nth n bitarr))
                  (<= (bits-length bitarr) (num-fanins aignet)))
             (equal (lit-eval (nth-lit n new-litarr) invals regvals new-aignet)
                    (id-eval n invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (output-eval lit-eval)
                                   (lit-eval-of-fanin-equals-output-eval))
                   :do-not-induct t)))
    :otf-flg t)

  (defret litarr-length-of-<fn>
    (equal (len new-litarr)
           (len bitarr)))

  (defret aignet-litp-of-litarr-entries
    (implies (equal 1 (nth n bitarr))
             (aignet-litp (nth-lit n new-litarr) new-aignet)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



       
