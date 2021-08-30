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
(include-book "std/lists/index-of" :dir :system)
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (in-theory (disable resize-list)))
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
             (equal (fanin 0 (lookup-stype m (po-stype) new-aignet))
                    (cond ((< (nfix m) (num-outs aignet))
                           (fanin 0 (lookup-stype m (po-stype) aignet)))
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
            :do-not-induct t)))

  (defret fanin-count-of-<fn>
    (equal (fanin-count new-aignet)
           (fanin-count aignet))))


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
             (fanin 0 (lookup-stype (+ (nfix out)
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

(local (defthm index-of-when-member
         (implies (member-equal k x)
                  (natp (acl2::index-of k x)))
         :rule-classes :type-prescription))

(define aignet-map-outputs-by-lit-list ((lits lit-listp)
                                        (out natp "index in outputs")
                                        aignet litarr)
  :guard (and (< (lits-max-id-val lits) (lits-length litarr))
              (<= (len lits)
                  (- (num-outs aignet) out)))
  :measure (len lits)
  :returns (new-litarr)
  (b* (((when (atom lits)) litarr)
       (lit (car lits))
       (litarr (set-lit (lit->var lit)
                        (lit-negate-cond (outnum->fanin out aignet) (lit->neg lit))
                        litarr)))
    (aignet-map-outputs-by-lit-list (cdr lits)
                                    (1+ (lnfix out))
                                    aignet litarr))
  ///
  ;; (local (include-book "std/lists/nth" :dir :system))
  ;; (local (include-book "std/lists/take" :dir :system))

  ;; This function is only used on tracked/non-preserved outputs, so for now we
  ;; won't prove what a lookup does.  To do so, we'd need to know that the
  ;; lits' variables were duplicate-free or that somehow they were consistent
  ;; with the outputs.



  (defret lookup-in-aignet-map-outputs-by-lit-list
    (implies (no-duplicatesp-equal (lit-list-vars lits))
             (equal (nth-lit m new-litarr)
                    (if (member-equal (nfix m) (lit-list-vars lits))
                        (b* ((index (acl2::index-of (nfix m) (lit-list-vars lits))))
                          (lit-negate-cond
                           (fanin 0 (lookup-stype (+ (nfix out) index)
                                                  (po-stype)
                                                  aignet))
                           (lit->neg (nth index lits))))
                      (nth-lit m litarr))))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* arith-equiv-forwarding
                                 lit-list-vars acl2::index-of))))

  (defret lookup-preserved-in-<fn>
    (implies (not (member-equal (nfix v) (lit-list-vars lits)))
             (equal (nth-lit v new-litarr) (nth-lit v litarr)))
    :hints(("Goal" :in-theory (enable lit-list-vars))))

  (defret lit-listp-lookup-in-<fn>
    (implies (member-equal (nfix v) (lit-list-vars lits))
             (aignet-litp (nth-lit v new-litarr) aignet))
    :hints(("Goal" :in-theory (enable lit-list-vars))))

  (defretd lookup-preserved-in-<fn>-split
    (implies (case-split (not (member-equal (nfix v) (lit-list-vars lits))))
             (equal (nth-lit v new-litarr) (nth-lit v litarr)))
    :hints(("Goal" :in-theory (enable lit-list-vars))))

  (defret litarr-len-of-<fn>
    (implies (< (lits-max-id-val lits) (len litarr))
             (equal (len new-litarr) (len litarr)))))


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
                  (equal (lit-eval (fanin 0 (lookup-stype n :po aignet))
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



(local (defthm aignet-lit-listp-of-aignet-fanins
         (iff (aignet-lit-listp x (aignet-fanins aignet))
              (aignet-lit-listp x aignet))
         :hints(("Goal" :in-theory (enable aignet-lit-listp)))))

(local (defthm lits-max-id-val-when-aignet-lit-listp
         (implies (aignet-lit-listp lits aignet)
                  (< (lits-max-id-val lits) (+ 1 (fanin-count aignet))))
         :hints(("Goal" :in-theory (enable aignet-lit-listp aignet-idp lits-max-id-val)))
         :rule-classes :forward-chaining))


(local (defthm nth-lit-of-resize-list-split
         (equal (nth-lit n (resize-list lits m 0))
                (if (and (< (nfix n) (nfix m))
                         (< (nfix n) (len lits)))
                    (nth-lit n lits)
                  0))
         :hints(("Goal" :in-theory (enable nth-lit)))))

(local (include-book "arithmetic/top" :Dir :system))


(encapsulate nil
  (local
   (defthm id-eval-when-not-aignet-idp
     (implies (not (aignet-idp id aignet))
              (equal (id-eval id invals regvals aignet) 0))
     :hints(("Goal" :in-theory (enable id-eval)))))

  (local
   (defthm aignet-idp-of-cons-po
     (equal (aignet-idp id (cons (po-node lit) aignet))
            (aignet-idp id aignet))
     :hints(("Goal" :in-theory (enable aignet-idp)))))

  (local
   (defthm id-eval-of-cons-po
     (equal (id-eval id invals regvals (cons (po-node lit) aignet))
            (id-eval id invals regvals aignet))
     :hints (("goal" :cases ((aignet-idp id aignet))))))

  (local
   (defthm lit-eval-of-cons-po
     (equal (lit-eval x invals regvals (cons (po-node lit) aignet))
            (lit-eval x invals regvals aignet))
     :hints (("goal" :expand ((:free (aignet) (lit-eval x invals regvals aignet)))))))

  (local (defthm aignet-eval-conjunction-of-cons-po
           (equal (aignet-eval-conjunction lits invals regvals (cons (po-node lit) aignet))
                  (aignet-eval-conjunction lits invals regvals aignet))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))

  (local
   (defthm conjoin-output-range-of-aignet-add-outs-identity-lemma
     (equal (conjoin-output-range (stype-count :po aignet) (len lits)
                                  invals regvals
                                  (aignet-add-outs lits aignet))
            (aignet-eval-conjunction lits invals regvals aignet))
     :hints(("Goal" :in-theory (enable aignet-add-outs
                                       aignet-eval-conjunction
                                       conjoin-output-range
                                       output-eval)
             :expand ((:free (lit)
                       (lookup-stype (stype-count :po aignet)
                                     :po (cons (po-node lit) aignet))))
             :induct (aignet-add-outs lits aignet)))))

  (defthm conjoin-output-range-of-aignet-add-outs-identity
    (implies (and (nat-equiv (stype-count :po aignet) start)
                  (nat-equiv n (len lits)))
             (equal (conjoin-output-range start n invals regvals
                                          (aignet-add-outs lits aignet))
                    (aignet-eval-conjunction lits invals regvals aignet)))
    :hints(("Goal" :in-theory (disable nat-equiv)))))

(defthm aignet-eval-conjunction-of-aignet-fanins
  (equal (aignet-eval-conjunction lits invals regvals (aignet-fanins aignet))
         (aignet-eval-conjunction lits invals regvals aignet))
  :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))


(defsection nth-lit-equiv
  (acl2::def-universal-equiv nth-lit-equiv
    :qvars (n)
    :equiv-terms ((equal (nth-lit n x))))

  (defthm nth-lit-of-nil
    (equal (nth-lit n nil) 0)
    :hints(("Goal" :in-theory (enable nth-lit))))

  (defthm nth-lit-of-repeat
    (equal (nth-lit n (acl2::repeat m 0)) 0)
    :hints(("Goal" :in-theory (enable nth-lit))))

  (defthm nth-lit-equiv-of-repeat-0
    (nth-lit-equiv (acl2::repeat n 0)
                   nil)
    :hints(("Goal" :in-theory (enable nth-lit-equiv))))


  (defcong nth-lit-equiv equal (nth-lit n x) 2
    :hints(("Goal" :in-theory (enable nth-lit-equiv-necc)))))



(define aignet-simplify-marked-with-tracking
  ((aignet "AIG to be transformed")
   (bitarr "Marks AIG nodes to be preserved: if bit N is set, node N will be copied")
   (mark "Marks AIG nodes that are to be tracked: they are not necessarily preserved, but we want to know their mappings if they are.")
   (assum-lits lit-listp)
   (lits lit-listp
         "Specifies literals to be tracked (again not necessarily preserved), ordered.
          They will be added as outputs ot the transformed AIG after the nodes
          specified by bitarr and mark, i.e. the first literal will be set as the
          N+Mth output where N is the number of bits set in bitarr and N is the
          number set in mark.  This is provided so that users may provide output
          numbers for these literals as hints to transformations.")
   (litarr "Overwritten with the map from assumption nodes in the old AIG to literals of the new AIG")
   (copy "Overwritten with the map from non-assumption nodes in the old AIG to literals of the new AIG")
   (config "Combinational transformation config")
   state)
  :parents (aignet)
  :guard (and (<= (bits-length bitarr) (num-fanins aignet))
              (<= (bits-length mark) (num-fanins aignet))
              (aignet-lit-listp lits aignet)
              (aignet-lit-listp assum-lits aignet))
  :guard-debug t
  :returns (mv new-aignet new-litarr new-copy new-state)
  :guard-hints (("goal" :do-not-induct t))
  (b* (((acl2::local-stobjs aignet2)
        (mv aignet2 aignet litarr copy state))
       (aignet2 (aignet-raw-copy-fanins-top aignet aignet2))
       (aignet2 (aignet-add-outs assum-lits aignet2))
       (assum-outs (num-outs aignet2))
       (aignet2 (aignet-add-outs-for-marked-ids 0 bitarr aignet2))
       (preserved-outs (num-outs aignet2))
       (aignet2 (aignet-add-outs-for-marked-ids 0 mark aignet2))
       (marked-outs (num-outs aignet2))
       (aignet2 (aignet-add-outs lits aignet2))
       ((mv aignet2 state) (apply-m-assumption-n-output-transforms! assum-outs (- preserved-outs assum-outs) aignet2 config state))
       (litarr (resize-lits (num-fanins aignet) litarr))
       (copy (resize-lits (num-fanins aignet) copy))
       ;; Copy the tracked/non-preserved outputs first so that the preserved
       ;; ones are authoritative.
       (copy (aignet-map-outputs-by-lit-list lits marked-outs aignet2 copy))
       (copy (aignet-map-outputs-by-bitarr 0 preserved-outs aignet2 mark copy))
       (copy (aignet-map-outputs-by-bitarr 0 assum-outs aignet2 bitarr copy))
       (litarr (aignet-map-outputs-by-lit-list assum-lits 0 aignet2 litarr))
       (aignet (aignet-raw-copy-fanins-top aignet2 aignet)))
    (mv aignet2 aignet litarr copy state))
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

  (defret eval-of-<fn>-when-marked
    (implies (and (equal 1 (nth n bitarr))
                  (<= (bits-length bitarr) (num-fanins aignet))
                  (equal (aignet-eval-conjunction assum-lits invals regvals aignet) 1))
             (equal (lit-eval (nth-lit n new-copy) invals regvals new-aignet)
                    (id-eval n invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (output-eval lit-eval)
                                   (lit-eval-of-fanin-equals-output-eval))
                   :do-not-induct t)))
    :otf-flg t)

  (local (defthm lit->var-nth-index-of-lit-list-vars
           (implies (member-equal n (lit-list-vars x))
                    (equal (lit->var (nth (acl2::index-of n (lit-list-vars x)) x))
                           (nfix n)))
           :hints(("Goal" :in-theory (enable lit-list-vars acl2::index-of)))))

  (defret eval-of-<fn>-when-assumption
    (implies (and (member-equal (nfix n) (lit-list-vars assum-lits))
                  (no-duplicatesp-equal (lit-list-vars assum-lits)))
             (equal (lit-eval (nth-lit n new-litarr) invals regvals new-aignet)
                    (id-eval n invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (output-eval)
                                   (lit-eval-of-fanin-equals-output-eval))
                   :expand ((:free (k) (lit-eval (nth k assum-lits) invals regvals aignet)))
                   :do-not-induct t)))
    :otf-flg t)

  (defret litarr-length-of-<fn>
    (b* ((fanins (+ 1 (fanin-count aignet))))
      (implies (and ;; (<= (len bitarr) fanins)
                    ;; (<= (len mark) fanins)
                    (aignet-lit-listp assum-lits aignet)
                    ;; (aignet-lit-listp lits aignet)
                    )
               (equal (len new-litarr)
                      fanins))))

  (defret copy-length-of-<fn>
    (b* ((fanins (+ 1 (fanin-count aignet))))
      (implies (and (<= (len bitarr) fanins)
                    (<= (len mark) fanins)
                    ;; (aignet-lit-listp assum-lits aignet)
                    (aignet-lit-listp lits aignet))
               (equal (len new-copy)
                      fanins))))

  (defret aignet-litp-of-<fn>-copy-entries
    (implies (equal 1 (nth n bitarr))
             (aignet-litp (nth-lit n new-copy) new-aignet)))

  (defret aignet-litp-of-<fn>-mark-copy-entries
    (implies (equal 1 (nth n mark))
             (aignet-litp (nth-lit n new-copy) new-aignet)))

  (defret aignet-litp-of-<fn>-lits
    (implies (member (nfix n) (lit-list-vars lits))
             (aignet-litp (nth-lit n new-copy) new-aignet))
    :hints(("Goal" :in-theory (disable aignet-idp))))

  (defret aignet-litp-of-<fn>-assum-lits
    (implies (member (nfix n) (lit-list-vars assum-lits))
             (aignet-litp (nth-lit n new-litarr) new-aignet))
    :hints(("Goal" :in-theory (disable aignet-idp))))

  (defret aignet-litp-of-<fn>-lits-when-originally-0
    (implies (equal (nth-lit n litarr) 0)
             (aignet-litp (nth-lit n new-litarr) new-aignet))
    :hints(("Goal" :in-theory (e/d (lookup-preserved-in-aignet-map-outputs-by-lit-list-split)
                                   (aignet-idp)))))

  (defret aignet-litp-of-<fn>-copies-when-originally-0
    (implies (equal (nth-lit n copy) 0)
             (aignet-litp (nth-lit n new-copy) new-aignet))
    :hints(("Goal" :in-theory (e/d (lookup-preserved-in-aignet-map-outputs-by-lit-list-split)
                                   (aignet-idp)))))


  (defret aignet-copies-in-bounds-of-<fn>-copies
    (implies (nth-lit-equiv copy nil)
             (aignet-copies-in-bounds new-copy new-aignet))
    :hints (("goal" :in-theory (e/d (aignet-copies-in-bounds) (<fn> aignet-idp)))))

  (defret aignet-copies-in-bounds-of-<fn>-litarr
    (implies (nth-lit-equiv litarr nil)
             (aignet-copies-in-bounds new-litarr new-aignet))
    :hints (("goal" :in-theory (e/d (aignet-copies-in-bounds) (<fn> aignet-idp)))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(define aignet-output-lits ((n natp) aignet)
  :guard (<= n (num-outs aignet))
  :measure (nfix (- (num-outs aignet) (nfix n)))
  :returns (lits lit-listp)
  (if (mbe :logic (zp (- (num-outs aignet) (nfix n)))
           :exec (eql (num-outs aignet) n))
      nil
    (cons (outnum->fanin n aignet)
          (aignet-output-lits (1+ (lnfix n)) aignet)))
  ///
  (defret aignet-lit-listp-of-<fn>
    (aignet-lit-listp lits aignet))

  (local (defun-nx ind (n k aignet)
           (declare (xargs :measure (nfix (- (num-outs aignet) (nfix n)))))
           (if (zp (nfix (- (num-outs aignet) (nfix n))))
               (list k)
             (ind (1+ (lnfix n)) (1- k) aignet))))

  (defret nth-of-<fn>
    (implies (< (+ (nfix k) (nfix n)) (num-outs aignet))
             (equal (nth k lits)
                    (outnum->fanin (+ (nfix k) (nfix n)) aignet)))
    :hints(("Goal" :in-theory (enable nth)
            :induct (ind n k aignet))))

  (defret len-of-<fn>
    (equal (len lits)
           (nfix (- (num-outs aignet) (nfix n))))))

(local (defthm lit-listp-of-take
         (implies (and (lit-listp x)
                       (<= (nfix n) (len x)))
                  (lit-listp (take n x)))))

(local (defthm lit-listp-of-nthcdr
         (implies (lit-listp x)
                  (lit-listp (nthcdr n x)))))

(local (defthm len-of-nthcdr
         (equal (len (nthcdr n x))
                (nfix (- (len x) (nfix n))))))



(local (defthm aignet-lit-listp-of-take
         (implies (and (aignet-lit-listp x aignet)
                       (<= (nfix n) (len x)))
                  (aignet-lit-listp (take n x) aignet))))

(local (defthm aignet-lit-listp-of-nthcdr
         (implies (aignet-lit-listp x aignet)
                  (aignet-lit-listp (nthcdr n x) aignet))))

(define aignet-simplify-with-tracking
  ((aignet "AIG to be transformed")
   (assum-lits lit-listp "Literals that are assumed")
   (pres-lits lit-listp  "Literals to be preserved")
   (track-lits lit-listp
         "Specifies literals to be tracked (again not necessarily preserved), ordered.
          They will be added as outputs ot the transformed AIG after the
          assumption and preserved lits.  This is provided so that users may
          provide output numbers for these literals as hints to
          transformations.")
   ;; (litarr "Overwritten with the map from assumption nodes in the old AIG to literals of the new AIG")
   ;; (copy "Overwritten with the map from non-assumption nodes in the old AIG to literals of the new AIG")
   (config "Combinational transformation config")
   state)
  :parents (aignet)
  :guard (and (aignet-lit-listp assum-lits aignet)
              (aignet-lit-listp pres-lits aignet)
              (aignet-lit-listp track-lits aignet))
  :guard-debug t
  :returns (mv new-aignet
               (new-assum-lits lit-listp)
               (new-pres-lits lit-listp)
               (new-track-lits lit-listp)
               new-state)
  :guard-hints (("goal" :do-not-induct t))
  (b* (((acl2::local-stobjs aignet2)
        (mv aignet2 aignet new-assum-lits new-pres-lits new-track-lits state))
       (aignet2 (aignet-raw-copy-fanins-top aignet aignet2))
       (aignet2 (aignet-add-outs assum-lits aignet2))
       (assum-outs (num-outs aignet2))
       (aignet2 (aignet-add-outs pres-lits aignet2))
       (preserved-outs (num-outs aignet2))
       (aignet2 (aignet-add-outs track-lits aignet2))
       (tracked-outs (num-outs aignet2))
       ((mv aignet2 state) (apply-m-assumption-n-output-transforms! assum-outs (- preserved-outs assum-outs) aignet2 config state))
       (lits (aignet-output-lits 0 aignet2))
       (new-assum-lits (take assum-outs lits))
       (new-pres-lits (take (- preserved-outs assum-outs) (nthcdr assum-outs lits)))
       (new-track-lits (take (- tracked-outs preserved-outs) (nthcdr preserved-outs lits)))
       (aignet (aignet-raw-copy-fanins-top aignet2 aignet)))
    (mv aignet2 aignet new-assum-lits new-pres-lits new-track-lits state))
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

  (local (defthm aignet-litp-of-nth-when-aignet-lit-listp
           (implies (and (aignet-lit-listp x aignet)
                         (< (nfix n) (len x)))
                    (aignet-litp (nth n x) aignet))))

  (defret eval-of-<fn>-when-preserved
    (implies (and (aignet-lit-listp pres-lits aignet)
                  (equal (aignet-eval-conjunction assum-lits invals regvals aignet) 1))
             (equal (lit-eval (nth n new-pres-lits) invals regvals new-aignet)
                    (lit-eval (nth n pres-lits) invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (output-eval lit-eval)
                                   (lit-eval-of-fanin-equals-output-eval))
                   :do-not-induct t
                   :cases ((< (nfix n) (len pres-lits))))))
    :otf-flg t)

  (local (defthm lit->var-nth-index-of-lit-list-vars
           (implies (member-equal n (lit-list-vars x))
                    (equal (lit->var (nth (acl2::index-of n (lit-list-vars x)) x))
                           (nfix n)))
           :hints(("Goal" :in-theory (enable lit-list-vars acl2::index-of)))))

  (local (defthm lit-eval-of-nil
           (equal (lit-eval nil ins regs aignet) 0)
           :hints(("Goal" :in-theory (enable lit-eval id-eval)))))

  (defret eval-of-<fn>-when-assumption
    (implies (aignet-lit-listp assum-lits aignet)
             (equal (lit-eval (nth n new-assum-lits) invals regvals new-aignet)
                    (lit-eval (nth n assum-lits) invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (output-eval)
                                   (lit-eval-of-fanin-equals-output-eval))
                   :do-not-induct t
                   :cases ((< (nfix n) (len assum-lits))))))
    :otf-flg t)

  (defret aignet-lit-listp-of-<fn>-pres-lits
    (implies (aignet-lit-listp pres-lits aignet)
             (aignet-lit-listp new-pres-lits new-aignet)))

  (defret aignet-lit-listp-of-<fn>-assum-lits
    (implies (aignet-lit-listp assum-lits aignet)
             (aignet-lit-listp new-assum-lits new-aignet)))

  (defret aignet-lit-listp-of-<fn>-track-lits
    (implies (aignet-lit-listp track-lits aignet)
             (aignet-lit-listp new-track-lits new-aignet)))

  (local (defthm len-of-take
           (equal (len (take n x))
                  (nfix n))))

  (defret len-of-<fn>-pres-lits
    (equal (len new-pres-lits) (len pres-lits)))

  (defret len-of-<fn>-assum-lits
    (equal (len new-assum-lits) (len assum-lits)))

  (defret len-of-<fn>-track-lits
    (equal (len new-track-lits) (len track-lits)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))






(define aignet-simplify-marked ((aignet "AIG to be transformed")
                                (bitarr "Marks AIG nodes to be preserved: if bit N is set, node N will be copied")
                                (litarr "Overwritten with the map from nodes in the old AIG to literals of the new AIG")
                                (config "Combinational transformation config")
                                state)
  :parents (aignet)
  :guard (<= (bits-length bitarr) (num-fanins aignet))
  :returns (mv new-aignet new-litarr new-state)
  (b* (((acl2::local-stobjs mark copy)
        (mv mark aignet copy litarr state))
       ((mv aignet copy litarr state) (aignet-simplify-marked-with-tracking
                                  aignet bitarr mark nil nil copy litarr config state)))
    (mv mark aignet copy litarr state))
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

  (local (in-theory (enable aignet-idp aignet-eval-conjunction)))

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
    (let ((fanins (+ 1 (fanin-count aignet))))
      (implies (<= (len bitarr) fanins)
               (equal (len new-litarr) fanins))))

  (defret aignet-litp-of-<fn>-litarr-entries
    (implies (equal 1 (nth n bitarr))
             (aignet-litp (nth-lit n new-litarr) new-aignet))
    :hints(("Goal" :in-theory (disable aignet-idp))))

  (defret aignet-litp-of-<fn>-lits-when-originally-0
    (implies (equal (nth-lit n litarr) 0)
             (aignet-litp (nth-lit n new-litarr) new-aignet))
    :hints(("Goal" :in-theory (e/d (lookup-preserved-in-aignet-map-outputs-by-lit-list-split)
                                   (aignet-idp)))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))





       
