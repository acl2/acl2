; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "FGL")




(include-book "logicman-transform")
(include-book "centaur/aignet/simplify-marked" :dir :system)
(include-book "interp-st-bfrs-ok")
(include-book "add-primitives")
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (std::add-default-post-define-hook :fix))

(define bfrlist->aignet-lits ((x bfr-listp) &optional ((bfrstate bfrstate-p) 'bfrstate))
  :guard (bfrstate-mode-is :aignet)
  :returns (lits aignet::lit-listp)
  (if (atom x)
      nil
    (cons (bfr->aignet-lit (car x))
          (bfrlist->aignet-lits (cdr x))))
  ///
  (defret lits-max-id-val-of-<fn>
    (implies (bfrstate-mode-is :aignet)
             (<= (aignet::lits-max-id-val lits) (bfrstate->bound bfrstate)))
    :hints(("Goal" :in-theory (enable aignet::lits-max-id-val
                                      bfr->aignet-lit bfr-fix aignet-lit->bfr)))
    :rule-classes :linear))

#!aignet
(define aignet-copies-above-n-in-bounds ((n natp) litarr aignet)
  :guard (<= n (lits-length litarr))
  :measure (nfix (- (lits-length litarr) (nfix n)))
  :returns in-bounds
  (if (mbe :logic (zp (- (lits-length litarr) (nfix n)))
           :exec (Eql (lits-length litarr) n))
      t
    (and (fanin-litp (get-lit n litarr) aignet)
         (aignet-copies-above-n-in-bounds (1+ (lnfix n)) litarr aignet)))
  ///
  (local (defthm nth-lit-out-of-bounds
           (implies (<= (len litarr) (nfix n))
                    (equal (nth-lit n litarr) 0))
           :hints(("Goal" :in-theory (enable nth-lit)))))

  (defret <fn>-implies
    (implies (and in-bounds
                  (<= (nfix n) (nfix i)))
             (aignet-litp (nth-lit i litarr) aignet))
    :hints (("goal" :induct <call>)
            '(:in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret <fn>-implies-linear
    (implies (and in-bounds
                  (<= (nfix n) (nfix i)))
             (<= (lit->var (nth-lit i litarr)) (fanin-count aignet)))
    :hints (("goal" :induct <call>)
            '(:in-theory (enable* acl2::arith-equiv-forwarding aignet::aignet-idp))))

  (defret <fn>-implies-lit-copy
    (implies (and in-bounds
                  (<= (nfix n) (lit->var lit)))
             (aignet-litp (lit-copy lit litarr) aignet)))

  (defret <fn>-of-update-lower
    (implies (< (nfix m) (nfix n))
             (equal (let ((litarr (update-nth-lit m lit litarr))) <call>)
                    in-bounds))))

#!aignet
(define aignet-copies-above-n-in-bounds-witness ((n natp) litarr aignet)
  :guard (<= n (lits-length litarr))
  :measure (nfix (- (lits-length litarr) (nfix n)))
  :returns (out-of-bounds-idx natp :rule-classes :type-prescription)
  (if (mbe :logic (zp (- (lits-length litarr) (nfix n)))
           :exec (Eql (lits-length litarr) n))
      (lnfix n)
    (if (fanin-litp (get-lit n litarr) aignet)
        (aignet-copies-above-n-in-bounds-witness (1+ (lnfix n)) litarr aignet)
      (lnfix n)))
  ///
  (local (in-theory (enable aignet-copies-above-n-in-bounds)))
  (defret <fn>-bound-when-not-in-bounds
    (implies (not (aignet-copies-above-n-in-bounds n litarr aignet))
             (< out-of-bounds-idx (lits-length litarr))))

  (defret <fn>-not-aignet-litp
    (implies (not (aignet-copies-above-n-in-bounds n litarr aignet))
             (not (aignet-litp (nth-lit out-of-bounds-idx litarr) aignet))))

  (defretd in-bounds-by-<fn>
    (iff (aignet-copies-above-n-in-bounds n litarr aignet)
         (aignet-litp (nth-lit out-of-bounds-idx litarr) aignet))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable nth-lit))))))

#!aignet
(define aignet-copies-below-n-in-bounds ((n natp) litarr aignet)
  :guard (<= n (lits-length litarr))
  :measure (nfix n)
  :returns in-bounds
  (if (zp n)
      t
    (and (fanin-litp (get-lit (1- n) litarr) aignet)
         (aignet-copies-below-n-in-bounds (1- n) litarr aignet)))
  ///
  ;; (local (defthm nth-lit-out-of-bounds
  ;;          (implies (<= (len litarr) (nfix n))
  ;;                   (equal (nth-lit n litarr) 0))
  ;;          :hints(("Goal" :in-theory (enable nth-lit)))))

  (defret <fn>-implies
    (implies (and in-bounds
                  (< (nfix i) (nfix n)))
             (aignet-litp (nth-lit i litarr) aignet))
    :hints (("goal" :induct <call>)
            '(:in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret <fn>-implies-linear
    (implies (and in-bounds
                  (< (nfix i) (nfix n)))
             (<= (lit->var (nth-lit i litarr)) (fanin-count aignet)))
    :hints (("goal" :induct <call>)
            '(:in-theory (enable* acl2::arith-equiv-forwarding aignet::aignet-idp))))

  (defret <fn>-implies-lit-copy
    (implies (and in-bounds
                  (< (lit->var lit) (nfix n)))
             (aignet-litp (lit-copy lit litarr) aignet)))

  (defret <fn>-of-update-greater
    (implies (<= (nfix n) (nfix m))
             (equal (let ((litarr (update-nth-lit m lit litarr))) <call>)
                    in-bounds)))

  (defret <fn>-of-0
    :pre-bind ((n 0))
    in-bounds))

;; BOZO just for aignet-cis-copied
(include-book "centaur/aignet/prune" :dir :system)

#!aignet    
(define aignet-dfs-copy-back-marked-nodes ((n natp)
                                           (bitarr "Marks nodes in aignet2 that
                                                    were copied to aignet and need
                                                    copying back")
                                           (litarr "Maps nodes in aignet2 that
                                                    were copied to their copies
                                                    in aignet.  Updated as we go
                                                    to map back to the new copies
                                                    in aignet2.")
                                           (aignet "Copying from this AIG")
                                           mark
                                           (copy "Maps nodes in aignet to their copies in aignet2")
                                           strash
                                           (gatesimp gatesimp-p)
                                           (aignet2 "Copying back to this AIG"))
  :guard (and (<= n (bits-length bitarr))
              (<= (bits-length bitarr) (num-fanins aignet2))
              (<= (bits-length bitarr) (lits-length litarr))
              (aignet-copies-above-n-in-bounds n litarr aignet)
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (lits-length copy))
              (ec-call (aignet-marked-copies-in-bounds copy mark aignet2))
              (ec-call (aignet-input-copies-in-bounds copy aignet aignet2)))
  :measure (nfix (- (bits-length bitarr) (nfix n)))
  :returns (mv new-litarr new-mark new-copy new-strash new-aignet2)
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable aignet::aignet-idp)
                 :expand ((aignet-copies-above-n-in-bounds n litarr aignet))))
  (b* (((when (mbe :logic (zp (- (bits-length bitarr) (nfix n)))
                   :exec (eql (bits-length bitarr) n)))
        (mbe :logic (non-exec (mv litarr mark copy strash (node-list-fix aignet2)))
             :exec (mv litarr mark copy strash aignet2)))
       ((unless (eql 1 (get-bit n bitarr)))
        (b* ((litarr (set-lit n 0 litarr)))
          (aignet-dfs-copy-back-marked-nodes
           (1+ (lnfix n)) bitarr litarr aignet mark copy strash gatesimp aignet2)))
       (aignet2-lit (get-lit n litarr))
       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-rec (lit->var aignet2-lit) aignet mark copy strash gatesimp aignet2))
       (litarr (set-lit n (lit-copy aignet2-lit copy) litarr)))
    (aignet-dfs-copy-back-marked-nodes
     (1+ (lnfix n)) bitarr litarr aignet mark copy strash gatesimp aignet2))
  ///
  (local (in-theory (disable (:d aignet-dfs-copy-back-marked-nodes))))

  (defret litarr-length-of-<fn>
    (implies (<= (len bitarr) (len litarr))
             (equal (len new-litarr) (len litarr)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  ;; (local (defthm aignet-idp-split-when-copies-below-n
  ;;          (implies (and (aignet-copies-below-n-in-bounds n litarr aignet)
  ;;                        (case-split (< (nfix m) (nfix n))))
  ;;                   (aignet-idp (lit->var (nth-lit m litarr)) aignet))))

    ;; (local (defthm nth-lit-out-of-bounds
    ;;        (implies (<= (len litarr) (nfix n))
    ;;                 (equal (nth-lit n litarr) 0))
    ;;        :hints(("Goal" :in-theory (enable nth-lit)))))

  (local (defthm aignet-copies-below-n-in-bounds-when-less
           (implies (and (aignet-copies-below-n-in-bounds n litarr aignet)
                         (<= (nfix m) (nfix n)))
                    (aignet-copies-below-n-in-bounds m litarr aignet))
           :hints(("Goal" :in-theory (enable aignet-copies-below-n-in-bounds)))))

  (local (defthm aignet-copies-below-n-in-bounds-of-extension
           (implies (and (aignet-extension-binding)
                         (aignet-copies-below-n-in-bounds n litarr orig))
                    (aignet-copies-below-n-in-bounds n litarr new))
           :hints(("Goal" :in-theory (enable aignet-copies-below-n-in-bounds)))))

  (defret litarr-aignet-copies-in-bounds-of-<fn>
    (implies (and (aignet-copies-below-n-in-bounds n litarr aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-copies-below-n-in-bounds (len bitarr) new-litarr new-aignet2))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet-copies-below-n-in-bounds)
             :expand <call>)))

  (defret litarr-below-n-preserved-of-<fn>
    (implies (< (nfix k) (nfix n))
             (equal (nth-lit k new-litarr) (nth-lit k litarr)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (defret litarr-above-n-aignet-litp-of-<fn>
    (implies (and (equal (nth k bitarr) 1)
                  (aignet-copies-below-n-in-bounds n litarr aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-litp (nth-lit k new-litarr) new-aignet2))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet-copies-below-n-in-bounds)
             :expand (<call>))
            (and stable-under-simplificationp
                 '(:cases ((< (nfix k) (nfix n)))))))
  
  (local
   (defthm <=-fanin-count-when-aignet-litp
     (implies (aignet-litp lit aignet)
              (<= (lit->var lit) (fanin-count aignet)))
     :hints(("Goal" :in-theory (enable aignet-idp)))))

  (defret litarr-above-n-bfr-p-of-<fn>
    (implies (and (fgl::bfr-markedp bfr bitarr)
                  (aignet-copies-below-n-in-bounds n litarr aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (equal bfrstate (fgl::bfrstate (fgl::bfrmode :aignet) (fanin-count new-aignet2))))
             (fgl::bfr-p (fgl::bfr-map bfr new-litarr) bfrstate))
    :hints(("Goal" :in-theory (e/d (fgl::bfr-p
                                      fgl::bfr-markedp
                                      fgl::bfr-map)
                                   (<fn> aignet-idp)))))

  
                  

  (defret aignet-extension-p-of-<fn>
    (aignet-extension-p new-aignet2 aignet2)
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (local (include-book "std/lists/nth" :dir :system))

  (defret eval-of-marked-of-<fn>
    (implies (and (equal (nth k bitarr) 1)
                  (<= (nfix n) (nfix k))
                  (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (equal (lit-eval (nth-lit k new-litarr) invals regvals new-aignet2)
                    (lit-eval (nth-lit k litarr)
                              (input-copy-values 0 invals regvals aignet copy aignet2)
                              (reg-copy-values 0 invals regvals aignet copy aignet2)
                              aignet)))
    :hints (("goal" :induct <call>
             :in-theory (enable* arith-equiv-forwarding)
             :expand (<call>))))

  (defret eval-lit-copy-of-marked-of-<fn>
    (implies (and (equal (nth (lit->var lit) bitarr) 1)
                  (<= (nfix n) (lit->var lit))
                  (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (equal (lit-eval (lit-copy lit new-litarr) invals regvals new-aignet2)
                    (b-xor (lit->neg lit)
                           (lit-eval (nth-lit (lit->var lit) litarr)
                                     (input-copy-values 0 invals regvals aignet copy aignet2)
                                     (reg-copy-values 0 invals regvals aignet copy aignet2)
                                     aignet))))
    :hints(("Goal" :in-theory (enable lit-copy))))

  ;; (defret bfr-eval-of-marked-of-<fn>
  ;;   (b* ((
  ;;   (implies (and (equal n 0)
  ;;                 (bfr-markedp bfr bitarr)
  ;;                 (dfs-copy-onto-invar aignet mark copy aignet2)
  ;;                 (aignet-marked-copies-in-bounds copy mark aignet2)
  ;;                 (aignet-input-copies-in-bounds copy aignet aignet2)
  ;;                 (aignet-cis-copied aignet copy aignet2)
  ;;                 (lbfr-mode-is :aignet)
  ;;                 (lbfr-p bfr aignet))
  ;;            (equal (bfr-eval (bfr-map bfr new-litarr) env
  ;;                             (update-logicman->aignet new-aignet2 logicman))
  ;;                   (bfr-eval (bfr-map bfr litarr) env
  ;;                             logicman)))
  ;;   :hints (("goal" :induct <call>
  ;;            :in-theory (enable* arith-equiv-forwarding)
  ;;            :expand (<call>))))

  (defret stype-count-of-<fn>
    (and (equal (stype-count :pi new-aignet2)
                (stype-count :pi aignet2))
         (equal (stype-count :reg new-aignet2)
                (stype-count :reg aignet2))
         (equal (stype-count :po new-aignet2)
                (stype-count :po aignet2))
         (equal (stype-count :nxst new-aignet2)
                (stype-count :nxst aignet2)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (defret lit-0-of-<fn>
    (implies (and (equal (nth-lit 0 litarr) 0)
                  (equal (nth-lit 0 copy) 0))
             (equal (nth-lit 0 new-litarr) 0))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet::lit-copy)
             :expand (<call>
                      (aignet-copy-dfs-rec 0 aignet mark copy strash gatesimp aignet2))))))

  
(local
 #!aignet
 (defthm aignet-lit-listp-by-lits-max-id-val
   (implies (< (lits-max-id-val lits) (num-fanins aignet))
            (aignet-lit-listp lits aignet))
   :hints(("Goal" :in-theory (enable lits-max-id-val aignet-idp)))))

(local
 #!aignet
 (defthm nth-lit-of-repeat
   (equal (nth-lit n (acl2::repeat m 0))
          0)
   :hints(("Goal" :in-theory (enable nth-lit)))))

(local
 #!aignet
 (defthm aignet-input-copies-in-bounds-of-copy-set-ins/regs
   (b* (;; (copy (acl2::repeat (+ 1 (fanin-count aignet2)) 0))
        (copy (aignet-copy-set-ins 0 aignet2 copy aignet))
        (copy (aignet-copy-set-regs 0 aignet2 copy aignet)))
     (aignet-input-copies-in-bounds copy aignet2 aignet))
   :hints(("Goal" :in-theory (enable aignet-input-copies-in-bounds)))))


(local
 #!aignet
 (defthm aignet-copies-above-n-in-bounds-of-aignet-simplify-marked-with-tracking
   (b* (((mv ?new-aignet ?new-litarr ?new-state)
         (aignet-simplify-marked-with-tracking
          aignet bitarr mark lits
          (acl2::repeat m 0)
          config state)))
     (aignet-copies-above-n-in-bounds
      n new-litarr new-aignet))
   :hints (("goal" :in-theory (enable in-bounds-by-aignet-copies-above-n-in-bounds-witness)))))

(local
 #!aignet
 (defthm aignet-marked-copies-in-bounds-of-repeat-0
   (aignet-marked-copies-in-bounds copy (acl2::repeat n 0) aignet)
   :hints(("Goal" :in-theory (enable aignet-marked-copies-in-bounds)))))

(local (in-theory (disable resize-list)))

(local (in-theory (disable w)))
                                   
    
(define fgl-simplify-object-logicman ((x fgl-object-p
                                         "Object whose symbolic value will be preserved by the transform.")
                                      (litarr "Receives the mapping from old to new AIG literals")
                                      (transforms)
                                      &key
                                      ((tracked-obj
                                        fgl-object-p
                                        "Object that is not preserved but whose
                                         bits' formulas are tracked through possibly
                                         non-preserving transforms, for heuristic
                                         use by the transforms")
                                       'nil)
                                      ((tracked-bits
                                        fgl-object-p
                                        "Object providing an ordered list of Boolean
                                         conditions that are passed to the transforms
                                         for heuristic use")
                                       'nil)
                                      (logicman 'logicman)
                                      (state 'state))
  :guard (and (lbfr-mode-is :aignet)
              (lbfr-listp (fgl-object-bfrlist x))
              (lbfr-listp (fgl-object-bfrlist tracked-obj))
              (lbfr-listp (fgl-object-bfrlist tracked-bits)))
  :returns (mv (new-litarr)
               (new-logicman)
               (new-state))
  :guard-hints (("goal" :in-theory (enable logicman->bfrstate)
                 :expand ((:free (litarr aignet)
                           (aignet::aignet-copies-above-n-in-bounds
                            0 (aignet::update-nth-lit 0 0 litarr) aignet)))))
  :guard-debug t
  :hooks nil ;; bozo
  (b* (((acl2::local-stobjs bitarr  aignet::mark aignet::copy aignet::aignet2)
        (mv litarr logicman bitarr aignet::mark aignet::copy aignet::aignet2 state))
       (size (+ 1 (bfrstate->bound (logicman->bfrstate))))
       (bitarr (resize-bits size bitarr))
       ((mv bitarr seen) (fgl-object-mark-bfrs x bitarr nil))
       (- (fast-alist-free seen))
       (aignet::mark (resize-bits size aignet::mark))
       ((mv aignet::mark seen) (fgl-object-mark-bfrs tracked-obj aignet::mark nil))
       (- (fast-alist-free seen))
       (tracked-lits (bfrlist->aignet-lits (fgl-object-bfrlist tracked-bits)
                                           (logicman->bfrstate)))
       (litarr (resize-lits 0 litarr))
       (litarr (resize-lits size litarr)))
    (stobj-let
     ((aignet (logicman->aignet logicman))
      (strash (logicman->strash logicman)))

     (strash aignet aignet::mark aignet::copy aignet::aignet2 litarr state)

     (b* ((aignet::aignet2 (aignet::aignet-raw-copy-fanins-top aignet aignet::aignet2))
          ((mv aignet::aignet2 litarr state)
           (aignet::aignet-simplify-marked-with-tracking
            aignet::aignet2 bitarr aignet::mark tracked-lits litarr transforms state))
          (aignet::copy (resize-lits (aignet::num-fanins aignet::aignet2) aignet::copy))
          (aignet::mark (resize-bits 0 aignet::mark))
          (aignet::mark (resize-bits (aignet::num-fanins aignet::aignet2) aignet::mark))
          (aignet::copy (aignet::aignet-copy-set-ins 0 aignet::aignet2 aignet::copy aignet))
          (aignet::copy (aignet::aignet-copy-set-regs 0 aignet::aignet2 aignet::copy aignet))
           ;; presumably already the case, but we need to make sure for some
           ;; dumb reason to do with literal<->bfr conversion
          (litarr (aignet::set-lit 0 0 litarr))
          ((mv litarr aignet::mark aignet::copy strash aignet)
           (aignet::aignet-dfs-copy-back-marked-nodes
            0 bitarr litarr aignet::aignet2 aignet::mark aignet::copy strash (aignet::make-gatesimp) aignet)))
       (mv strash aignet aignet::mark aignet::copy aignet::aignet2 litarr state))

     (mv litarr logicman bitarr aignet::mark aignet::copy aignet::aignet2 state)))
  ///

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret logicman-get-of-<fn>
    (implies (and (not (equal (logicman-field-fix k) :strash))
                  (not (equal (logicman-field-fix k) :aignet)))
             (equal (logicman-get k new-logicman)
                    (logicman-get k logicman))))

  ;; (local
  ;;  #!aignet
  ;;  (defthm <=-fanin-count-when-aignet-litp
  ;;    (implies (aignet-litp lit aignet)
  ;;             (<= (lit->var lit) (fanin-count aignet)))
  ;;    :hints(("Goal" :in-theory (enable aignet-idp)))))

  (local (defthm bfrs-markedp-necc-bind
           (implies (and (member-equal bfr immed-bfrs)
                         (bfrs-markedp immed-bfrs bitarr))
                    (bfr-markedp bfr bitarr))
           :hints(("Goal" :in-theory (enable bfrs-markedp-necc)))))


  (defret bfr-litarr-p-of-<fn>
    (implies (and (equal bound (bfrstate->bound (logicman->bfrstate new-logicman)))
                  (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x)))
             (bfr-litarr-p (fgl-object-bfrlist x) new-litarr bound))
    :hints(("Goal" :in-theory (enable bfr-litarr-p-by-witness))
           (and stable-under-simplificationp
                (let ((witness (acl2::find-call-lst 'BFR-LITARR-P-WITNESS clause)))
                  (and witness
                       `(:clause-processor
                         (acl2::simple-generalize-cp
                          clause
                          '((,witness . bfr)))))))))

  (local (defthm nth-mark-when-bfr-markedp
           (implies (and (bfr-markedp bfr bitarr)
                         (not (equal bfr t))
                         bfr
                         (not (equal bfr 0)))
                    (equal (equal 1 (nth (satlink::lit->var bfr) bitarr))
                           t))
           :hints(("Goal" :in-theory (enable bfr-markedp)))))


  (local
   #!aignet
   (defthm id-eval-of-var-when-aignet-lit-fix-equal-1
     (implies (equal (aignet-lit-fix lit aignet) 1)
              (equal (id-eval (lit->var lit) invals regvals aignet)
                     (b-not (lit->neg lit))))
     :hints(("Goal" :in-theory (enable aignet-lit-fix aignet-id-fix
                                       satlink::equal-of-make-lit)
             :expand ((id-eval (lit->var lit) invals regvals aignet))))))

  (local
   #!aignet
   (defthm id-eval-of-var-when-aignet-lit-fix-equal-0
     (implies (equal (aignet-lit-fix lit aignet) 0)
              (equal (id-eval (lit->var lit) invals regvals aignet)
                     (lit->neg lit)))
     :hints(("Goal" :in-theory (enable aignet-lit-fix aignet-id-fix
                                       satlink::equal-of-make-lit)
             :expand ((id-eval (lit->var lit) invals regvals aignet))))))

  (local
   #!aignet
   (defthm lit-eval-when-known-id-eval
     (implies (and (equal v (id-eval (lit->var lit) invals regvals aignet))
                   (syntaxp (quotep v)))
              (equal (lit-eval lit invals regvals aignet)
                     (b-xor v (lit->neg lit))))
     :hints (("goal" :expand ((lit-eval lit invals regvals aignet))))))

  (local
   #!aignet
   (progn
     (defthm id-eval-of-repeat-nil-regs
       (equal (id-eval id invals (acl2::repeat k nil) aignet)
              (id-eval id invals nil aignet))
       :hints (("goal" :induct (id-eval-ind id aignet)
                :expand ((:free (invals regvals)
                          (id-eval id invals regvals aignet)))
                :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))))

     (defthm lit-eval-of-repeat-nil
       (equal (lit-eval lit invals (acl2::repeat k nil) aignet)
              (lit-eval lit invals nil aignet))
       :hints (("goal" 
                :expand ((:free (invals regvals)
                          (lit-eval lit invals regvals aignet))))))))
  ;; (local
  ;;  #!aignet
  ;;  (defthm lit-eval-when-aignet-lit-fix-equal-0
  ;;    (implies (equal (aignet-lit-fix lit aignet) 0)
  ;;             (equal (lit-eval lit invals regvals aignet)
  ;;                    0))
  ;;    :hints(("Goal" :in-theory (enable aignet-lit-fix aignet-id-fix
  ;;                                      satlink::equal-of-make-lit)
  ;;            :expand ((id-eval (lit->var lit) invals regvals aignet)
  ;;                     (lit-eval lit invals regvals aignet))))))

  (local
   (defthm bfr-eval-aignet-mode
     (implies (lbfr-mode-is :aignet)
              (equal (bfr-eval x env logicman)
                     (bit->bool (aignet::lit-eval
                                 (bfr->aignet-lit x (logicman->bfrstate))
                                 (alist-to-bitarr (aignet::num-ins (logicman->aignet logicman))
                                                  env nil)
                                 nil (logicman->aignet logicman)))))
     :hints(("Goal" :in-theory (enable bfr-eval)))))

  (local (defthm bfr->aignet-lit-of-bfr-map
           (implies (and (bfr-p (bfr-map bfr litarr) bfrstate2)
                         (bfrstate-mode-is :aignet bfrstate2)
                         (bfr-p bfr (bfrstate (bfrmode :aignet) (+ -1 (len litarr))))
                         (equal (aignet::nth-lit 0 litarr) 0)
                         (<= 1 (len litarr)))
                    (equal (bfr->aignet-lit (bfr-map bfr litarr) bfrstate2)
                           (aignet::lit-copy (bfr->aignet-lit bfr (bfrstate
                                                                   (bfrmode :aignet)
                                                                   (+ -1 (len litarr))))
                                             litarr)))
           :hints(("Goal" :in-theory (enable bfr->aignet-lit bfr-fix bfr-p bfr-map aignet::lit-copy
                                             satlink::lit-negate-cond
                                             satlink::equal-of-make-lit
                                             aignet-lit->bfr
                                             bounded-lit-fix
                                             bfr-fix)
                   :do-not-induct t))))


  (local
   (defthm nth-equal-1-of-bfr->aignet-lit
     (implies (and (bfrstate-mode-is :aignet)
                   (not (equal (satlink::lit->var (bfr->aignet-lit bfr bfrstate)) 0)))
              (equal (equal (nth (satlink::lit->var (bfr->aignet-lit bfr bfrstate)) bitarr) 1)
                     (bfr-markedp bfr bitarr)))
     :hints(("Goal" :in-theory (enable bfr-markedp bfr->aignet-lit bfr-fix aignet-lit->bfr
                                       bounded-lit-fix)))))

  (local (defthm lit-copy-when-lit->var-equal-0
           (implies (equal (satlink::lit->var x) 0)
                    (equal (aignet::lit-copy x copy)
                           (satlink::lit-negate-cond (aignet::nth-lit 0 copy)
                                                     (satlink::lit->neg x))))
           :hints(("Goal" :in-theory (enable aignet::lit-copy)))))


  (defret bfr-litarr-correct-p-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj))
                  ;; (equal (aignet::nth-lit 0 litarr) 0)
                  )
             (bfr-litarr-correct-p (fgl-object-bfrlist x) env
                                   new-litarr new-logicman logicman))
    :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-by-witness
                                    ;; bfr-eval bfr-map bfr->aignet-lit bfr-fix aignet-lit->bfr
                                    logicman->bfrstate)))
           (and stable-under-simplificationp
                (let ((witness (acl2::find-call-lst 'BFR-LITARR-correct-p-witness clause)))
                  (and witness
                       `(:clause-processor
                         (acl2::simple-generalize-cp
                          clause
                          '((,witness . bfr)))))))
           (and stable-under-simplificationp
                '(:cases ((equal (satlink::lit->var
                                  (bfr->aignet-lit bfr (logicman->bfrstate)))
                                 0))))))

  (defret bfr-litarr-correct-p-all-envs-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj))
                  ;; (equal (aignet::nth-lit 0 litarr) 0)
                  )
             (bfr-litarr-correct-p-all-envs (fgl-object-bfrlist x)
                                   new-litarr new-logicman logicman))
    :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-all-envs)
                                   (<fn>)))))

  (defret litarr-len-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj)))
             (equal (len new-litarr)
                    (+ 1 (bfrstate->bound (logicman->bfrstate logicman)))))
    :hints(("Goal" :in-theory (enable logicman->bfrstate))))

  
  (defret stype-count-of-<fn>
    (b* ((new-aignet (logicman->aignet new-logicman))
         (aignet (logicman->aignet logicman)))
      (and (equal (aignet::stype-count :pi new-aignet)
                  (aignet::stype-count :pi aignet))
           (equal (aignet::stype-count :reg new-aignet)
                  (aignet::stype-count :reg aignet))
           (equal (aignet::stype-count :po new-aignet)
                  (aignet::stype-count :po aignet))
           (equal (aignet::stype-count :nxst new-aignet)
                  (aignet::stype-count :nxst aignet)))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state)))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman)
           (bfr-nvars logicman))))

(define fgl-simplify-object-impl ((x fgl-object-p
                                     "Object whose symbolic value will be preserved by the transform.")
                                  (transforms)
                                  &key
                                  ((tracked-obj
                                    fgl-object-p
                                    "Object that is not preserved but whose bits' formulas
                                are tracked through possibly non-preserving transforms,
                                for heuristic use by the transforms")
                                   'nil)
                                  ((tracked-bits
                                    fgl-object-p
                                    "Object providing an ordered list of Boolean conditions
                                that are passed to the transforms for heuristic
                                use")
                                   'nil)
                                  (logicman 'logicman)
                                  (state 'state))
  :guard (and (lbfr-mode-is :aignet)
              (lbfr-listp (fgl-object-bfrlist x))
              (lbfr-listp (fgl-object-bfrlist tracked-obj))
              (lbfr-listp (fgl-object-bfrlist tracked-bits)))
  :returns (mv (new-x fgl-object-p)
               (new-logicman)
               (new-state))
  :hooks nil
  :guard-hints (("goal" :in-theory (enable logicman->bfrstate)))
  :guard-debug t
  (b* (((acl2::local-stobjs litarr)
        (mv new-x litarr logicman state))
       ((mv litarr logicman state)
        (fgl-simplify-object-logicman
         x litarr transforms
         :tracked-obj tracked-obj
         :tracked-bits tracked-bits ))
       ((mv new-x memo) (fgl-object-map-bfrs-memo x litarr nil)))
    (fast-alist-free memo)
    (mv new-x litarr logicman state))
  ///

  (defret logicman-extension-p-of-<fn>
    (logicman-extension-p new-logicman logicman)
    :hints(("Goal" :in-theory (enable logicman-extension-p))))

  (defret logicman-get-of-<fn>
    (implies (and (not (equal (logicman-field-fix k) :strash))
                  (not (equal (logicman-field-fix k) :aignet)))
             (equal (logicman-get k new-logicman)
                    (logicman-get k logicman))))

  ;; (local
  ;;  (defret eval-of-<fn>-all-envs-bind
  ;;    (implies (and (bind-free '((logicman . logicman)))
  ;;                  (bfr-litarr-correct-p-all-envs (fgl-object-bfrlist x)
  ;;                                                 litarr logicman2 logicman))
  ;;             (equal (fgl-object-eval new-x env logicman2)
  ;;                    (fgl-object-eval x env logicman)))
  ;;    :hints (("goal" :use eval-of-<fn>
  ;;             :in-theory (disable eval-of-<fn>)))
  ;;    :fn fgl-object-map-bfrs))

  (defret eval-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj)))
             (equal (fgl-object-eval new-x env new-logicman)
                    (fgl-object-eval x env logicman)))
    :hints (("goal" :use ((:instance bfr-litarr-correct-p-all-envs-of-fgl-simplify-object-logicman
                           (litarr (create-litarr))))
             :in-theory (disable bfr-litarr-correct-p-all-envs-of-fgl-simplify-object-logicman))))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state)))

  (defret bfr-nvars-of-<fn>
    (equal (bfr-nvars new-logicman)
           (bfr-nvars logicman)))

  (defret bfr-listp-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj)))
             (lbfr-listp (fgl-object-bfrlist new-x) new-logicman))))


(define fgl-simplify-object (x transforms
                             &key
                             ((tracked-obj
                               "Object that is not preserved but whose bits' formulas
                                are tracked through possibly non-preserving transforms,
                                for heuristic use by the transforms")
                              'nil)
                             ((tracked-bits
                               "Object providing an ordered list of Boolean conditions
                                that are passed to the transforms for heuristic use")
                              'nil))
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  x)

(def-formula-checks fgl-simplify-formula-checks
  (fgl-simplify-object-fn))

;; (local (in-theory (enable BFR-LISTP-WHEN-NOT-MEMBER-WITNESS)))
(local (include-book "primitive-lemmas"))

(local (defthm bfr-listp-of-car-objectlist
         (implies (bfr-listp (fgl-objectlist-bfrlist x))
                  (bfr-listp (fgl-object-bfrlist (car x))))))

(local (defthm bfr-listp-of-cdr-objectlist
         (implies (bfr-listp (fgl-objectlist-bfrlist x))
                  (bfr-listp (fgl-objectlist-bfrlist (cdr x))))))

(local (in-theory (disable bfr-listp-when-not-member-witness)))
(local
 (acl2::add-default-hints
  '((and stable-under-simplificationp
         '(:in-theory (enable bfr-listp-when-not-member-witness))))))

(def-fgl-primitive fgl-simplify-object-fn (x transforms tracked-obj tracked-bits)
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (cw "Warning: skipping simplify transform because we're not in aignet mode~%")
        (mv nil nil interp-st state))
       ((unless (fgl-object-case transforms :g-concrete))
        (fgl-interp-error :msg "Fgl-simplify-object: transforms must be a concrete object)"
                          :debug-obj transforms
                          :nvals 2))
       (transforms (g-concrete->val transforms)))
    (stobj-let ((logicman (interp-st->logicman interp-st)))
               (new-x logicman state)
               (fgl-simplify-object-impl
                x transforms :tracked-obj tracked-obj :tracked-bits tracked-bits)
               (mv t new-x interp-st state)))
  :returns (mv successp ans interp-st state)
  :formula-check fgl-simplify-formula-checks)
