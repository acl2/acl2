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
(include-book "bfrs-replace")
(include-book "centaur/aignet/simplify-marked" :dir :system)
(include-book "interp-st-bfrs-ok")
(include-book "add-primitives")
(include-book "pathcond-transform")
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "centaur/misc/hons-sets" :dir :system))
(local (std::add-default-post-define-hook :fix))


(local (defthm bit-listp-of-lit-eval-list
         #!aignet
         (bit-listp (lit-eval-list x invals regvals aignet))))

;; (define bools->bits ((x boolean-listp))
;;   :returns (bits aignet::bit-listp)
;;   (if (atom x)
;;       nil
;;     (cons (bool->bit (car x))
;;           (bools->bits (cdr x)))))

(defsection bits->bools->bits
  (local (in-theory (enable bools->bits bits->bools)))

  (defthm bits->bools-of-bools->bits
    (equal (bits->bools (bools->bits x))
           (acl2::boolean-list-fix x)))

  (defthm bools->bits-of-bits->bools
    (equal (bools->bits (bits->bools x))
           (aignet::bit-list-fix x))))

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
    :rule-classes :linear)

  (defret len-of-<fn>
    (equal (len lits) (len x)))

  (defret eval-of-<fn>
    (implies (and (equal bfrstate (logicman->bfrstate logicman))
                  (bfrstate-mode-is :aignet))
             (equal (aignet::lit-eval-list lits (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman))
                                                                 env nil)
                                           nil (logicman->aignet logicman))
                    (bools->bits (bfr-list-eval x env))))
    :hints(("Goal" :in-theory (enable bfr-list-eval bools->bits bfr-eval)))))

(define aignet-lits->bfrlist ((x satlink::lit-listp) &optional ((bfrstate bfrstate-p) 'bfrstate))
  :guard (and (bfrstate-mode-is :aignet)
              (<= (aignet::lits-max-id-val x) (bfrstate->bound bfrstate)))
  :returns (bfrs (implies (bfrstate-mode-is :aignet)
                          (bfr-listp bfrs)))
  (if (atom x)
      nil
    (cons (aignet-lit->bfr (car x))
          (aignet-lits->bfrlist (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len bfrs) (len x)))

  (defret eval-of-<fn>
    (implies (and (equal bfrstate (logicman->bfrstate logicman))
                  (bfrstate-mode-is :aignet)
                  (<= (aignet::lits-max-id-val x) (bfrstate->bound bfrstate)))
             (equal (bfr-list-eval bfrs env)
                    (bits->bools (aignet::lit-eval-list x (alist-to-bitarr (aignet::stype-count :pi (logicman->aignet logicman))
                                                                           env nil)
                                                        nil (logicman->aignet logicman)))))
    :hints(("Goal" :in-theory (enable bfr-list-eval bits->bools bfr-eval bounded-lit-fix)))))
    

                              

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
(defsection aignet-copies-in-bounds-when-below-n
  (local (defret <fn>-implies-split
           (implies (and in-bounds
                         (case-split (< (nfix i) (nfix n))))
                    (aignet-litp (nth-lit i litarr) aignet))
           :fn aignet-copies-below-n-in-bounds))
  (local (defthm nth-lit-out-of-bounds
           (implies (<= (len x) (nfix n))
                    (equal (nth-lit n x) 0))
           :hints(("Goal" :in-theory (enable nth-lit)))))

  (defthmd aignet-copies-in-bounds-when-below-n
    (implies (and (aignet-copies-below-n-in-bounds n litarr aignet)
                  (<= (len litarr) (nfix n)))
             (aignet-copies-in-bounds litarr aignet))
    :hints(("Goal" :in-theory (enable aignet-copies-in-bounds)
            :do-not-induct t))))


#!aignet
(defret nth-lit-0-of-aignet-copy-dfs-rec
  (implies (equal (nth-lit 0 copy) 0)
           (equal (nth-lit 0 new-copy) 0))
  :hints (("goal" :induct <call> :expand (<call>)
           :in-theory (enable (:i <fn>))))
  :fn aignet-copy-dfs-rec)

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

  (local (defthm aignet-copies-below-n-in-bounds-when-less
           (implies (and (aignet-copies-below-n-in-bounds n litarr aignet)
                         (<= (nfix m) (nfix n)))
                    (aignet-copies-below-n-in-bounds m litarr aignet))
           :hints(("Goal" :in-theory (enable aignet-copies-below-n-in-bounds)))))
  ;; (local (defthm aignet-idp-split-when-copies-below-n
  ;;          (implies (and (aignet-copies-below-n-in-bounds n litarr aignet)
  ;;                        (case-split (< (nfix m) (nfix n))))
  ;;                   (aignet-idp (lit->var (nth-lit m litarr)) aignet))))

    ;; (local (defthm nth-lit-out-of-bounds
    ;;        (implies (<= (len litarr) (nfix n))
    ;;                 (equal (nth-lit n litarr) 0))
    ;;        :hints(("Goal" :in-theory (enable nth-lit)))))

  (defret copy-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len copy))
                  (aignet-copies-above-n-in-bounds n litarr aignet)
                  (<= (len bitarr) (len litarr)))
             (equal (len new-copy) (len copy)))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet-idp)
             :expand (<call>
                      (aignet-copies-above-n-in-bounds n litarr aignet)))))

  (defret mark-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len mark))
                  (aignet-copies-above-n-in-bounds n litarr aignet)
                  (<= (len bitarr) (len litarr)))
             (equal (len new-mark) (len mark)))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet-idp)
             :expand (<call>
                      (aignet-copies-above-n-in-bounds n litarr aignet)))))

  (local (defthm aignet-copies-below-n-in-bounds-of-extension
           (implies (and (aignet-extension-binding)
                         (aignet-copies-below-n-in-bounds n litarr orig))
                    (aignet-copies-below-n-in-bounds n litarr new))
           :hints(("Goal" :in-theory (enable aignet-copies-below-n-in-bounds)))))

  (defret litarr-aignet-copies-below-n-in-bounds-of-<fn>
    (implies (and (aignet-copies-below-n-in-bounds n litarr aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-copies-below-n-in-bounds (len bitarr) new-litarr new-aignet2))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet-copies-below-n-in-bounds)
             :expand <call>)))

  (defret litarr-aignet-copies-in-bounds-of-<fn>
    (implies (and (aignet-copies-below-n-in-bounds n litarr aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (equal (len bitarr) (len litarr)))
             (aignet-copies-in-bounds new-litarr new-aignet2))
    :hints (("goal" :use litarr-aignet-copies-below-n-in-bounds-of-<fn>
             :in-theory (e/d (aignet-copies-in-bounds-when-below-n)
                             (litarr-aignet-copies-below-n-in-bounds-of-<fn>)))))


  (defret aignet-input-copies-in-bounds-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (aignet-input-copies-in-bounds new-copy aignet new-aignet2))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet-copies-below-n-in-bounds)
             :expand <call>)))

  (defret aignet-marked-copies-in-bounds-of-<fn>
    (implies (and (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
             (aignet-marked-copies-in-bounds new-copy new-mark new-aignet2))
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

  (defret dfs-copy-onto-invar-of-<fn>
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (dfs-copy-onto-invar aignet new-mark new-copy new-aignet2))
    :hints (("goal" :induct <call>
             :expand (<call>))))



  (defret input-copy-values-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (equal (input-copy-values k invals regvals aignet new-copy new-aignet2)
                    (input-copy-values k invals regvals aignet copy aignet2)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (defret reg-copy-values-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (equal (reg-copy-values k invals regvals aignet new-copy new-aignet2)
                    (reg-copy-values k invals regvals aignet copy aignet2)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

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
                      (aignet-copy-dfs-rec 0 aignet mark copy strash gatesimp aignet2)))))

  (defret copy-lit-0-of-<fn>
    (implies (and ;; (equal (nth-lit 0 litarr) 0)
                  (equal (nth-lit 0 copy) 0))
             (equal (nth-lit 0 new-copy) 0))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet::lit-copy)
             :expand (<call>
                      (aignet-copy-dfs-rec 0 aignet mark copy strash gatesimp aignet2))))))



#!aignet
(define aignet-lit-copies-in-bounds ((lits lit-listp) litarr aignet)
  :guard (< (lits-max-id-val lits) (lits-length litarr))
  :returns in-bounds
  (if (atom lits)
      t
    (and (fanin-litp (get-lit (lit->var (car lits)) litarr) aignet)
         (aignet-lit-copies-in-bounds (cdr lits) litarr aignet)))
  ///
  ;; (local (defthm nth-lit-out-of-bounds
  ;;          (implies (<= (len litarr) (nfix n))
  ;;                   (equal (nth-lit n litarr) 0))
  ;;          :hints(("Goal" :in-theory (enable nth-lit)))))

  (defret <fn>-implies
    (implies (and in-bounds
                  (member (nfix i) (lit-list-vars lits)))
             (aignet-litp (nth-lit i litarr) aignet))
    :hints (("goal" :induct <call>
             :in-theory (enable* lit-list-vars
                                 acl2::arith-equiv-forwarding))))

  (defret <fn>-implies-linear
    (implies (and in-bounds
                  (member (nfix i) (lit-list-vars lits)))
             (<= (lit->var (nth-lit i litarr)) (fanin-count aignet)))
    :hints (("goal" :induct <call>
             :in-theory (enable* lit-list-vars
                                 aignet-idp
                                 acl2::arith-equiv-forwarding))))

  (defret <fn>-implies-lit-copy
    (implies (and in-bounds
                  (member-equal (lit->var lit) (lit-list-vars lits)))
             (aignet-litp (lit-copy lit litarr) aignet)))

  (defret <fn>-of-update-non-member
    (implies (not (member-equal (nfix m) (lit-list-vars lits)))
             (equal (let ((litarr (update-nth-lit m lit litarr))) <call>)
                    in-bounds))
    :hints(("Goal" :in-theory (enable* lit-list-vars
                                       acl2::arith-equiv-forwarding))))

  (defret <fn>-of-empty
    :pre-bind ((lits nil))
    in-bounds))

#!aignet
(defsection aignet-non-lit-copies-in-bounds
  (defun-sk aignet-non-lit-copies-in-bounds (lits litarr aignet)
    (forall i
            (implies (not (member-equal (nfix i) (lit-list-vars lits)))
                     (aignet-litp (nth-lit i litarr) aignet)))
    :rewrite :direct)

  (in-theory (disable aignet-non-lit-copies-in-bounds))


  (defthm aignet-non-lit-copies-in-bounds-of-node-list-fix
    (equal (aignet-non-lit-copies-in-bounds lits litarr (node-list-fix aignet))
           (aignet-non-lit-copies-in-bounds lits litarr aignet))
    :hints (("goal" :cases ((aignet-non-lit-copies-in-bounds lits litarr aignet)))
            (and stable-under-simplificationp
                 (let* ((lit (assoc 'aignet-non-lit-copies-in-bounds clause))
                        (other (if (eq (nth 3 lit) 'aignet)
                                   '(node-list-fix aignet)
                                 'aignet)))
                   `(:expand (,lit)
                     :use ((:instance aignet-non-lit-copies-in-bounds-necc
                            (i (aignet-non-lit-copies-in-bounds-witness . ,(cdr lit)))
                            (aignet ,other)))
                     :in-theory (disable aignet-non-lit-copies-in-bounds-necc))))))

  (defthm aignet-non-lit-copies-in-bounds-of-atom
    (implies (not (consp lits))
             (equal (aignet-non-lit-copies-in-bounds lits litarr aignet)
                    (aignet-copies-in-bounds litarr aignet)))
    :hints (("goal" :cases ((aignet-copies-in-bounds litarr aignet))
             :in-theory (e/d (aignet-copies-in-bounds
                              aignet-non-lit-copies-in-bounds
                              lit-list-vars)
                             (aignet-copies-in-bounds-necc
                              aignet-non-lit-copies-in-bounds-necc))
             :use ((:instance aignet-copies-in-bounds-necc
                    (copy litarr)
                    (n (aignet-non-lit-copies-in-bounds-witness lits litarr aignet)))
                   (:instance aignet-non-lit-copies-in-bounds-necc
                    (i (aignet-copies-in-bounds-witness litarr aignet)))))))

  (defthm aignet-non-lit-copies-in-bounds-of-cdr
    (implies (not (aignet-non-lit-copies-in-bounds lits litarr aignet))
             (not (aignet-non-lit-copies-in-bounds (cdr lits) litarr aignet)))
    :hints (("goal" :expand ((aignet-non-lit-copies-in-bounds lits litarr aignet))
             :use ((:instance aignet-non-lit-copies-in-bounds-necc
                    (i (aignet-non-lit-copies-in-bounds-witness lits litarr aignet))
                    (lits (cdr lits))))
             :in-theory (e/d (lit-list-vars) (aignet-non-lit-copies-in-bounds-necc)))))


  (defthm aignet-non-lit-copies-in-bounds-of-cdr-update
    (implies (and (aignet-non-lit-copies-in-bounds lits litarr aignet)
                  (aignet-litp new-lit aignet)
                  (equal (nfix k) (lit->var (car lits))))
             (aignet-non-lit-copies-in-bounds
              (cdr lits)
              (update-nth-lit k new-lit litarr)
              aignet))
    :hints (("goal" :expand ((aignet-non-lit-copies-in-bounds
                              (cdr lits)
                              (update-nth-lit k new-lit litarr)
                              aignet))
             :use ((:instance aignet-non-lit-copies-in-bounds-necc
                    (i (aignet-non-lit-copies-in-bounds-witness
                        (cdr lits)
                        (update-nth-lit k new-lit litarr)
                        aignet))))
             :in-theory (e/d (lit-list-vars) (aignet-non-lit-copies-in-bounds-necc)))))

  (defthm aignet-non-lit-copies-in-bounds-when-copies-in-bounds
    (implies (aignet-copies-in-bounds litarr aignet)
             (aignet-non-lit-copies-in-bounds lit litarr aignet))
    :hints(("Goal" :in-theory (enable aignet-non-lit-copies-in-bounds)))))




#!aignet
(define aignet-dfs-copy-back-lits ((lits lit-listp
                                         "Literals in aignet2 that were copied to aignet and need copying back")
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
  :guard (and (aignet-lit-listp lits aignet2)
              (no-duplicatesp-equal (lit-list-vars lits))
              (< (lits-max-id-val lits) (lits-length litarr))

              (aignet-lit-copies-in-bounds lits litarr aignet)
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (lits-length copy))
              (ec-call (aignet-marked-copies-in-bounds copy mark aignet2))
              (ec-call (aignet-input-copies-in-bounds copy aignet aignet2)))
  :returns (mv new-litarr new-mark new-copy new-strash new-aignet2)
  :guard-hints (("goal" :do-not-induct t
                 :in-theory (enable aignet::aignet-idp lit-list-vars lits-max-id-val)
                 :expand ((aignet-lit-copies-in-bounds lits litarr aignet))))
  (b* (((when (atom lits))
        (mbe :logic (non-exec (mv litarr mark copy strash (node-list-fix aignet2)))
             :exec (mv litarr mark copy strash aignet2)))
       (var (lit->var (car lits)))
       (aignet-lit (get-lit var litarr))
       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-rec (lit->var aignet-lit) aignet mark copy strash gatesimp aignet2))
       (litarr (set-lit var (lit-copy aignet-lit copy) litarr)))
    (aignet-dfs-copy-back-lits
     (cdr lits) litarr aignet mark copy strash gatesimp aignet2))
  ///
  (local (in-theory (disable (:d aignet-dfs-copy-back-marked-nodes))))

  (defret litarr-length-of-<fn>
    (implies (< (lits-max-id-val lits) (len litarr))
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

  ;; (local (defthm aignet-non-lit-copies-
  ;;          (implies (and (aignet-copies-below-n-in-bounds n litarr aignet)
  ;;                        (<= (nfix m) (nfix n)))
  ;;                   (aignet-copies-below-n-in-bounds m litarr aignet))
  ;;          :hints(("Goal" :in-theory (enable aignet-copies-below-n-in-bounds)))))

  (local (defthm aignet-non-lit-copies-in-bounds-of-extension
           (implies (and (aignet-extension-binding)
                         (aignet-non-lit-copies-in-bounds lits litarr orig))
                    (aignet-non-lit-copies-in-bounds lits litarr new))
           :hints(("Goal" :expand ((aignet-non-lit-copies-in-bounds lits litarr new))))))

  (defret litarr-aignet-copies-in-bounds-of-<fn>
    (implies (and (aignet-non-lit-copies-in-bounds lits litarr aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-copies-in-bounds new-litarr new-aignet2))
    :hints (("goal" :induct <call>
             ;; :in-theory (enable aignet-copies-below-n-in-bounds)
             :expand <call>)))


  (defret litarr-non-vars-preserved-of-<fn>
    (implies (not (member-equal (nfix k) (lit-list-vars lits)))
             (equal (nth-lit k new-litarr) (nth-lit k litarr)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable lit-list-vars))))


  (defret aignet-extension-p-of-<fn>
    (aignet-extension-p new-aignet2 aignet2)
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (defret litarr-aignet-lit-copies-in-bounds-of-<fn>
    (implies (and (no-duplicatesp-equal (lit-list-vars lits))
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-lit-copies-in-bounds lits new-litarr new-aignet2))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet-lit-copies-in-bounds
                                lit-list-vars)
             ;; :in-theory (enable aignet-copies-below-n-in-bounds)
             :expand <call>)))

  ;; (defret litarr-aignet-idp-of-copies-in-bounds-of-<fn>
  ;;   (implies (and (aignet-non-lit-copies-in-bounds lits litarr aignet2)
  ;;                 (aignet-marked-copies-in-bounds copy mark aignet2)
  ;;                 (aignet-input-copies-in-bounds copy aignet aignet2))
  ;;            (aignet-non-lit-copies-in-bounds lits new-litarr new-aignet2))
  ;;   :hints (("goal" :induct <call>
  ;;            ;; :in-theory (enable aignet-copies-below-n-in-bounds)
  ;;            :expand <call>)))


  (defret member-lit-aignet-litp-of-<fn>
    (implies (and (member-equal (nfix k) (lit-list-vars lits))
                  (aignet-non-lit-copies-in-bounds lits litarr aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-litp (nth-lit k new-litarr) new-aignet2))
    :hints (("goal" :induct <call>
             :in-theory (enable lit-list-vars)
             :expand (<call>))
            '(:use ((:instance litarr-aignet-copies-in-bounds-of-<fn>))
              :in-theory (e/d (lit-list-vars)
                              (litarr-aignet-copies-in-bounds-of-<fn>)))))

  (local
   (defthm <=-fanin-count-when-aignet-litp
     (implies (aignet-litp lit aignet)
              (<= (lit->var lit) (fanin-count aignet)))
     :hints(("Goal" :in-theory (enable aignet-idp)))))


  (defret litarr-bfr-p-of-<fn>
    (implies (and (member-equal (lit->var
                                 (fgl::bfr->aignet-lit bfr))
                                (lit-list-vars lits))
                  (aignet-non-lit-copies-in-bounds lits litarr aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (equal bfrstate (fgl::bfrstate (fgl::bfrmode :aignet) (fanin-count new-aignet2))))
             (fgl::bfr-p (fgl::bfr-map bfr new-litarr) bfrstate))
    :hints(("Goal" :in-theory (e/d (fgl::bfr-p
                                      fgl::bfr-markedp
                                      fgl::bfr-map)
                                   (<fn> aignet-idp)))))





  (local (include-book "std/lists/nth" :dir :system))

  (defret eval-lit-member-<fn>
    (implies (and (member-equal (nfix k) (lit-list-vars lits))
                  (no-duplicatesp-equal (lit-list-vars lits))
                  (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (equal (lit-eval (nth-lit k new-litarr) invals regvals new-aignet2)
                    (lit-eval (nth-lit k litarr)
                              (input-copy-values 0 invals regvals aignet copy aignet2)
                              (reg-copy-values 0 invals regvals aignet copy aignet2)
                              aignet)))
    :hints (("goal" :induct <call>
             :in-theory (enable* arith-equiv-forwarding
                                 lit-list-vars)
             :expand (<call>))))

  (defret eval-lit-copy-member-of-<fn>
    (implies (and (member-equal (lit->var lit) (lit-list-vars lits))
                  (no-duplicatesp-equal (lit-list-vars lits))
                  (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (equal (lit-eval (lit-copy lit new-litarr) invals regvals new-aignet2)
                    (b-xor (lit->neg lit)
                           (lit-eval (nth-lit (lit->var lit) litarr)
                                     (input-copy-values 0 invals regvals aignet copy aignet2)
                                     (reg-copy-values 0 invals regvals aignet copy aignet2)
                                     aignet))))
    :hints(("Goal" :in-theory (enable lit-copy lit-list-vars))))

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
             :expand (<call>))))

  (defret copy-lit-0-of-<fn>
    (implies (equal (nth-lit 0 copy) 0)
             (equal (nth-lit 0 new-copy) 0))
    :hints (("goal" :induct <call>
             :in-theory (enable aignet::lit-copy)
             :expand (<call>))))

  (defret dfs-copy-onto-invar-of-<fn>
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (dfs-copy-onto-invar aignet new-mark new-copy new-aignet2))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (defret input-copy-values-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (equal (input-copy-values k invals regvals aignet new-copy new-aignet2)
                    (input-copy-values k invals regvals aignet copy aignet2)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (defret reg-copy-values-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (equal (reg-copy-values k invals regvals aignet new-copy new-aignet2)
                    (reg-copy-values k invals regvals aignet copy aignet2)))
    :hints (("goal" :induct <call>
             :expand (<call>)))))

(defthm bfr-bitarr-p-when-aignet-copies-in-bounds
  (implies (aignet::aignet-copies-in-bounds litarr aignet)
           (bfr-litarr-p bfrs litarr (aignet::fanin-count aignet)))
  :hints(("Goal" :in-theory (enable bfr-litarr-p bfr-p bfr-map))))

(defthm bfr-bitarr-p-when-aignet-lit-copies-in-bounds
  (implies (and (aignet::aignet-lit-copies-in-bounds bfrs litarr aignet)
                (aignet::lit-listp bfrs))
           (bfr-litarr-p bfrs litarr (aignet::fanin-count aignet)))
  :hints(("Goal" :in-theory (enable bfr-litarr-p bfr-p bfr-map
                                    aignet::aignet-lit-copies-in-bounds
                                    aignet::aignet-idp))))


(local
 #!aignet
 (defthm aignet-lit-listp-by-lits-max-id-val
   (implies (< (lits-max-id-val lits) (num-fanins aignet))
            (aignet-lit-listp lits aignet))
   :hints(("Goal" :in-theory (enable lits-max-id-val aignet-idp)))))

(local
 #!aignet
 (defthm lits-max-id-val-by-aignet-lit-listp
   (implies (aignet-lit-listp lits aignet)
            (< (lits-max-id-val lits) (+ 1 (fanin-count aignet))))
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
   (b* (((mv ?new-aignet ?new-litarr ?new-copy ?new-state)
         (aignet-simplify-marked-with-tracking
          aignet bitarr mark assum-lits lits
          (acl2::repeat m 0)
          (acl2::repeat m 0)
          config state)))
     (and (aignet-copies-above-n-in-bounds
           n new-litarr new-aignet)
          (aignet-copies-above-n-in-bounds
           n new-copy new-aignet)))
   :hints (("goal" :in-theory (enable in-bounds-by-aignet-copies-above-n-in-bounds-witness)))))

(local
 #!aignet
 (defthm aignet-copies-in-bounds-of-aignet-simplify-marked-with-tracking
   (b* (((mv ?new-aignet ?new-litarr ?new-copy ?new-state)
         (aignet-simplify-marked-with-tracking
          aignet bitarr mark assum-lits lits
          (acl2::repeat m 0)
          (acl2::repeat m 0)
          config state)))
     (and (aignet-copies-in-bounds
           new-litarr new-aignet)
          (aignet-copies-in-bounds
           new-copy new-aignet)))
   :hints (("goal" :in-theory (enable aignet-copies-in-bounds)))))

(local
 #!aignet
 (defthm aignet-marked-copies-in-bounds-of-repeat-0
   (aignet-marked-copies-in-bounds copy (acl2::repeat n 0) aignet)
   :hints(("Goal" :in-theory (enable aignet-marked-copies-in-bounds)))))

(local (in-theory (disable resize-list)))

(local (in-theory (disable w)))


;; (local
;;  (defsection hons-union-duplicate-free
;;    (local
;;     (progn
;;       (defun hons-union1-duplicate-free-lemma-ind (x y z)
;;         (if (atom x)
;;             (list y z)
;;           (if (member-equal (car x) y)
;;               (hons-union1-duplicate-free-lemma-ind (cdr x) y z)
;;             (hons-union1-duplicate-free-lemma-ind (cdr x) y (cons (car x) z)))))
;;       (defthm hons-assoc-equal-of-hons-put-list
;;         (iff (hons-assoc-equal k (acl2::hons-put-list keys vals l))
;;              (or (member-equal k keys)
;;                  (hons-assoc-equal k l))))
;;       (defthm hons-union1-duplicate-free-lemma
;;         (implies (and (no-duplicatesp-equal y)
;;                       (no-duplicatesp-equal x)
;;                       (no-duplicatesp-equal z)
;;                       (not (intersectp-equal x z))
;;                       (not (intersectp-equal y z))
;;                       (not (consp atom)))
;;                  (no-duplicatesp-equal
;;                   (acl2::hons-union1 x (acl2::hons-put-list y vals atom)
;;                                      (append z y))))
;;         :hints (("goal" :induct (hons-union1-duplicate-free-lemma-ind x y z))))

;;       (defthm hons-union1-duplicate-free
;;         (implies (and (no-duplicatesp-equal y)
;;                       (no-duplicatesp-equal x)
;;                       (not (consp atom)))
;;                  (no-duplicatesp-equal
;;                   (acl2::hons-union1 x (acl2::hons-put-list y vals atom)
;;                                      y)))
;;         :hints (("goal" :use ((:instance hons-union1-duplicate-free-lemma (z nil))))))

;;       (defthm hons-union2-duplicate-free-lemma
;;         (implies (and (no-duplicatesp-equal y)
;;                       (no-duplicatesp-equal x)
;;                       (no-duplicatesp-equal z)
;;                       (not (intersectp-equal x z))
;;                       (not (intersectp-equal y z)))
;;                  (no-duplicatesp-equal
;;                   (acl2::hons-union2 x y (append z y))))
;;         :hints (("goal" :induct (hons-union1-duplicate-free-lemma-ind x y z))))

;;       (defthm hons-union2-duplicate-free
;;         (implies (and (no-duplicatesp-equal y)
;;                       (no-duplicatesp-equal x))
;;                  (no-duplicatesp-equal
;;                   (acl2::hons-union2 x y y)))
;;         :hints (("goal" :use ((:instance hons-union2-duplicate-free-lemma (z nil))))))))

;;    (defthm hons-union-duplicate-free
;;      (implies (and (no-duplicatesp-equal x)
;;                    (no-duplicatesp-equal y))
;;               (no-duplicatesp-equal (acl2::hons-union x y)))
;;      :hints(("Goal" :in-theory (enable acl2::hons-union)
;;              :do-not-induct t)))))

#!aignet
(defstobj-clone aignet-pathcond2 aignet-pathcond :suffix "2")


#!aignet
(fty::deffixtype aignet-pathcond2 :pred nbalistp :fix nbalist-fix :equiv nbalist-equiv)
#!aignet
(fty::deffixtype aignet-pathcond :pred nbalistp :fix nbalist-fix :equiv nbalist-equiv)
#!aignet
(fty::deffixtype fgl::aignet-pathcond :pred nbalistp :fix nbalist-fix :equiv nbalist-equiv)

#!aignet
(defsection duplicate-vars-of-nbalist-to-cube
  (defthm member-vars-of-nbalist-to-cube
    (implies (not (nbalist-boundp var nbalist))
             (not (member var
                          (lit-list-vars (nbalist-to-cube nbalist)))))
    :hints(("Goal" :in-theory (enable nbalist-to-cube nbalist-boundp-redef lit-list-vars))))

  (defthm nbalist-fix-when-atom
    (implies (not (consp x))
             (equal (nbalist-fix x) nil))
    :hints(("Goal" :in-theory (enable nbalist-fix))))

  (defthm duplicate-vars-of-nbalist-to-cube
    (no-duplicatesp-equal
     (lit-list-vars (nbalist-to-cube nbalist)))
    :hints(("Goal" :in-theory (enable nbalist-to-cube lit-list-vars (:i len))
            :induct (len nbalist)
            :expand ((nbalist-to-cube nbalist))))))

#!aignet
(define aignet-pathcond-union-cubes ((n natp) aignet-pathcond aignet-pathcond2)
  :returns (mv contra (cube lit-listp))
  :guard (<= n (aignet-pathcond-len aignet-pathcond))
  :measure (nfix (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
  :verify-guards nil
  :prepwork
  ((local (defthm natp-car-nth-when-nbalistp
         (implies (and (nbalistp x)
                       (< (nfix n) (len x)))
                  (natp (car (nth n x))))
         :hints(("Goal" :in-theory (enable nbalistp)))))
   (local (defthm bitp-cdr-nth-when-nbalistp
            (implies (and (nbalistp x)
                          (< (nfix n) (len x)))
                     (and (bitp (cdr (nth n x)))
                          (cdr (nth n x))))
            :hints(("Goal" :in-theory (enable nbalistp)))))
   (local (defthmd hons-assoc-equal-when-nbalistp
            (implies (and (nbalistp x)
                          (cdr (hons-assoc-equal k x)))
                     (bitp (cdr (hons-assoc-equal k x))))
            :hints(("Goal" :in-theory (enable nbalistp hons-assoc-equal)))))
   (local (defthm nbalist-lookup-of-car-nth
            (implies (and (nbalistp x)
                          (< (nfix n) (len x)))
                     (equal (cdr (nth n x))
                            (nbalist-lookup (car (nth n x)) x)))
            :hints(("Goal" :in-theory (enable nbalistp nth nbalist-lookup-redef)
                    :induct (nth n x))
                   (and stable-under-simplificationp
                        '(:use ((:instance bitp-cdr-nth-when-nbalistp
                                 (n (1- n)) (x (cdr x))))
                          :in-theory (disable bitp-cdr-nth-when-nbalistp))))))
   (local (defthm nbalist-lookup-of-car-nth-exists
            (implies (< (nfix n) (len (nbalist-fix x)))
                     (nbalist-boundp (car (nth n (nbalist-fix x))) x))
            :hints (("goal" :use ((:instance nbalist-lookup-of-car-nth
                                   (x (nbalist-fix x)))
                                  (:instance bitp-cdr-nth-when-nbalistp
                                   (x (nbalist-fix x))))
                     :in-theory (disable nbalist-lookup-of-car-nth
                                         bitp-cdr-nth-when-nbalistp)))))

   (local (defthm nbalist-lookup-of-car-nth-when-nbalistp
            (implies (and (nbalistp x)
                          (< (nfix n) (len x)))
                     (nbalist-boundp (car (nth n x)) x))
            :hints (("goal" :use ((:instance nbalist-lookup-of-car-nth-exists))))))

   (local (in-theory (disable nth))))
  (b* (((when (mbe :logic (zp (- (aignet-pathcond-len aignet-pathcond) (nfix n)))
                   :exec (eql (aignet-pathcond-len aignet-pathcond) n)))
        (mv nil (nbalist-to-cube (aignet-pathcond->nbalist aignet-pathcond2))))
       (key (aignet-pathcond-nthkey n aignet-pathcond))
       (val1 (aignet-pathcond-lookup key aignet-pathcond))
       (val2 (aignet-pathcond-lookup key aignet-pathcond2))
       ((when val2)
        (if (eql val1 val2)
            (aignet-pathcond-union-cubes (1+ (lnfix n)) aignet-pathcond aignet-pathcond2)
          (mv t nil)))
       ((mv contra rest)
        (aignet-pathcond-union-cubes (1+ (lnfix n)) aignet-pathcond aignet-pathcond2))
       ((when contra) (mv t nil)))
    (mv nil (cons (make-lit key (b-not val1)) rest)))
  ///
  (verify-guards aignet-pathcond-union-cubes
    :hints (("goal" :do-not-induct t)))

  (local (in-theory (disable AIGNET-PATHCOND-EVAL-IN-TERMS-OF-NBALIST-TO-CUBE)))

  (local (defthm nbalistp-of-nthcdr
           (implies (nbalistp x)
                    (nbalistp (nthcdr n x)))
           :hints(("Goal" :in-theory (enable nbalistp nthcdr)))))
  (local (include-book "std/lists/nthcdr" :dir :system))

  (local (defthm lit-eval-of-make-lit
           (equal (lit-eval (make-lit id neg) invals regvals aignet)
                  (b-xor (id-eval id invals regvals aignet) neg))
           :hints(("Goal" :in-theory (enable lit-eval)))))

  (local (defthm nbalist-lookup-when-not-equal-1
           (implies (and (not (equal 1 (nbalist-lookup k x)))
                         (nbalist-lookup k x))
                    (equal (nbalist-lookup k x) 0))))

  (defret eval-of-<fn>
    (implies (not contra)
             (equal (aignet-eval-conjunction cube invals regvals aignet)
                    (bool->bit (and (aignet-pathcond-eval
                                     aignet (nthcdr n (nbalist-fix aignet-pathcond)) invals regvals)
                                    (aignet-pathcond-eval
                                     aignet aignet-pathcond2 invals regvals)))))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction)
            :expand ((:with aignet-pathcond-eval-redef
                      (aignet-pathcond-eval aignet (nthcdr n (nbalist-fix aignet-pathcond)) invals regvals)))
            :induct <call> :do-not-induct t)
           ;; (and stable-under-simplificationp
           ;;      '(:cases ((nbalist-boundp (car (nth n (nbalist-fix aignet-pathcond))) aignet-pathcond2))))
           ))

  (defretd contra-of-<fn>
    (implies (and (aignet-pathcond-eval
                   aignet (nthcdr n (nbalist-fix aignet-pathcond)) invals regvals)
                  (aignet-pathcond-eval
                   aignet aignet-pathcond2 invals regvals))
             (not contra))
    :hints(("Goal" ;; :in-theory (enable aignet-pathcond-eval-redef)
            :expand ((:with aignet-pathcond-eval-redef
                      (aignet-pathcond-eval aignet (nthcdr n (nbalist-fix aignet-pathcond)) invals regvals)))
            :induct <call>)))

  (defretd contra-of-<fn>-top
    :pre-bind ((n 0))
    (implies (and (aignet-pathcond-eval
                   aignet aignet-pathcond invals regvals)
                  (aignet-pathcond-eval
                   aignet aignet-pathcond2 invals regvals))
             (not contra))
    :hints(("Goal" :in-theory (e/d () (<fn>))
            :use ((:instance contra-of-<fn> (n 0))))))

  (local (defthmd <-plus-1-when-natp
           (implies (and (natp x) (natp y))
                    (equal (< x (+ 1 y))
                           (<= x y)))))


  (defret aignet-lit-listp-of-<fn>
    (implies (and (bounded-pathcond-p (nthcdr n (nbalist-fix aignet-pathcond)) (num-fanins aignet))
                  (bounded-pathcond-p aignet-pathcond2 (num-fanins aignet)))
             (aignet-lit-listp cube aignet))
    :hints(("Goal" :in-theory (e/d (aignet-idp <-plus-1-when-natp)
                                   (nth))
            :expand ((:with bounded-pathcond-p-redef
                      (:free (num-fanins)
                       (bounded-pathcond-p (nthcdr n (nbalist-fix aignet-pathcond)) num-fanins)))))))

  (defret lits-max-id-val-of-<fn>
    (implies (and (bounded-pathcond-p (nthcdr n (nbalist-fix aignet-pathcond)) bound)
                  (bounded-pathcond-p aignet-pathcond2 bound)
                  (posp bound))
             (< (lits-max-id-val cube) bound))
    :hints(("Goal" :in-theory (e/d (lits-max-id-val <-plus-1-when-natp)
                                   (nth))
            :expand ((:with bounded-pathcond-p-redef
                      (:free (num-fanins)
                       (bounded-pathcond-p (nthcdr n (nbalist-fix aignet-pathcond)) num-fanins)))))))

  (defret member-vars-of-<fn>
    (implies (and (not (nbalist-boundp var (nthcdr n (nbalist-fix aignet-pathcond))))
                  (not (nbalist-boundp var aignet-pathcond2)))
             (not (member-equal var (lit-list-vars cube))))
    :hints(("Goal" :in-theory (enable lit-list-vars)
            :induct <call>
            :expand ((:with nbalist-boundp-redef
                      (:free (var) (nbalist-boundp var (nthcdr n (nbalist-fix aignet-pathcond)))))))))


  (defthm hons-assoc-equal-car-nth-of-nthcdr
    (implies (and (nbalistp x)
                  (< (nfix n) (len x)))
             (not (hons-assoc-equal (car (nth n x)) (nthcdr (+ 1 (nfix n)) x))))
    :hints (("goal" :induct (nth n x)
             :in-theory (enable nth nbalistp))))

  (defthm nbalist-boundp-car-nth-in-nthcdr
    (implies (and (< (nfix n) (len x))
                  (nbalistp x))
             (not (nbalist-boundp (car (nth n x))
                                  (nthcdr (+ 1 (nfix n)) x))))
    :hints(("Goal" :in-theory (enable nbalist-boundp nth))))


  (defret duplicate-vars-of-<fn>
    (no-duplicatesp-equal
     (lit-list-vars cube))
    :hints(("Goal" :in-theory (e/d (lit-list-vars)
                                   (nthcdr)))))


  (local (defthm member-make-lit-of-nbalist-to-cube
           (implies (and (nbalist-boundp var aignet-pathcond)
                         (equal (nbalist-lookup var aignet-pathcond) (b-not neg)))
                    (member-equal (make-lit var neg) (nbalist-to-cube aignet-pathcond)))
           :hints(("Goal" :in-theory (enable nbalist-to-cube
                                             nbalist-boundp-redef
                                             nbalist-lookup-redef
                                             satlink::equal-of-make-lit)
                   :induct t
                   :do-not-induct t))))


  (local (defret member-make-lit-of-<fn>-2
           (implies (and (nbalist-boundp var aignet-pathcond2)
                         (equal (nbalist-lookup var aignet-pathcond2) (b-not neg))
                         (not contra))
                    (member-equal (satlink::make-lit var neg) cube))))

  (local (defret member-make-lit-of-<fn>-1
           (implies (and (nbalist-boundp var (nthcdr n (nbalist-fix aignet-pathcond)))
                         (equal (nbalist-lookup var (nthcdr n (nbalist-fix aignet-pathcond))) (b-not neg))
                         (not contra))
                    (member-equal (satlink::make-lit var neg) cube))
    :hints(("Goal"
            :in-theory (e/d (satlink::equal-of-make-lit)
                            (nth (:d <fn>) nthcdr
                                 nbalist-lookup-when-not-equal-1
                                 nbalist-lookup-when-not-boundp
                                 acl2::nfix-equal-to-nonzero))
            :induct <call>
            :expand (<call>
                     (:free (n x) (nthcdr (+ 1 n) x))
                     (:with nbalist-boundp-redef
                      (:free (var) (nbalist-boundp var (nthcdr n (nbalist-fix aignet-pathcond)))))
                     (:with nbalist-lookup-redef
                      (:free (var) (nbalist-lookup var (nthcdr n (nbalist-fix aignet-pathcond))))))))))

  (defret nbalist-to-cube-subsetp-of-<fn>-lemma
    (implies (not contra)
             (subsetp-equal (aignet::nbalist-to-cube (nthcdr n (nbalist-fix aignet-pathcond)))
                            cube))
    :hints(("Goal" :in-theory (e/d (aignet::nbalist-to-cube)
                                   (aignet::nbalist-to-cube-of-nthcdr))
            :induct <call>
            :expand (<call>
                     (aignet::nbalist-to-cube (nthcdr n (nbalist-fix aignet-pathcond)))))))


  (defret nbalist-to-cube-subsetp-of-<fn>-1
    :pre-bind ((n 0))
    (implies (not contra)
             (subsetp-equal (aignet::nbalist-to-cube aignet-pathcond)
                            cube))
    :hints (("goal" :use ((:instance nbalist-to-cube-subsetp-of-<fn>-lemma
                           (n 0))))))

  (defret nbalist-to-cube-subsetp-of-<fn>-2
    (implies (not contra)
             (subsetp-equal (aignet::nbalist-to-cube aignet-pathcond2)
                            cube))
    :hints(("Goal" :in-theory (e/d (aignet::nbalist-to-cube)
                                   (aignet::nbalist-to-cube-of-nthcdr))
            :induct <call>
            :expand (<call>
                     (aignet::nbalist-to-cube (nthcdr n (nbalist-fix aignet-pathcond))))))))



(defstobj-clone litarr2 litarr :suffix "2")


(local #!satlink
       (fty::deflist lit-list :pred lit-listp :elt-type litp :true-listp t
         :parents (litp)
         :short "List of literals"))

;; (local
;;  (defthm true-listp-of-hons-union2
;;    (implies (true-listp z)
;;             (true-listp (acl2::hons-union2 x y z)))))

;; (local
;;  (defthm true-listp-of-hons-union1
;;    (implies (true-listp z)
;;             (true-listp (acl2::hons-union1 x y z)))))

;; (local
;;  (defthm true-listp-of-hons-union
;;    (implies (and (true-listp x) (true-listp y))
;;             (true-listp (acl2::hons-union x y)))
;;    :hints(("Goal" :in-theory (enable acl2::hons-union)))))

;; (local
;;  #!satlink
;;  (defthmd lit-listp-when-set-equiv
;;    (implies (and (acl2::set-equiv y (double-rewrite x))
;;                  (syntaxp (not (equal y x)))
;;                  (true-listp x)
;;                  (true-listp y))
;;             (equal (lit-listp x) (lit-listp y)))))

;; (local
;;  #!satlink
;;  (defthm lit-listp-of-hons-union
;;    (implies (and (lit-listp x)
;;                  (lit-listp y))
;;             (lit-listp (acl2::hons-union x y)))
;;    :hints (("goal" :in-theory (enable lit-listp-when-set-equiv)))))


(local
 #!aignet
 (defthm aignet-copies-above-n-in-bounds-when-aignet-copies-in-bounds
   (implies (aignet-copies-in-bounds copy aignet)
            (aignet-copies-above-n-in-bounds n copy aignet))
   :hints(("Goal" :in-theory (enable aignet-copies-above-n-in-bounds)))))

(local
 #!aignet
 (defthm aignet-lit-listp-of-aignet-fanins
   (equal (aignet-lit-listp lits (aignet-fanins aignet))
          (aignet-lit-listp lits aignet))))





(local
 #!aignet
 (defthm aignet-lit-copies-in-bounds-when-copies-in-bounds
   (implies (aignet-copies-in-bounds copy aignet)
            (aignet-lit-copies-in-bounds lits copy aignet))
   :hints(("Goal" :in-theory (enable aignet-lit-copies-in-bounds)))))



(define combine-pathcond-lits (use-pathcond
                               pathcond
                               use-constraint
                               constraint-pathcond)
  :returns (mv contra (assum-lits aignet::lit-listp))
  (if (and use-pathcond (pathcond-enabledp pathcond))
      (stobj-let ((aignet-pathcond (pathcond-aignet pathcond)))
                 (contra assum-lits)
                 (cond ((aignet-pathcond-lookup 0 aignet-pathcond) (mv t nil))
                       ((and use-constraint (pathcond-enabledp constraint-pathcond))
                        (stobj-let ((aignet::aignet-pathcond2 (pathcond-aignet constraint-pathcond)))
                                   (contra assum-lits)
                                   (if (aignet-pathcond-lookup 0 aignet::aignet-pathcond2)
                                       (mv t nil)
                                     (aignet::aignet-pathcond-union-cubes
                                      0 aignet::aignet-pathcond2 aignet-pathcond))
                                   (mv contra assum-lits)))
                       (t (mv nil (aignet::nbalist-to-cube
                                   (aignet::aignet-pathcond->nbalist aignet-pathcond)))))
                 (mv contra assum-lits))
    (if (and use-constraint (pathcond-enabledp constraint-pathcond))
        (stobj-let ((aignet-pathcond (pathcond-aignet constraint-pathcond)))
                   (contra assum-lits)
                   (if (aignet-pathcond-lookup 0 aignet-pathcond)
                       (mv t nil)
                     (mv nil (aignet::nbalist-to-cube
                              (aignet::aignet-pathcond->nbalist aignet-pathcond))))
                   (mv contra assum-lits))
      (mv nil nil)))
  ///



  (defretd contra-of-<fn>
    (implies (and (logicman-pathcond-eval env pathcond)
                  (logicman-pathcond-eval env constraint-pathcond)
                  (lbfr-mode-is :aignet))
             (not contra))
    :hints(("Goal" :in-theory (e/d (logicman-pathcond-eval
                                    aignet::contra-of-aignet-pathcond-union-cubes-top)
                                   (aignet::aignet-pathcond-eval-in-terms-of-nbalist-to-cube)))))

  (defret eval-of-<fn>
    (implies (and (logicman-pathcond-eval env pathcond)
                  (logicman-pathcond-eval env constraint-pathcond)
                  (lbfr-mode-is :aignet)
                  (equal pi-count (bfr-nvars logicman)))
             (equal (aignet::aignet-eval-conjunction
                     assum-lits
                     (alist-to-bitarr pi-count env nil) nil (logicman->aignet logicman))
                    1))
    :hints(("Goal" :in-theory (e/d (logicman-pathcond-eval bfr-nvars)
                                   (aignet::aignet-pathcond-eval-in-terms-of-nbalist-to-cube))
            :use contra-of-<fn>
            :expand ((:free (aignet invals regvals)
                      (aignet::aignet-eval-conjunction nil invals regvals aignet))))))

  (local (defthmd <=-when-<-plus-1
           (implies (and (integerp bound) (integerp x)
                         (< x (+ 1 bound)))
                    (<= x bound))))

  (defret lits-max-id-val-of-<fn>
    (implies (and (bfr-pathcond-p pathcond (bfrstate (bfrmode :aignet) bound))
                  (bfr-pathcond-p constraint-pathcond (bfrstate (bfrmode :aignet) bound))
                  (natp bound))
             (<= (aignet::lits-max-id-val assum-lits) bound))
    :hints(("Goal" :in-theory (enable bfr-pathcond-p aignet::lits-max-id-val
                                      <=-when-<-plus-1))))

  (defret aignet-lit-listp-of-<fn>
    (implies (and (bfr-pathcond-p pathcond (logicman->bfrstate))
                  (bfr-pathcond-p constraint-pathcond (logicman->bfrstate))
                  (lbfr-mode-is :aignet))
             (aignet::aignet-lit-listp assum-lits (logicman->aignet logicman)))
    :hints(("Goal" :in-theory (enable bfr-pathcond-p))))

  (defret no-duplicate-vars-of-<fn>
    (no-duplicatesp-equal (aignet::lit-list-vars assum-lits)))

  (local (defthm bfr-listp-when-lits-max-id-val
           (implies (and (<= (aignet::lits-max-id-val lits) (bfrstate->bound bfrstate))
                         (not (member 0 (aignet::lit-list-vars lits)))
                         (satlink::lit-listp lits)
                         (bfrstate-mode-is :aignet))
                    (bfr-listp lits bfrstate))
           :hints(("Goal" :in-theory (enable bfr-listp aignet::lits-max-id-val aignet::lit-list-vars
                                             bfr-p)))))


  (local (fty::deffixequiv bfr-pathcond-p))

  (defret member-0-of-<fn>-vars
    (not (member-equal 0 (aignet::lit-list-vars assum-lits))))

  (defret bfr-listp-of-<fn>
    (implies (and (bfr-pathcond-p pathcond bfrstate)
                  (bfr-pathcond-p constraint-pathcond bfrstate)
                  (bfrstate-mode-is :aignet))
             (bfr-listp assum-lits bfrstate))
    :hints (("Goal" :use ((:instance lits-max-id-val-of-<fn>
                           (bound (bfrstate->bound bfrstate)))
                          (:instance bfrstate-fix-redef
                           (x bfrstate)))
             :in-theory (disable lits-max-id-val-of-<fn> <fn>)))))


(local
 #!aignet
 (defthm lits-max-id-val-<=-fanin-count
   (iff (< (fanin-count aignet) (lits-max-id-val x))
        (not (aignet-lit-listp x aignet)))
   :hints(("Goal" :in-theory (enable lits-max-id-val aignet-lit-listp aignet-idp)))))


(local
 #!aignet
 (defsection lit-eval-list-of-aignet-simplify-with-tracking
   (defthm len-of-lit-eval-list
     (equal (len (lit-eval-list x invals regvals aignet))
            (len x))
     :hints(("Goal" :in-theory (enable lit-eval-list))))

   (defthm nth-of-lit-eval-list
     (implies (< (nfix n) (len x))
              (equal (nth n (lit-eval-list x invals regvals aignet))
                     (lit-eval (nth n x) invals regvals aignet)))
     :hints(("Goal" :in-theory (enable nth lit-eval-list))))

   (defret lit-eval-list-of-aignet-simplify-with-tracking
     (implies (and (aignet-lit-listp pres-lits aignet)
                   (equal (aignet-eval-conjunction assum-lits invals regvals aignet) 1))
              (equal (lit-eval-list new-pres-lits invals regvals new-aignet)
                     (lit-eval-list pres-lits invals regvals aignet)))
     :fn aignet-simplify-with-tracking
     :hints ((and stable-under-simplificationp
                  (acl2::equal-by-nths-hint))))

   (defthm repeat-0-bit-list-equiv-nil
     (bits-equiv (acl2::repeat n 0) nil)
     :hints(("Goal" :in-theory (enable bits-equiv))))

   (defcong bits-equiv equal (lit-eval-list x invals regvals aignet) 2)
   (defcong bits-equiv equal (lit-eval-list x invals regvals aignet) 3)

   (defthm lit-eval-list-of-aignet-fanins
     (equal (lit-eval-list x invals regvals (aignet-fanins aignet))
            (lit-eval-list x invals regvals aignet)))))



(local (defthm boolean-listp-of-bfr-list-eval
         (boolean-listp (bfr-list-eval x env))
         :hints(("Goal" :in-theory (enable bfr-list-eval)))))

(define fgl-simplify-object-ordered-logicman ((x fgl-object-p
                                                 "Object whose symbolic value will be preserved by the transform.")
                                              (transforms)
                                              &key
                                              ((tracked-obj
                                                fgl-object-p
                                                "Object that is not preserved but whose
                                         bits' formulas are tracked through possibly
                                         non-preserving transforms, for heuristic
                                         use by the transforms")
                                               'nil)
                                              ((assum-lits aignet::lit-listp) 'nil)
                                              ;; (use-pathcond 't)
                                              ;; (use-constraint 'nil)
                                              (logicman 'logicman)
                                              ;; (pathcond 'pathcond)
                                              ;; (constraint-pathcond 'constraint-pathcond)
                                              (state 'state))
  :guard (and (lbfr-mode-is :aignet)
              (lbfr-listp (fgl-object-bfrlist x))
              (lbfr-listp (fgl-object-bfrlist tracked-obj))
              (lbfr-listp assum-lits)
              (no-duplicatesp-equal (aignet::lit-list-vars assum-lits))
              ;; (ec-call (bfr-pathcond-p-fn pathcond (logicman->bfrstate)))
              ;; (ec-call (bfr-pathcond-p-fn constraint-pathcond (logicman->bfrstate)))
              )
  :returns (mv ;; (new-litarr)
               ;; (new-litarr2)
            (new-x fgl-object-p)
            (new-logicman)
            ;; (new-pathcond)
            ;; (new-constraint-pathcond)
            (new-state))
  :guard-hints (("goal" :in-theory (enable logicman->bfrstate
                                           aignet-lit-listp-when-bfr-listp)
                 ;; :expand ((:free (litarr aignet)
                 ;;           (aignet::aignet-copies-above-n-in-bounds
                 ;;            0 (aignet::update-nth-lit 0 0 litarr) aignet)))
                 :do-not-induct t))
  :prepwork ((local (defthmd aignet-lit-listp-when-bfr-listp
                      (implies (and (lbfr-listp lits)
                                    (aignet::lit-listp lits)
                                    (lbfr-mode-is :aignet))
                               (aignet::aignet-lit-listp lits (logicman->aignet logicman)))
                      :hints(("Goal" :in-theory (enable bfr-listp aignet::lit-listp
                                                        bfr-p aignet::aignet-idp))))))
  ;; :guard-debug t
  :hooks nil ;; bozo
  (b* (((acl2::local-stobjs  aignet::mark aignet::copy aignet::aignet2)
        (mv new-x logicman aignet::mark aignet::copy aignet::aignet2 state))
       ;; (size (+ 1 (bfrstate->bound (logicman->bfrstate))))
       ;; (bitarr (resize-bits size bitarr))
       ;; ((mv bitarr seen) (fgl-object-mark-bfrs x bitarr nil))
       (obj-lits (bfrlist->aignet-lits (fgl-object-bfrlist x) (logicman->bfrstate)))
       ;; (- (fast-alist-free seen))
       (track-lits (bfrlist->aignet-lits (fgl-object-bfrlist tracked-obj) (logicman->bfrstate))))
    (stobj-let
     ((aignet (logicman->aignet logicman))
      (strash (logicman->strash logicman)))

     (new-obj strash aignet aignet::mark aignet::copy aignet::aignet2 state)

     (b* ((aignet::aignet2 (aignet::aignet-raw-copy-fanins-top aignet aignet::aignet2))
          ((mv aignet::aignet2 ?new-assums new-obj-lits ?new-track-lits state)
           (aignet::aignet-simplify-with-tracking
            aignet::aignet2 assum-lits obj-lits track-lits transforms state))
          (aignet::copy (resize-lits (aignet::num-fanins aignet::aignet2) aignet::copy))
          (aignet::mark (resize-bits 0 aignet::mark))
          (aignet::mark (resize-bits (aignet::num-fanins aignet::aignet2) aignet::mark))
          (aignet::copy (aignet::aignet-copy-set-ins 0 aignet::aignet2 aignet::copy aignet))
          (aignet::copy (aignet::aignet-copy-set-regs 0 aignet::aignet2 aignet::copy aignet))
          
          ((mv aignet::mark aignet::copy strash aignet)
           (aignet::aignet-copy-dfs-list new-obj-lits aignet::aignet2 aignet::mark aignet::copy strash
                                         (aignet::make-gatesimp) aignet))
          ;;  ;; presumably already the case, but we need to make sure for some
          ;;  ;; dumb reason to do with literal<->bfr conversion
          ;; ;; (litarr (aignet::set-lit 0 0 litarr))
          ;; ((mv litarr2 aignet::mark aignet::copy strash aignet)
          ;;  (aignet::aignet-dfs-copy-back-marked-nodes
          ;;   0 bitarr litarr2 aignet::aignet2 aignet::mark aignet::copy strash (aignet::make-gatesimp) aignet))
          ;; (litarr2 (aignet::set-lit 0 0 litarr2))
          ;; ((mv litarr aignet::mark aignet::copy strash aignet)
          ;;  (aignet::aignet-dfs-copy-back-lits
          ;;   assum-lits litarr aignet::aignet2 aignet::mark aignet::copy strash (aignet::make-gatesimp) aignet))
          ;; (litarr (aignet::set-lit 0 0 litarr))
          (new-new-obj-lits (aignet::lit-list-copies new-obj-lits aignet::copy))
          (new-bfrs (aignet-lits->bfrlist new-new-obj-lits
                                          (bfrstate (bfrmode :aignet) (1- (aignet::num-fanins aignet)))))
          ((mv new-obj ?rest-bfrs) (fgl-object-replace-bfrlist x new-bfrs))
          )
       (mv new-obj strash aignet aignet::mark aignet::copy aignet::aignet2 state))

     (mv new-obj logicman aignet::mark aignet::copy aignet::aignet2 state)))
  ///
  ;; (defret contra-of-<fn>
  ;;   (implies (and (logicman-pathcond-eval env pathcond)
  ;;                 (logicman-pathcond-eval env constraint-pathcond)
  ;;                 (lbfr-mode-is :aignet))
  ;;            (not contra))
  ;;   :hints(("Goal" :in-theory (enable contra-of-combine-pathcond-lits))))

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

  (local (defthm take-of-equal-len
           (implies (equal len (len x))
                    (equal (take len x)
                           (true-list-fix x)))))

  (local (defthm logicman->bfrstate-of-update-logicman->aignet
           (implies (lbfr-mode-is :aignet)
                    (equal (logicman->bfrstate (update-logicman->aignet aignet logicman))
                           (bfrstate (lbfr-mode)
                                     (aignet::fanin-count aignet))))
           :hints(("Goal" :in-theory (enable logicman->bfrstate)))))

  (defret bfr-listp-of-<fn>
    (implies (lbfr-mode-is :aignet)
             (bfr-listp (fgl-object-bfrlist new-x) (logicman->bfrstate new-logicman))))


  (local (defthm logicman-extension-p-of-update-logicman->aignet
           (implies (and (bind-logicman-extension new old)
                         (aignet::aignet-extension-p aignet (logicman->aignet new))
                         (equal (aignet::stype-count :reg aignet)
                                (aignet::stype-count :reg (logicman->aignet new))))
                    (logicman-extension-p (update-logicman->aignet aignet new) old))
           :hints(("Goal" :in-theory (enable logicman-extension-p)))))
  


  (defret eval-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj))
                  (equal (aignet::aignet-eval-conjunction
                          assum-lits
                          (alist-to-bitarr (bfr-nvars logicman)
                                           (fgl-env->bfr-vals env)
                                           nil)
                          nil
                          (logicman->aignet logicman))
                         1))
             (equal (fgl-object-eval new-x env new-logicman)
                    (fgl-object-eval x env logicman)))
    :hints(("Goal" :in-theory (enable bfr-nvars))))


 ;; (defret bfr-litarr-correct-p-litarr2-of-<fn>
 ;;    (implies (and (lbfr-mode-is :aignet)
 ;;                  (lbfr-listp (fgl-object-bfrlist x))
 ;;                  (lbfr-listp (fgl-object-bfrlist tracked-obj))
 ;;                  (equal (aignet::aignet-eval-conjunction
 ;;                          assum-lits
 ;;                          (alist-to-bitarr (bfr-nvars logicman) env nil) nil
 ;;                          (logicman->aignet logicman))
 ;;                         1))
 ;;             (bfr-litarr-correct-p (fgl-object-bfrlist x) env
 ;;                                   new-litarr2 new-logicman logicman))
 ;;    :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-by-witness
 ;;                                    ;; contra-of-combine-pathcond-lits
 ;;                                    ;; bfr-eval bfr-map bfr->aignet-lit bfr-fix aignet-lit->bfr
 ;;                                    logicman->bfrstate
 ;;                                    ;; bfr-eval
 ;;                                    bfr-nvars)
 ;;                                   (aignet::bit-list-fix-of-repeat)))
 ;;           (and stable-under-simplificationp
 ;;                (let ((witness (acl2::find-call-lst 'BFR-LITARR-correct-p-witness clause)))
 ;;                  (and witness
 ;;                       `(:clause-processor
 ;;                         (acl2::simple-generalize-cp
 ;;                          clause
 ;;                          '((,witness . bfr)))))))
 ;;           (and stable-under-simplificationp
 ;;                '(:cases ((equal (satlink::lit->var
 ;;                                  (bfr->aignet-lit bfr (logicman->bfrstate)))
 ;;                                 0))))))




  ;; (local (defthm aignet-copies-in-bounds-of-update-nth-lit
  ;;          (implies (and (aignet-litp lit aignet)
  ;;                        (aignet-copies-in-bounds


  ;; (local (defthm bfr-litarr-p-of-update-nth-lit-0
  ;;          (implies (bfr-litarr-p bfrs litarr bound)
  ;;                   (bfr-litarr-p bfrs (aignet::update-nth-lit n 0 litarr) bound))
  ;;          :hints(("Goal" :in-theory (enable bfr-litarr-p)
  ;;                  :induct t)
  ;;                 (and stable-under-simplificationp
  ;;                      '(:in-theory (enable bfr-map bfr-p aignet::lit-copy))))))



  ;; (defret bfr-litarr-p-litarr2-of-<fn>
  ;;   (implies (and (equal bound (bfrstate->bound (logicman->bfrstate new-logicman)))
  ;;                 (lbfr-mode-is :aignet)
  ;;                 (lbfr-listp (fgl-object-bfrlist x))
  ;;                 (lbfr-listp (fgl-object-bfrlist tracked-obj)))
  ;;            (bfr-litarr-p (fgl-object-bfrlist x) new-litarr2 bound))
  ;;   :hints(("Goal" :in-theory (enable logicman->bfrstate))))

  ;; (defret bfr-litarr-p-litarr-of-<fn>
  ;;   (implies (and (equal bound (bfrstate->bound (logicman->bfrstate new-logicman)))
  ;;                 (lbfr-mode-is :aignet)
  ;;                 ;; (lbfr-listp (fgl-object-bfrlist x))
  ;;                 (no-duplicatesp-equal (aignet::lit-list-vars assum-lits))
  ;;                 (aignet::lit-listp assum-lits))
  ;;            (bfr-litarr-p ;; (mv-nth 1 (combine-pathcond-lits
  ;;                          ;;            use-pathcond pathcond
  ;;                          ;;            use-constraint constraint-pathcond))
  ;;             assum-lits new-litarr bound)))

    ;; :hints(("Goal" :in-theory (enable bfr-litarr-p-by-witness))
    ;;        (and stable-under-simplificationp
    ;;             (let ((witness (acl2::find-call-lst 'BFR-LITARR-P-WITNESS clause)))
    ;;               (and witness
    ;;                    `(:clause-processor
    ;;                      (acl2::simple-generalize-cp
    ;;                       clause
    ;;                       '((,witness . bfr)))))))))

  ;; (local (defthm nth-mark-when-bfr-markedp
  ;;          (implies (and (bfr-markedp bfr bitarr)
  ;;                        (not (equal bfr t))
  ;;                        bfr
  ;;                        (not (equal bfr 0)))
  ;;                   (equal (equal 1 (nth (satlink::lit->var bfr) bitarr))
  ;;                          t))
  ;;          :hints(("Goal" :in-theory (enable bfr-markedp)))))


  ;; (local
  ;;  #!aignet
  ;;  (defthm id-eval-of-var-when-aignet-lit-fix-equal-1
  ;;    (implies (equal (aignet-lit-fix lit aignet) 1)
  ;;             (equal (id-eval (lit->var lit) invals regvals aignet)
  ;;                    (b-not (lit->neg lit))))
  ;;    :hints(("Goal" :in-theory (enable aignet-lit-fix aignet-id-fix
  ;;                                      satlink::equal-of-make-lit)
  ;;            :expand ((id-eval (lit->var lit) invals regvals aignet))))))

  ;; (local
  ;;  #!aignet
  ;;  (defthm id-eval-of-var-when-aignet-lit-fix-equal-0
  ;;    (implies (equal (aignet-lit-fix lit aignet) 0)
  ;;             (equal (id-eval (lit->var lit) invals regvals aignet)
  ;;                    (lit->neg lit)))
  ;;    :hints(("Goal" :in-theory (enable aignet-lit-fix aignet-id-fix
  ;;                                      satlink::equal-of-make-lit)
  ;;            :expand ((id-eval (lit->var lit) invals regvals aignet))))))

  ;; (local
  ;;  #!aignet
  ;;  (defthm lit-eval-when-known-id-eval
  ;;    (implies (and (equal v (id-eval (lit->var lit) invals regvals aignet))
  ;;                  (syntaxp (quotep v)))
  ;;             (equal (lit-eval lit invals regvals aignet)
  ;;                    (b-xor v (lit->neg lit))))
  ;;    :hints (("goal" :expand ((lit-eval lit invals regvals aignet))))))

  ;; (local
  ;;  #!aignet
  ;;  (progn
  ;;    (defthm id-eval-of-repeat-nil-regs
  ;;      (equal (id-eval id invals (acl2::repeat k nil) aignet)
  ;;             (id-eval id invals nil aignet))
  ;;      :hints (("goal" :induct (id-eval-ind id aignet)
  ;;               :expand ((:free (invals regvals)
  ;;                         (id-eval id invals regvals aignet)))
  ;;               :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))))

  ;;    (defthm lit-eval-of-repeat-nil
  ;;      (equal (lit-eval lit invals (acl2::repeat k nil) aignet)
  ;;             (lit-eval lit invals nil aignet))
  ;;      :hints (("goal"
  ;;               :expand ((:free (invals regvals)
  ;;                         (lit-eval lit invals regvals aignet))))))))
  ;; ;; (local
  ;; ;;  #!aignet
  ;; ;;  (defthm lit-eval-when-aignet-lit-fix-equal-0
  ;; ;;    (implies (equal (aignet-lit-fix lit aignet) 0)
  ;; ;;             (equal (lit-eval lit invals regvals aignet)
  ;; ;;                    0))
  ;; ;;    :hints(("Goal" :in-theory (enable aignet-lit-fix aignet-id-fix
  ;; ;;                                      satlink::equal-of-make-lit)
  ;; ;;            :expand ((id-eval (lit->var lit) invals regvals aignet)
  ;; ;;                     (lit-eval lit invals regvals aignet))))))

  ;; (local
  ;;  (defthm bfr-eval-aignet-mode
  ;;    (implies (lbfr-mode-is :aignet)
  ;;             (equal (bfr-eval x env logicman)
  ;;                    (bit->bool (aignet::lit-eval
  ;;                                (bfr->aignet-lit x (logicman->bfrstate))
  ;;                                (alist-to-bitarr (aignet::num-ins (logicman->aignet logicman))
  ;;                                                 env nil)
  ;;                                nil (logicman->aignet logicman)))))
  ;;    :hints(("Goal" :in-theory (enable bfr-eval)))))

  ;; (local (defthm bfr->aignet-lit-of-bfr-map
  ;;          (implies (and (bfr-p (bfr-map bfr litarr) bfrstate2)
  ;;                        (bfrstate-mode-is :aignet bfrstate2)
  ;;                        (bfr-p bfr (bfrstate (bfrmode :aignet) (+ -1 (len litarr))))
  ;;                        ;; (equal (aignet::nth-lit 0 litarr) 0)
  ;;                        ;; (<= 1 (len litarr))
  ;;                        )
  ;;                   (equal (bfr->aignet-lit (bfr-map bfr litarr) bfrstate2)
  ;;                          (cond ((eq bfr t) 1)
  ;;                                ((eq bfr nil) 0)
  ;;                                (t (aignet::lit-copy (bfr->aignet-lit bfr (bfrstate
  ;;                                                                           (bfrmode :aignet)
  ;;                                                                           (+ -1 (len litarr))))
  ;;                                                     litarr)))))
  ;;          :hints(("Goal" :in-theory (enable bfr->aignet-lit bfr-fix bfr-p bfr-map aignet::lit-copy
  ;;                                            satlink::lit-negate-cond
  ;;                                            satlink::equal-of-make-lit
  ;;                                            aignet-lit->bfr
  ;;                                            bounded-lit-fix
  ;;                                            bfr-fix)
  ;;                  :do-not-induct t))))


  ;; (local
  ;;  (defthm nth-equal-1-of-bfr->aignet-lit
  ;;    (implies (and (bfrstate-mode-is :aignet)
  ;;                  (not (equal (satlink::lit->var (bfr->aignet-lit bfr bfrstate)) 0)))
  ;;             (equal (equal (nth (satlink::lit->var (bfr->aignet-lit bfr bfrstate)) bitarr) 1)
  ;;                    (bfr-markedp bfr bitarr)))
  ;;    :hints(("Goal" :in-theory (enable bfr-markedp bfr->aignet-lit bfr-fix aignet-lit->bfr
  ;;                                      bounded-lit-fix)))))

  ;; (local (defthm lit-copy-when-lit->var-equal-0
  ;;          (implies (equal (satlink::lit->var x) 0)
  ;;                   (equal (aignet::lit-copy x copy)
  ;;                          (satlink::lit-negate-cond (aignet::nth-lit 0 copy)
  ;;                                                    (satlink::lit->neg x))))
  ;;          :hints(("Goal" :in-theory (enable aignet::lit-copy)))))

  ;; ;; (local
  ;; ;;  (defthm stype-count-equals-bfr-nvars
  ;; ;;    (equal (equal

  ;; (local
  ;;  #!aignet
  ;;  (defthm lit-copy-of-update-nth-lit-0-0
  ;;          (equal (lit-copy lit (update-nth-lit 0 0 litarr))
  ;;                 (cond ((equal (lit-fix lit) 0) 0)
  ;;                       ((equal (lit-fix lit) 1) 1)
  ;;                       (t (lit-copy lit litarr))))
  ;;          :hints(("Goal" :in-theory (enable lit-copy satlink::lit-negate-cond)))))



  ;; (local (defthm lit->var-0-of-bfr->aignet-lit
  ;;          (implies (and (bfr-p bfr (bfrstate (bfrmode :aignet) bound))
  ;;                        (not (equal bfr t))
  ;;                        bfr)
  ;;                   (not (equal (satlink::lit->var (bfr->aignet-lit bfr (bfrstate (bfrmode :aignet) bound))) 0)))
  ;;          :hints(("Goal" :in-theory (e/d (bfr->aignet-lit bfr-p))
  ;;                  :use ((:instance satlink::equal-of-make-lit
  ;;                         (a 0)
  ;;                         (var (satlink::lit->var bfr))
  ;;                         (neg (satlink::lit->neg bfr)))
  ;;                        (:instance satlink::equal-of-make-lit
  ;;                         (a 1)
  ;;                         (var (satlink::lit->var bfr))
  ;;                         (neg (satlink::lit->neg bfr))))))))


  ;; (local (in-theory (disable acl2::repeat-when-zp nth
  ;;                            default-+-2 default-+-1
  ;;                            aignet::fanin-count-of-atom)))

  ;; (defret bfr-litarr-correct-p-litarr2-of-<fn>
  ;;   (implies (and (lbfr-mode-is :aignet)
  ;;                 (lbfr-listp (fgl-object-bfrlist x))
  ;;                 (lbfr-listp (fgl-object-bfrlist tracked-obj))
  ;;                 (equal (aignet::aignet-eval-conjunction
  ;;                         assum-lits
  ;;                         (alist-to-bitarr (bfr-nvars logicman) env nil) nil
  ;;                         (logicman->aignet logicman))
  ;;                        1))
  ;;            (bfr-litarr-correct-p (fgl-object-bfrlist x) env
  ;;                                  new-litarr2 new-logicman logicman))
  ;;   :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-by-witness
  ;;                                   ;; contra-of-combine-pathcond-lits
  ;;                                   ;; bfr-eval bfr-map bfr->aignet-lit bfr-fix aignet-lit->bfr
  ;;                                   logicman->bfrstate
  ;;                                   ;; bfr-eval
  ;;                                   bfr-nvars)
  ;;                                  (aignet::bit-list-fix-of-repeat)))
  ;;          (and stable-under-simplificationp
  ;;               (let ((witness (acl2::find-call-lst 'BFR-LITARR-correct-p-witness clause)))
  ;;                 (and witness
  ;;                      `(:clause-processor
  ;;                        (acl2::simple-generalize-cp
  ;;                         clause
  ;;                         '((,witness . bfr)))))))
  ;;          (and stable-under-simplificationp
  ;;               '(:cases ((equal (satlink::lit->var
  ;;                                 (bfr->aignet-lit bfr (logicman->bfrstate)))
  ;;                                0))))))




  ;; (local
  ;;  (defthm lit->var-of-bfr->aignet-lit
  ;;    (implies (bfr-p bfr bfrstate)
  ;;             (equal (satlink::lit->var (bfr->aignet-lit bfr bfrstate))
  ;;                    (satlink::lit->var bfr)))
  ;;    :hints(("Goal" :in-theory (enable bfr->aignet-lit)))))

  ;; (local (defthm member-lit->var-of-lit-list-vars
  ;;          (implies (member lit lits)
  ;;                   (member (satlink::lit->var lit) (aignet::lit-list-vars lits)))
  ;;          :hints(("Goal" :in-theory (enable aignet::lit-list-vars)))))

  ;; (defret bfr-litarr-correct-p-litarr-of-<fn>
  ;;   (implies (and (lbfr-mode-is :aignet)
  ;;                 ;; (lbfr-listp (fgl-object-bfrlist x))
  ;;                 (lbfr-listp assum-lits)
  ;;                 (aignet::lit-listp assum-lits)
  ;;                 (no-duplicatesp-equal (aignet::lit-list-vars assum-lits))
  ;;                 ;; (lbfr-listp (fgl-object-bfrlist tracked-obj))
  ;;                 ;; (logicman-pathcond-eval env pathcond)
  ;;                 ;; (logicman-pathcond-eval env constraint-pathcond)
  ;;                 ;; (not contra)
  ;;                 ;; (bfr-pathcond-p pathcond (logicman->bfrstate))
  ;;                 ;; (bfr-pathcond-p constraint-pathcond (logicman->bfrstate))
  ;;                 ;; (equal (aignet::nth-lit 0 litarr) 0)
  ;;                 )
  ;;            (bfr-litarr-correct-p ;; (mv-nth 1 (combine-pathcond-lits
  ;;                                  ;;    use-pathcond pathcond
  ;;                                  ;;    use-constraint constraint-pathcond))
  ;;             assum-lits env new-litarr new-logicman logicman))
  ;;   :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-by-witness
  ;;                                   ;; contra-of-combine-pathcond-lits
  ;;                                   ;; bfr-eval bfr-map bfr->aignet-lit bfr-fix aignet-lit->bfr
  ;;                                   logicman->bfrstate
  ;;                                   bfr-nvars
  ;;                                   aignet-lit-listp-when-bfr-listp)
  ;;                                  (aignet::bit-list-fix-of-repeat)))
  ;;          (and stable-under-simplificationp
  ;;               (let ((witness (acl2::find-call-lst 'BFR-LITARR-correct-p-witness clause)))
  ;;                 (and witness
  ;;                      `(:clause-processor
  ;;                        (acl2::simple-generalize-cp
  ;;                         clause
  ;;                         '((,witness . bfr)))))))
  ;;          (and stable-under-simplificationp
  ;;               '(:cases ((equal (satlink::lit->var
  ;;                                 (bfr->aignet-lit bfr (logicman->bfrstate)))
  ;;                                0))))))

  ;; ;; (defret bfr-litarr-correct-p-all-envs-of-<fn>
  ;; ;;   (implies (and (lbfr-mode-is :aignet)
  ;; ;;                 (lbfr-listp (fgl-object-bfrlist x))
  ;; ;;                 (lbfr-listp (fgl-object-bfrlist tracked-obj))
  ;; ;;                 ;; (equal (aignet::nth-lit 0 litarr) 0)
  ;; ;;                 )
  ;; ;;            (bfr-litarr-correct-p-all-envs (fgl-object-bfrlist x)
  ;; ;;                                  new-litarr new-logicman logicman))
  ;; ;;   :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-all-envs)
  ;; ;;                                  (<fn>)))))

  ;; (defret litarr-len-of-<fn>
  ;;   (implies (and (lbfr-mode-is :aignet)
  ;;                 ;; (lbfr-listp (fgl-object-bfrlist x))
  ;;                 ;; (bfr-pathcond-p pathcond (logicman->bfrstate))
  ;;                 ;; (bfr-pathcond-p constraint-pathcond (logicman->bfrstate))
  ;;                 ;; (lbfr-listp (fgl-object-bfrlist tracked-obj))
  ;;                 (lbfr-listp assum-lits)
  ;;                 (aignet::lit-listp assum-lits)
  ;;                 )
  ;;            (equal (len new-litarr)
  ;;                   (+ 1 (bfrstate->bound (logicman->bfrstate logicman)))))
  ;;   :hints(("Goal" :in-theory (enable logicman->bfrstate
  ;;                                     aignet-lit-listp-when-bfr-listp))))

  ;; (defret litarr2-len-of-<fn>
  ;;   (implies (and (lbfr-mode-is :aignet)
  ;;                 (lbfr-listp (fgl-object-bfrlist x))
  ;;                 (lbfr-listp (fgl-object-bfrlist tracked-obj))
  ;;                 ;; (bfr-pathcond-p pathcond (logicman->bfrstate))
  ;;                 ;; (bfr-pathcond-p constraint-pathcond (logicman->bfrstate))
  ;;                 ;; (lbfr-listp (fgl-object-bfrlist tracked-obj))
  ;;                 )
  ;;            (equal (len new-litarr2)
  ;;                   (+ 1 (bfrstate->bound (logicman->bfrstate logicman)))))
  ;;   :hints(("Goal" :in-theory (enable logicman->bfrstate))))


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






(define fgl-simplify-object-logicman ((x fgl-object-p
                                         "Object whose symbolic value will be preserved by the transform.")
                                      (litarr "Receives the mapping from old to new pathcond literals")
                                      (litarr2 "Receives the mapping from old to new non-pathcond literals")
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
                                      ((assum-lits aignet::lit-listp) 'nil)
                                      ;; (use-pathcond 't)
                                      ;; (use-constraint 'nil)
                                      (logicman 'logicman)
                                      ;; (pathcond 'pathcond)
                                      ;; (constraint-pathcond 'constraint-pathcond)
                                      (state 'state))
  :guard (and (lbfr-mode-is :aignet)
              (lbfr-listp (fgl-object-bfrlist x))
              (lbfr-listp (fgl-object-bfrlist tracked-obj))
              (lbfr-listp (fgl-object-bfrlist tracked-bits))
              (lbfr-listp assum-lits)
              (no-duplicatesp-equal (aignet::lit-list-vars assum-lits))
              ;; (ec-call (bfr-pathcond-p-fn pathcond (logicman->bfrstate)))
              ;; (ec-call (bfr-pathcond-p-fn constraint-pathcond (logicman->bfrstate)))
              )
  :returns (mv (new-litarr)
               (new-litarr2)
               (new-logicman)
               ;; (new-pathcond)
               ;; (new-constraint-pathcond)
               (new-state))
  :guard-hints (("goal" :in-theory (enable logicman->bfrstate
                                           aignet-lit-listp-when-bfr-listp)
                 :expand ((:free (litarr aignet)
                           (aignet::aignet-copies-above-n-in-bounds
                            0 (aignet::update-nth-lit 0 0 litarr) aignet)))
                 :do-not-induct t))
  :prepwork ((local (defthmd aignet-lit-listp-when-bfr-listp
                      (implies (and (lbfr-listp lits)
                                    (aignet::lit-listp lits)
                                    (lbfr-mode-is :aignet))
                               (aignet::aignet-lit-listp lits (logicman->aignet logicman)))
                      :hints(("Goal" :in-theory (enable bfr-listp aignet::lit-listp
                                                        bfr-p aignet::aignet-idp))))))
  ;; :guard-debug t
  :hooks nil ;; bozo
  (b* (((acl2::local-stobjs bitarr  aignet::mark aignet::copy aignet::aignet2)
        (mv litarr litarr2 logicman bitarr aignet::mark aignet::copy aignet::aignet2 state))
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
       (litarr (resize-lits size litarr))
       (litarr2 (resize-lits 0 litarr2))
       (litarr2 (resize-lits size litarr2)))
    (stobj-let
     ((aignet (logicman->aignet logicman))
      (strash (logicman->strash logicman)))

     (strash aignet aignet::mark aignet::copy aignet::aignet2 litarr litarr2 state)

     (b* ((aignet::aignet2 (aignet::aignet-raw-copy-fanins-top aignet aignet::aignet2))
          ((mv aignet::aignet2 litarr litarr2 state)
           (aignet::aignet-simplify-marked-with-tracking
            aignet::aignet2 bitarr aignet::mark assum-lits tracked-lits litarr litarr2 transforms state))
          (aignet::copy (resize-lits (aignet::num-fanins aignet::aignet2) aignet::copy))
          (aignet::mark (resize-bits 0 aignet::mark))
          (aignet::mark (resize-bits (aignet::num-fanins aignet::aignet2) aignet::mark))
          (aignet::copy (aignet::aignet-copy-set-ins 0 aignet::aignet2 aignet::copy aignet))
          (aignet::copy (aignet::aignet-copy-set-regs 0 aignet::aignet2 aignet::copy aignet))
           ;; presumably already the case, but we need to make sure for some
           ;; dumb reason to do with literal<->bfr conversion
          ;; (litarr (aignet::set-lit 0 0 litarr))
          ((mv litarr2 aignet::mark aignet::copy strash aignet)
           (aignet::aignet-dfs-copy-back-marked-nodes
            0 bitarr litarr2 aignet::aignet2 aignet::mark aignet::copy strash (aignet::make-gatesimp) aignet))
          (litarr2 (aignet::set-lit 0 0 litarr2))
          ((mv litarr aignet::mark aignet::copy strash aignet)
           (aignet::aignet-dfs-copy-back-lits
            assum-lits litarr aignet::aignet2 aignet::mark aignet::copy strash (aignet::make-gatesimp) aignet))
          (litarr (aignet::set-lit 0 0 litarr)))
       (mv strash aignet aignet::mark aignet::copy aignet::aignet2 litarr litarr2 state))

     (mv litarr litarr2 logicman bitarr aignet::mark aignet::copy aignet::aignet2 state)))
  ///
  ;; (defret contra-of-<fn>
  ;;   (implies (and (logicman-pathcond-eval env pathcond)
  ;;                 (logicman-pathcond-eval env constraint-pathcond)
  ;;                 (lbfr-mode-is :aignet))
  ;;            (not contra))
  ;;   :hints(("Goal" :in-theory (enable contra-of-combine-pathcond-lits))))

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

  ;; (local (defthm aignet-copies-in-bounds-of-update-nth-lit
  ;;          (implies (and (aignet-litp lit aignet)
  ;;                        (aignet-copies-in-bounds


  (local (defthm bfr-litarr-p-of-update-nth-lit-0
           (implies (bfr-litarr-p bfrs litarr bound)
                    (bfr-litarr-p bfrs (aignet::update-nth-lit n 0 litarr) bound))
           :hints(("Goal" :in-theory (enable bfr-litarr-p)
                   :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable bfr-map bfr-p aignet::lit-copy))))))



  (defret bfr-litarr-p-litarr2-of-<fn>
    (implies (and (equal bound (bfrstate->bound (logicman->bfrstate new-logicman)))
                  (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj)))
             (bfr-litarr-p (fgl-object-bfrlist x) new-litarr2 bound))
    :hints(("Goal" :in-theory (enable logicman->bfrstate))))

  (defret bfr-litarr-p-litarr-of-<fn>
    (implies (and (equal bound (bfrstate->bound (logicman->bfrstate new-logicman)))
                  (lbfr-mode-is :aignet)
                  ;; (lbfr-listp (fgl-object-bfrlist x))
                  (no-duplicatesp-equal (aignet::lit-list-vars assum-lits))
                  (aignet::lit-listp assum-lits))
             (bfr-litarr-p ;; (mv-nth 1 (combine-pathcond-lits
                           ;;            use-pathcond pathcond
                           ;;            use-constraint constraint-pathcond))
              assum-lits new-litarr bound)))

    ;; :hints(("Goal" :in-theory (enable bfr-litarr-p-by-witness))
    ;;        (and stable-under-simplificationp
    ;;             (let ((witness (acl2::find-call-lst 'BFR-LITARR-P-WITNESS clause)))
    ;;               (and witness
    ;;                    `(:clause-processor
    ;;                      (acl2::simple-generalize-cp
    ;;                       clause
    ;;                       '((,witness . bfr)))))))))

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
                         ;; (equal (aignet::nth-lit 0 litarr) 0)
                         ;; (<= 1 (len litarr))
                         )
                    (equal (bfr->aignet-lit (bfr-map bfr litarr) bfrstate2)
                           (cond ((eq bfr t) 1)
                                 ((eq bfr nil) 0)
                                 (t (aignet::lit-copy (bfr->aignet-lit bfr (bfrstate
                                                                            (bfrmode :aignet)
                                                                            (+ -1 (len litarr))))
                                                      litarr)))))
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

  ;; (local
  ;;  (defthm stype-count-equals-bfr-nvars
  ;;    (equal (equal

  (local
   #!aignet
   (defthm lit-copy-of-update-nth-lit-0-0
           (equal (lit-copy lit (update-nth-lit 0 0 litarr))
                  (cond ((equal (lit-fix lit) 0) 0)
                        ((equal (lit-fix lit) 1) 1)
                        (t (lit-copy lit litarr))))
           :hints(("Goal" :in-theory (enable lit-copy satlink::lit-negate-cond)))))



  (local (defthm lit->var-0-of-bfr->aignet-lit
           (implies (and (bfr-p bfr (bfrstate (bfrmode :aignet) bound))
                         (not (equal bfr t))
                         bfr)
                    (not (equal (satlink::lit->var (bfr->aignet-lit bfr (bfrstate (bfrmode :aignet) bound))) 0)))
           :hints(("Goal" :in-theory (e/d (bfr->aignet-lit bfr-p))
                   :use ((:instance satlink::equal-of-make-lit
                          (a 0)
                          (var (satlink::lit->var bfr))
                          (neg (satlink::lit->neg bfr)))
                         (:instance satlink::equal-of-make-lit
                          (a 1)
                          (var (satlink::lit->var bfr))
                          (neg (satlink::lit->neg bfr))))))))


  (local (in-theory (disable acl2::repeat-when-zp nth
                             default-+-2 default-+-1
                             aignet::fanin-count-of-atom)))

  (defret bfr-litarr-correct-p-litarr2-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj))
                  (equal (aignet::aignet-eval-conjunction
                          assum-lits
                          (alist-to-bitarr (bfr-nvars logicman) env nil) nil
                          (logicman->aignet logicman))
                         1))
             (bfr-litarr-correct-p (fgl-object-bfrlist x) env
                                   new-litarr2 new-logicman logicman))
    :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-by-witness
                                    ;; contra-of-combine-pathcond-lits
                                    ;; bfr-eval bfr-map bfr->aignet-lit bfr-fix aignet-lit->bfr
                                    logicman->bfrstate
                                    ;; bfr-eval
                                    bfr-nvars)
                                   (aignet::bit-list-fix-of-repeat)))
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




  (local
   (defthm lit->var-of-bfr->aignet-lit
     (implies (bfr-p bfr bfrstate)
              (equal (satlink::lit->var (bfr->aignet-lit bfr bfrstate))
                     (satlink::lit->var bfr)))
     :hints(("Goal" :in-theory (enable bfr->aignet-lit)))))

  (local (defthm member-lit->var-of-lit-list-vars
           (implies (member lit lits)
                    (member (satlink::lit->var lit) (aignet::lit-list-vars lits)))
           :hints(("Goal" :in-theory (enable aignet::lit-list-vars)))))

  (defret bfr-litarr-correct-p-litarr-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  ;; (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp assum-lits)
                  (aignet::lit-listp assum-lits)
                  (no-duplicatesp-equal (aignet::lit-list-vars assum-lits))
                  ;; (lbfr-listp (fgl-object-bfrlist tracked-obj))
                  ;; (logicman-pathcond-eval env pathcond)
                  ;; (logicman-pathcond-eval env constraint-pathcond)
                  ;; (not contra)
                  ;; (bfr-pathcond-p pathcond (logicman->bfrstate))
                  ;; (bfr-pathcond-p constraint-pathcond (logicman->bfrstate))
                  ;; (equal (aignet::nth-lit 0 litarr) 0)
                  )
             (bfr-litarr-correct-p ;; (mv-nth 1 (combine-pathcond-lits
                                   ;;    use-pathcond pathcond
                                   ;;    use-constraint constraint-pathcond))
              assum-lits env new-litarr new-logicman logicman))
    :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-by-witness
                                    ;; contra-of-combine-pathcond-lits
                                    ;; bfr-eval bfr-map bfr->aignet-lit bfr-fix aignet-lit->bfr
                                    logicman->bfrstate
                                    bfr-nvars
                                    aignet-lit-listp-when-bfr-listp)
                                   (aignet::bit-list-fix-of-repeat)))
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

  ;; (defret bfr-litarr-correct-p-all-envs-of-<fn>
  ;;   (implies (and (lbfr-mode-is :aignet)
  ;;                 (lbfr-listp (fgl-object-bfrlist x))
  ;;                 (lbfr-listp (fgl-object-bfrlist tracked-obj))
  ;;                 ;; (equal (aignet::nth-lit 0 litarr) 0)
  ;;                 )
  ;;            (bfr-litarr-correct-p-all-envs (fgl-object-bfrlist x)
  ;;                                  new-litarr new-logicman logicman))
  ;;   :hints(("Goal" :in-theory (e/d (bfr-litarr-correct-p-all-envs)
  ;;                                  (<fn>)))))

  (defret litarr-len-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  ;; (lbfr-listp (fgl-object-bfrlist x))
                  ;; (bfr-pathcond-p pathcond (logicman->bfrstate))
                  ;; (bfr-pathcond-p constraint-pathcond (logicman->bfrstate))
                  ;; (lbfr-listp (fgl-object-bfrlist tracked-obj))
                  (lbfr-listp assum-lits)
                  (aignet::lit-listp assum-lits)
                  )
             (equal (len new-litarr)
                    (+ 1 (bfrstate->bound (logicman->bfrstate logicman)))))
    :hints(("Goal" :in-theory (enable logicman->bfrstate
                                      aignet-lit-listp-when-bfr-listp))))

  (defret litarr2-len-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj))
                  ;; (bfr-pathcond-p pathcond (logicman->bfrstate))
                  ;; (bfr-pathcond-p constraint-pathcond (logicman->bfrstate))
                  ;; (lbfr-listp (fgl-object-bfrlist tracked-obj))
                  )
             (equal (len new-litarr2)
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

(define pathconds-map-bfrs (use-pathcond
                            pathcond
                            use-constraint
                            constraint-pathcond
                            litarr
                            logicman)
  :returns (mv contra new-pathcond new-constraint-pathcond)
  :guard (and (< 0 (lits-length litarr))
              (lbfr-mode-is :aignet)
              (ec-call (bfr-pathcond-p-fn pathcond (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
              (ec-call (bfr-pathcond-p-fn constraint-pathcond (bfrstate (bfrmode :aignet) (1- (lits-length litarr)))))
              (b* (((mv contra assum-lits)
                    (combine-pathcond-lits
                     use-pathcond
                     pathcond
                     use-constraint
                     constraint-pathcond)))
                (and (not contra)
                     (non-exec
                      (ec-call (bfr-litarr-p assum-lits
                                             litarr
                                             (bfrstate->bound (logicman->bfrstate logicman))))))))
  :hooks ((:fix :omit (pathcond constraint-pathcond)))
  :prepwork ((local (in-theory (enable combine-pathcond-lits)))
             (local (defthm bfr-litarr-p-when-subsetp
                      (implies (and (bfr-litarr-p lits1 litarr bound)
                                    (subsetp-equal lits2 lits1))
                               (bfr-litarr-p lits2 litarr bound))
                      :hints(("Goal" :in-theory (enable bfr-litarr-p subsetp-equal))))))
  :guard-hints (("goal" :do-not-induct t))
  (b* (((mv contra1 pathcond)
        (if (and use-pathcond (pathcond-enabledp pathcond))
            (logicman-pathcond-map-bfrs pathcond litarr logicman)
          (mv nil pathcond)))
       ((mv contra2 constraint-pathcond)
        (if (and use-constraint (pathcond-enabledp constraint-pathcond))
            (logicman-pathcond-map-bfrs constraint-pathcond litarr logicman)
          (mv nil constraint-pathcond))))
    (mv (or contra1 contra2) pathcond constraint-pathcond))
  ///
  ;; (local (defthm bfr-litarr-correct-p-when-subsetp
  ;;          (implies (and (bfr-litarr-correct-p lits1 env litarr logicman2 logicman)
  ;;                        (subsetp-equal lits2 lits1))
  ;;                   (bfr-litarr-correct-p lits2 env litarr logicman2 logicman))
  ;;          :hints(("Goal" :in-theory (enable bfr-litarr-correct-p subsetp-equal)))))

  (local
   (defret logicman-pathcond-eval-checkpoints!-of-<fn>-rw
     (implies (and ;; (not contra)
               (bind-free `((logicman . ,logicman2)) (logicman))
               (bfr-litarr-correct-p (aignet::nbalist-to-cube (nth *pathcond-aignet* pathcond))
                                     env litarr logicman2 logicman)
               (lbfr-mode-is :aignet logicman)
               (lbfr-mode-is :aignet logicman2)
               (equal (aignet::num-ins (logicman->aignet logicman))
                      (aignet::num-ins (logicman->aignet logicman2))))
              (equal (logicman-pathcond-eval-checkpoints! env new-pathcond logicman2)
                     (logicman-pathcond-eval-checkpoints! env pathcond logicman)))
     :fn logicman-pathcond-map-bfrs))


  (defret logicman-pathcond-eval-checkpoints!-of-<fn>
    (b* (((mv contra1 assum-lits)
          (combine-pathcond-lits
                              use-pathcond pathcond use-constraint constraint-pathcond)))
      (implies (and (bfr-litarr-correct-p
                     assum-lits env litarr logicman logicman)
                    ;; (lbfr-mode-is :aignet old-logicman)
                    (lbfr-mode-is :aignet logicman)
                    ;; (logicman-extension-p logicman old-logicman)
                    ;; (bfr-pathcond-p-fn pathcond (logicman->bfrstate old-logicman))
                    ;; (bfr-pathcond-p-fn constraint-pathcond (logicman->bfrstate old-logicman))
                    ;; (equal (aignet::num-ins (logicman->aignet logicman))
                    ;;        (aignet::num-ins (logicman->aignet old-logicman)))
                    (not contra1))
               (and (equal (logicman-pathcond-eval-checkpoints! env new-pathcond logicman)
                           (logicman-pathcond-eval-checkpoints! env pathcond logicman))
                    (equal (logicman-pathcond-eval-checkpoints! env new-constraint-pathcond logicman)
                           (logicman-pathcond-eval-checkpoints! env constraint-pathcond logicman))))))

  (defret pathcond-enabledp-of-<fn>
    (and (equal (nth *pathcond-enabledp* new-pathcond)
                (nth *pathcond-enabledp* pathcond))
         (equal (nth *pathcond-enabledp* new-constraint-pathcond)
                (nth *pathcond-enabledp* constraint-pathcond))))


  ;; (local (defthm logicman-pathcond-eval-when-nbalist-boundp-0
  ;;          (implies (and (aignet::nbalist-boundp 0 (pathcond-aignet pathcond))
  ;;                        (pathcond-enabledp pathcond)
  ;;                        (lbfr-mode-is :aignet))
  ;;                   (not (logicman-pathcond-eval env pathcond logicman)))
  ;;          :hints(("Goal" :in-theory (enable logicman-pathcond-eval)))))

  (local
   (defret contra-of-<fn>-rw
     (implies (and ;; (not contra)
               (bind-free `((logicman . ,logicman2) (env . env)) (logicman env))
               (bfr-litarr-correct-p (aignet::nbalist-to-cube (nth *pathcond-aignet* pathcond))
                                     env litarr logicman2 logicman)
               (lbfr-mode-is :aignet logicman)
               (lbfr-mode-is :aignet logicman2)
               (equal (aignet::num-ins (logicman->aignet logicman))
                      (aignet::num-ins (logicman->aignet logicman2)))
               (logicman-pathcond-eval env pathcond logicman)
               (pathcond-enabledp pathcond))
              (not contra))
     :fn logicman-pathcond-map-bfrs))

  (defret contra-of-<fn>
    (b* (((mv ?contra1 assum-lits)
          (combine-pathcond-lits
           use-pathcond pathcond use-constraint constraint-pathcond)))
      (implies (and (logicman-pathcond-eval env pathcond logicman)
                    (logicman-pathcond-eval env constraint-pathcond logicman)
                    (bfr-litarr-correct-p
                     assum-lits env litarr logicman logicman)
                    (lbfr-mode-is :aignet logicman))
               (not contra)))
    :hints(("Goal" :in-theory (e/d (aignet::contra-of-aignet-pathcond-union-cubes-top
                                      logicman-pathcond-eval)
                                   (aignet::aignet-pathcond-eval-in-terms-of-nbalist-to-cube)))))

  (defret pathcond-rewind-stack-len-of-<fn>
    (and (equal (pathcond-rewind-stack-len (bfrmode :aignet) new-pathcond)
                (pathcond-rewind-stack-len (bfrmode :aignet) pathcond))
         (equal (pathcond-rewind-stack-len (bfrmode :aignet) new-constraint-pathcond)
                (pathcond-rewind-stack-len (bfrmode :aignet) constraint-pathcond))))

  (defret pathcond-rewind-ok-of-<fn>
    (and (equal (pathcond-rewind-ok (bfrmode :aignet) new-pathcond)
                (pathcond-rewind-ok (bfrmode :aignet) pathcond))
         (equal (pathcond-rewind-ok (bfrmode :aignet) new-constraint-pathcond)
                (pathcond-rewind-ok (bfrmode :aignet) constraint-pathcond)))
    :hints(("Goal" :in-theory (e/d (pathcond-rewind-ok)
                                   (<fn>)))))

  (defret logicman-pathcond-p-of-<fn>
    (b* (((mv ?contra1 assum-lits)
          (combine-pathcond-lits
           use-pathcond pathcond use-constraint constraint-pathcond)))
      (implies (and (fgl::bfr-litarr-p
                     assum-lits litarr
                     (bfrstate->bound (logicman->bfrstate logicman)))
                    (lbfr-mode-is :aignet logicman)
                    (not contra1))
               (and (implies (logicman-pathcond-p pathcond logicman)
                             (logicman-pathcond-p new-pathcond logicman))
                    (implies (logicman-pathcond-p constraint-pathcond logicman)
                             (logicman-pathcond-p new-constraint-pathcond logicman))))))


  ;; (defret bounded-pathcond-p-of-<fn>
  ;;   (b* (((mv ?contra1 assum-lits)
  ;;         (combine-pathcond-lits
  ;;          use-pathcond pathcond use-constraint constraint-pathcond)))
  ;;     (implies (and (fgl::bfr-litarr-p
  ;;                    assum-lits
  ;;                    litarr (bfrstate->bound (logicman->bfrstate logicman)))
  ;;                   (lbfr-mode-is :aignet logicman)
  ;;                   (not contra1)
  ;;                   (aignet::bounded-pathcond-p pathcond logicman)
  ;;                   (aignet::bounded-pathcond-p constraint-pathcond logicman))
  ;;              (and (aignet::bounded-pathcond-p
  ;;                    (nth *pathcond-aignet* new-pathcond)
  ;;                    (+ 1 (aignet::fanin-count (logicman->aignet logicman))))
  ;;                   (aignet::bounded-pathcond-p
  ;;                    (nth *pathcond-aignet* new-constraint-pathcond)
  ;;                    (+ 1 (aignet::fanin-count (logicman->aignet logicman))))))))
  )


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
                                  (use-pathcond 't)
                                  (use-constraint 'nil)
                                  (logicman 'logicman)
                                  (pathcond 'pathcond)
                                  (constraint-pathcond 'constraint-pathcond)
                                  (state 'state))
  :guard (and (lbfr-mode-is :aignet)
              (lbfr-listp (fgl-object-bfrlist x))
              (lbfr-listp (fgl-object-bfrlist tracked-obj))
              (lbfr-listp (fgl-object-bfrlist tracked-bits))
              (ec-call (bfr-pathcond-p-fn pathcond (logicman->bfrstate)))
              (ec-call (bfr-pathcond-p-fn constraint-pathcond (logicman->bfrstate))))
  :returns (mv contra
               (new-x fgl-object-p)
               (new-logicman)
               (new-pathcond)
               (new-constraint-pathcond)
               (new-state))
  :hooks nil
  :guard-hints (("goal" :in-theory (enable logicman->bfrstate)))
  :guard-debug t
  (b* (((mv contra assum-lits)
        (combine-pathcond-lits use-pathcond pathcond use-constraint constraint-pathcond))
       ((when contra)
        (mv t nil logicman pathcond constraint-pathcond state))
       ((acl2::local-stobjs litarr litarr2)
        (mv contra new-x litarr litarr2 logicman pathcond constraint-pathcond state))
       ((mv litarr litarr2 logicman state)
        (fgl-simplify-object-logicman
         x litarr litarr2 transforms
         :tracked-obj tracked-obj
         :tracked-bits tracked-bits
         :assum-lits assum-lits))
       ((mv new-x memo) (fgl-object-map-bfrs-memo x litarr2 nil))
       (- (fast-alist-free memo))
       ((mv contra pathcond constraint-pathcond)
        (pathconds-map-bfrs use-pathcond pathcond use-constraint constraint-pathcond litarr logicman)))
    (mv contra (and (not contra) new-x)
        litarr litarr2 logicman pathcond constraint-pathcond state))
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

  (local
   (defret eval-of-<fn>-rw
     (implies (and (bind-logicman-extension logicman2 logicman)
                   (bfr-litarr-correct-p (fgl-object-bfrlist x)
                                         (fgl-env->bfr-vals env)
                                         litarr logicman2 logicman))
              (equal (fgl-object-eval new-x env logicman2)
                     (fgl-object-eval x env logicman)))
     :fn fgl-object-map-bfrs))

  (local
   (defret contra-of-<fn>-rw
     (b* (((mv ?contra1 assum-lits)
           (combine-pathcond-lits
            use-pathcond pathcond use-constraint constraint-pathcond)))
       (implies (and (bind-free '((env . (fgl-env->bfr-vals$inline env))) (env))
                     (logicman-pathcond-eval env pathcond logicman)
                     (logicman-pathcond-eval env constraint-pathcond logicman)
                     (bfr-litarr-correct-p
                      assum-lits env litarr logicman logicman)
                     (lbfr-mode-is :aignet logicman))
                (not contra)))
     :fn pathconds-map-bfrs))

  (local (defthm bfr-litarr-correct-p-of-logicman-extension
           (implies (and (bind-logicman-extension old older)
                         (bfr-listp bfrs (logicman->bfrstate older)))
                    (iff (bfr-litarr-correct-p bfrs env litarr new old)
                         (bfr-litarr-correct-p bfrs env litarr new older)))
           :hints(("Goal" :in-theory (enable bfr-listp bfr-litarr-correct-p)))))


  (defret eval-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj))
                  (bfr-pathcond-p pathcond (logicman->bfrstate))
                  (bfr-pathcond-p constraint-pathcond (logicman->bfrstate))
                  (logicman-pathcond-eval (fgl-env->bfr-vals env) pathcond logicman)
                  (logicman-pathcond-eval (fgl-env->bfr-vals env) constraint-pathcond logicman))
             (equal (fgl-object-eval new-x env new-logicman)
                    (fgl-object-eval x env logicman)))
    :hints(("Goal" :in-theory (enable contra-of-combine-pathcond-lits))))

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
             (lbfr-listp (fgl-object-bfrlist new-x) new-logicman)))

  (defret logicman-pathcond-eval-checkpoints!-of-<fn>
    (implies (and (lbfr-mode-is :aignet logicman)
                  (bfr-pathcond-p pathcond (logicman->bfrstate logicman))
                  (bfr-pathcond-p constraint-pathcond (logicman->bfrstate logicman))
                  ;; (lbfr-listp (fgl-object-bfrlist x))
                  )
             (and (equal (logicman-pathcond-eval-checkpoints! env new-pathcond new-logicman)
                         (logicman-pathcond-eval-checkpoints! env pathcond logicman))
                  (equal (logicman-pathcond-eval-checkpoints! env new-constraint-pathcond new-logicman)
                         (logicman-pathcond-eval-checkpoints! env constraint-pathcond logicman)))))

  (defret pathcond-enabledp-of-<fn>
    (and (equal (nth *pathcond-enabledp* new-pathcond)
                (nth *pathcond-enabledp* pathcond))
         (equal (nth *pathcond-enabledp* new-constraint-pathcond)
                (nth *pathcond-enabledp* constraint-pathcond))))

  (defret logicman-pathcond-eval-of-<fn>
    (implies (and (lbfr-mode-is :aignet logicman)
                  (bfr-pathcond-p pathcond (logicman->bfrstate logicman))
                  (bfr-pathcond-p constraint-pathcond (logicman->bfrstate logicman))
                  ;; (lbfr-listp (fgl-object-bfrlist x))
                  )
             (and (equal (logicman-pathcond-eval env new-pathcond new-logicman)
                         (logicman-pathcond-eval env pathcond logicman))
                  (equal (logicman-pathcond-eval env new-constraint-pathcond new-logicman)
                         (logicman-pathcond-eval env constraint-pathcond logicman))))
    :hints (("goal" :use logicman-pathcond-eval-checkpoints!-of-<fn>
             :in-theory (e/d (logicman-pathcond-eval-checkpoints!)
                             (logicman-pathcond-eval-checkpoints!-of-<fn>
                              <fn>)))
            '(:cases ((pathcond-enabledp pathcond)))
            '(:cases ((pathcond-enabledp constraint-pathcond)))))

  (local
   (defret contra-of-<fn>-rw2
     (b* (((mv ?contra1 assum-lits)
           (combine-pathcond-lits
            use-pathcond pathcond use-constraint constraint-pathcond)))
       (implies (and (bind-free '((env . env)) (env))
                     (logicman-pathcond-eval env pathcond logicman)
                     (logicman-pathcond-eval env constraint-pathcond logicman)
                     (bfr-litarr-correct-p
                      assum-lits env litarr logicman logicman)
                     (lbfr-mode-is :aignet logicman))
                (not contra)))
     :fn pathconds-map-bfrs))

  (defret contra-of-<fn>
    (implies (and (lbfr-mode-is :aignet logicman)
                  (bfr-pathcond-p pathcond (logicman->bfrstate logicman))
                  (bfr-pathcond-p constraint-pathcond (logicman->bfrstate logicman))
                  ;; (lbfr-listp (fgl-object-bfrlist x))
                  (logicman-pathcond-eval env pathcond logicman)
                  (logicman-pathcond-eval env constraint-pathcond logicman))
             (not contra))
    :hints(("Goal" :in-theory (e/d (contra-of-combine-pathcond-lits)))))

  (defret pathcond-rewind-stack-len-of-<fn>
    (and (equal (pathcond-rewind-stack-len (bfrmode :aignet) new-pathcond)
                (pathcond-rewind-stack-len (bfrmode :aignet) pathcond))
         (equal (pathcond-rewind-stack-len (bfrmode :aignet) new-constraint-pathcond)
                (pathcond-rewind-stack-len (bfrmode :aignet) constraint-pathcond))))

  (defret pathcond-rewind-ok-of-<fn>
    (and (equal (pathcond-rewind-ok (bfrmode :aignet) new-pathcond)
                (pathcond-rewind-ok (bfrmode :aignet) pathcond))
         (equal (pathcond-rewind-ok (bfrmode :aignet) new-constraint-pathcond)
                (pathcond-rewind-ok (bfrmode :aignet) constraint-pathcond)))
    :hints(("Goal" :in-theory (e/d (pathcond-rewind-ok)
                                   (<fn>)))))


  (defret logicman-pathcond-p-of-<fn>
    (implies (and (lbfr-mode-is :aignet logicman)
                  (logicman-pathcond-p pathcond logicman)
                  (logicman-pathcond-p constraint-pathcond logicman))
             (and (logicman-pathcond-p new-pathcond new-logicman)
                  (logicman-pathcond-p new-constraint-pathcond new-logicman)))))


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
                              'nil)
                             ((use-pathcond
                               "Assume the path condition true when simplifying the formulas")
                              't)
                             ((use-constraint
                               "Assume the constraint condition true when simplifying the formulas")
                              't))
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  x)



(define fgl-simplify-ordered-impl ((x fgl-object-p
                                     "Object whose symbolic value will be preserved by the transform.")
                                  (transforms)
                                  &key
                                  ((tracked-obj
                                    fgl-object-p
                                    "Object that is not preserved but whose bits' formulas
                                are tracked through possibly non-preserving transforms,
                                for heuristic use by the transforms")
                                   'nil)
                                  (use-pathcond 't)
                                  (use-constraint 'nil)
                                  (logicman 'logicman)
                                  (pathcond 'pathcond)
                                  (constraint-pathcond 'constraint-pathcond)
                                  (state 'state))
  :guard (and (lbfr-mode-is :aignet)
              (lbfr-listp (fgl-object-bfrlist x))
              (lbfr-listp (fgl-object-bfrlist tracked-obj))
              (ec-call (bfr-pathcond-p-fn pathcond (logicman->bfrstate)))
              (ec-call (bfr-pathcond-p-fn constraint-pathcond (logicman->bfrstate))))
  :returns (mv (new-x fgl-object-p)
               (new-logicman)
               (new-state))
  :hooks nil
  :guard-hints (("goal" :in-theory (enable logicman->bfrstate)))
  :guard-debug t
  (b* (((mv contra assum-lits)
        (combine-pathcond-lits use-pathcond pathcond use-constraint constraint-pathcond))
       ((when contra)
        (mv nil logicman state))
       ((mv new-obj logicman state)
        (fgl-simplify-object-ordered-logicman
         x transforms
         :tracked-obj tracked-obj
         :assum-lits assum-lits)))
    (mv new-obj logicman state))
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

  ;; (local
  ;;  (defret eval-of-<fn>-rw
  ;;    (implies (and (bind-logicman-extension logicman2 logicman)
  ;;                  (bfr-litarr-correct-p (fgl-object-bfrlist x)
  ;;                                        (fgl-env->bfr-vals env)
  ;;                                        litarr logicman2 logicman))
  ;;             (equal (fgl-object-eval new-x env logicman2)
  ;;                    (fgl-object-eval x env logicman)))
  ;;    :fn fgl-object-map-bfrs))

  ;; (local
  ;;  (defret contra-of-<fn>-rw
  ;;    (b* (((mv ?contra1 assum-lits)
  ;;          (combine-pathcond-lits
  ;;           use-pathcond pathcond use-constraint constraint-pathcond)))
  ;;      (implies (and (bind-free '((env . (fgl-env->bfr-vals$inline env))) (env))
  ;;                    (logicman-pathcond-eval env pathcond logicman)
  ;;                    (logicman-pathcond-eval env constraint-pathcond logicman)
  ;;                    (bfr-litarr-correct-p
  ;;                     assum-lits env litarr logicman logicman)
  ;;                    (lbfr-mode-is :aignet logicman))
  ;;               (not contra)))
  ;;    :fn pathconds-map-bfrs))

  ;; (local (defthm bfr-litarr-correct-p-of-logicman-extension
  ;;          (implies (and (bind-logicman-extension old older)
  ;;                        (bfr-listp bfrs (logicman->bfrstate older)))
  ;;                   (iff (bfr-litarr-correct-p bfrs env litarr new old)
  ;;                        (bfr-litarr-correct-p bfrs env litarr new older)))
  ;;          :hints(("Goal" :in-theory (enable bfr-listp bfr-litarr-correct-p)))))


  (defret eval-of-<fn>
    (implies (and (lbfr-mode-is :aignet)
                  (lbfr-listp (fgl-object-bfrlist x))
                  (lbfr-listp (fgl-object-bfrlist tracked-obj))
                  (bfr-pathcond-p pathcond (logicman->bfrstate))
                  (bfr-pathcond-p constraint-pathcond (logicman->bfrstate))
                  (logicman-pathcond-eval (fgl-env->bfr-vals env) pathcond logicman)
                  (logicman-pathcond-eval (fgl-env->bfr-vals env) constraint-pathcond logicman))
             (equal (fgl-object-eval new-x env new-logicman)
                    (fgl-object-eval x env logicman)))
    :hints(("Goal" :in-theory (enable contra-of-combine-pathcond-lits))))

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


(define fgl-simplify-ordered (x transforms
                             &key
                             ((tracked-obj
                               "Object that is not preserved but whose bits' formulas
                                are tracked through possibly non-preserving transforms,
                                for heuristic use by the transforms")
                              'nil)
                             ((use-pathcond
                               "Assume the path condition true when simplifying the formulas")
                              't)
                             ((use-constraint
                               "Assume the constraint condition true when simplifying the formulas")
                              't))
  :ignore-ok t
  :irrelevant-formals-ok t
  :enabled t
  x)





(def-formula-checks fgl-simplify-formula-checks
  (fgl-simplify-object-fn fgl-simplify-ordered-fn))

;; (local (in-theory (enable BFR-LISTP-WHEN-NOT-MEMBER-WITNESS)))
(local (include-book "primitive-lemmas"))

(local (defthm bfr-listp-of-car-objectlist
         (implies (bfr-listp (fgl-objectlist-bfrlist x))
                  (bfr-listp (fgl-object-bfrlist (car x))))))

(local (defthm bfr-listp-of-cdr-objectlist
         (implies (bfr-listp (fgl-objectlist-bfrlist x))
                  (bfr-listp (fgl-objectlist-bfrlist (cdr x))))))

(local (in-theory (disable bfr-listp-when-not-member-witness
                           fgl-object-bfrlist-when-booleanp
                           fgl-object-bfrlist-when-integerp
                           bfr-listp$-when-subsetp-equal
                           equal-of-booleans-rewrite
                           append)))
(local
 (acl2::add-default-hints
  '((and stable-under-simplificationp
         '(:in-theory (enable bfr-listp-when-not-member-witness))))))

(def-fgl-primitive fgl-simplify-object-fn (x transforms tracked-obj tracked-bits use-pathcond use-constraint)
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (cw "Warning: skipping simplify transform because we're not in aignet mode~%")
        (mv nil nil interp-st state))
       ((unless (fgl-object-case transforms :g-concrete))
        (fgl-interp-error :msg "Fgl-simplify-object: transforms must be a concrete object)"
                          :debug-obj transforms
                          :nvals 2))
       (transforms (g-concrete->val transforms)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (pathcond (interp-st->pathcond interp-st))
                (constraint-pathcond (interp-st->constraint interp-st)))
               (contra new-x logicman pathcond constraint-pathcond state)
               (fgl-simplify-object-impl
                x transforms :tracked-obj tracked-obj :tracked-bits tracked-bits :use-pathcond use-pathcond :use-constraint use-constraint)
               (if contra
                   (b* ((interp-st (interp-st-set-error :unreachable interp-st)))
                     (mv t new-x interp-st state))
                 (mv t new-x interp-st state))))
  :returns (mv successp ans interp-st state)
  :formula-check fgl-simplify-formula-checks)



(def-fgl-primitive fgl-simplify-ordered-fn (x transforms tracked-obj use-pathcond use-constraint)
  (b* (((unless (bfr-mode-is :aignet (interp-st-bfr-mode)))
        (cw "Warning: skipping simplify transform because we're not in aignet mode~%")
        (mv nil nil interp-st state))
       ((unless (fgl-object-case transforms :g-concrete))
        (fgl-interp-error :msg "Fgl-simplify-object: transforms must be a concrete object)"
                          :debug-obj transforms
                          :nvals 2))
       (transforms (g-concrete->val transforms)))
    (stobj-let ((logicman (interp-st->logicman interp-st))
                (pathcond (interp-st->pathcond interp-st))
                (constraint-pathcond (interp-st->constraint interp-st)))
               (new-x logicman state)
               (fgl-simplify-ordered-impl
                x transforms :tracked-obj tracked-obj :use-pathcond use-pathcond :use-constraint use-constraint)
               (mv t new-x interp-st state)))
  :returns (mv successp ans interp-st state)
  :formula-check fgl-simplify-formula-checks)
