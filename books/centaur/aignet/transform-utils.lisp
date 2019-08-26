; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2017 Centaur Technology
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


(include-book "centaur/aignet/copying" :dir :system)
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (in-theory (disable acl2::resize-list-when-atom resize-list)))

(defstobj-clone aignet-tmp aignet :suffix "TMP")
(defstobj-clone copy2 copy :suffix "2")
(defstobj-clone strash2 strash :suffix "2")


(define count-xors-rec ((start natp) aignet (acc natp))
  :guard (<= start (num-fanins aignet))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :measure (nfix (- (num-fanins aignet) (nfix start)))
  :returns (count natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix start)))
                   :exec (eql start (num-fanins aignet))))
        (lnfix acc))
       (acc (if (and (eql (id->type start aignet) (gate-type))
                     (eql (id->regp start aignet) 1))
                (+ 1 (lnfix acc))
              (lnfix acc))))
    (count-xors-rec (+ 1 (lnfix start)) aignet acc))
  ///

  (local (defthm stype-count-of-lookup-fanin-count
           (implies (not (equal (ctype stype) (out-ctype)))
                    (equal (stype-count stype (lookup-id (fanin-count aignet) aignet))
                           (stype-count stype aignet)))
           :hints(("Goal" :in-theory (enable lookup-id fanin-count fanin-node-p)))))

  (local (defthm cdr-of-lookup-id
           (implies (and (posp n)
                         (< n (num-fanins aignet))
                         (not (equal (ctype stype) (out-ctype))))
                    (equal (stype-count stype (cdr (lookup-id n aignet)))
                           (stype-count stype (lookup-id (+ -1 n) aignet))))
           :hints(("Goal" :in-theory (e/d (lookup-id node-list-fix fanin-node-p)
                                          (lookup-id-in-extension-inverse)) :induct t)
                  (and stable-under-simplificationp
                       '(:expand ((lookup-id (+ -1 (fanin-count aignet)) aignet)))))))

  (defret count-xors-rec-value
    (implies (<= (nfix start) (num-fanins aignet))
             (equal count
                    (+ (nfix acc)
                       (- (stype-count :xor aignet)
                          (stype-count :xor (lookup-id (- (nfix start) 1) aignet))))))
    :hints(("Goal" :in-theory (e/d (stype-count lookup-id
                                                lookup-id-in-bounds))
            :induct (count-xors-rec start aignet acc)
            :expand ((stype-count :xor (lookup-id start aignet))))
           (and stable-under-simplificationp
                '(:cases ((natp start)))))))

(define count-xors  (aignet)
  :returns (count natp :rule-classes :type-prescription)
  (count-xors-rec 0 aignet 0)
  ///
  (defret count-xors-value
    (equal (count-xors aignet)
           (stype-count :xor aignet))))
                   
  

(define print-aignet-stats ((name stringp) aignet)
  (b* ((xors (count-xors aignet))
       (gates (num-gates aignet)))
    (cw "~s0 network: Nodes: ~x8       ~
         PIs ~x1 regs ~x2~%       ~
         gates ~x3 (ands ~x4 xors ~x5)~%       ~
         nxsts ~x6 POs ~x7~%"
        (mbe :logic (acl2::str-fix name) :exec name)
        (num-ins aignet)
        (num-regs aignet)
        gates
        (- gates xors)
        xors
        (num-nxsts aignet)
        (num-outs aignet)
        (num-fanins aignet))))





(define aignet-raw-copy-fanins ((n posp) aignet aignet2)
  :guard (and (<= n (num-fanins aignet))
              (non-exec (equal aignet2 (aignet-fanins (lookup-id (1- n) aignet)))))
  ;; :measure (nfix (- (num-fanins aignet) (nfix n)))
  :guard-hints (("goal" :in-theory (e/d (aignet-idp fanin co-node->fanin regp
                                                    gate-node->fanin0
                                                    gate-node->fanin1)
                                        (aignet-nodes-ok))
                 :expand ((:free (n aignet aignet2) (aignet-raw-copy-fanins n aignet aignet2))
                          (aignet-fanins (lookup-id n aignet)))
                 :cases ((equal 0 n))
                 :use ((:instance aignet-nodes-ok (aignet (lookup-id n aignet))))))
  :returns new-aignet2
  :enabled t
  :prepwork ((local (defthm aignet-fanins-under-iff
                      (iff (aignet-fanins x)
                           (posp (fanin-count x)))
                      :hints(("Goal" :in-theory (enable aignet-fanins fanin-count)))))
             (local (defthm aignet-fanins-of-lookup-fanin-count
                      (equal (aignet-fanins (lookup-id (fanin-count aignet) aignet))
                             (aignet-fanins aignet))
                      :hints(("Goal" :in-theory (enable lookup-id fanin-count fanin-node-p)))))
             (local (defthm aignet-fanins-of-cdr-lookup-id
                      (implies (<= (nfix n) (fanin-count aignet))
                               (equal (aignet-fanins (cdr (lookup-id n aignet)))
                                      (aignet-fanins (lookup-id (nfix (+ -1 (nfix n))) aignet))))
                      :hints(("Goal" :in-theory (enable aignet-fanins lookup-id fanin-count)))))
             (local (defthm node-equal-pi
                      (implies (node-p x)
                               (equal (equal x '(:pi))
                                      (equal (stype x) :pi)))
                      :hints(("Goal" :in-theory (enable node-p stype)))))
             (local (defthm node-equal-reg
                      (implies (node-p x)
                               (equal (equal x '(:reg))
                                      (equal (stype x) :reg)))
                      :hints(("Goal" :in-theory (enable node-p stype)))))
             (local (defthm fanin-count-cdr-lookup-id
                      (equal (fanin-count (cdr (lookup-id n aignet)))
                             (if (or (zp n)
                                     (< (fanin-count aignet) (nfix n)))
                                 0
                               (+ -1 (nfix n))))
                      :hints(("Goal" :in-theory (enable lookup-id fanin-count))))))
  (mbe :logic (non-exec (aignet-fanins aignet))
       :exec (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix n)))
                              :exec (eql n (num-fanins aignet))))
                   aignet2)
                  (slot0 (id->slot n 0 aignet))
                  (slot1 (id->slot n 1 aignet))
                  (type (snode->type slot0))
                  (regp (snode->regp slot1))
                  (aignet2 (aignet-case type regp
                             :xor (aignet-add-xor (snode->fanin slot0)
                                                  (snode->fanin slot1)
                                                  aignet2)
                             :and (aignet-add-and (snode->fanin slot0)
                                                  (snode->fanin slot1)
                                                  aignet2)
                             :pi (aignet-add-in aignet2)
                             :reg (aignet-add-reg aignet2)
                             :const aignet2)))
               (aignet-raw-copy-fanins (+ 1 (lnfix n)) aignet aignet2))))

(define aignet-raw-copy-fanins-top (aignet aignet2)
  :enabled t
  (mbe :logic (non-exec (aignet-fanins aignet))
       :exec (b* ((aignet2 (aignet-init 0 (num-regs aignet) (num-ins aignet)
                                        (num-fanins aignet)
                                        aignet2)))
               (aignet-raw-copy-fanins 1 aignet aignet2))))

(local (defthm fanin-count-of-append
         (equal (fanin-count (append a b))
                (+ (fanin-count a) (fanin-count b)))))
(local (defthm stype-count-of-append
         (equal (stype-count stype (append a b))
                (+ (stype-count stype a) (stype-count stype b)))))

(define aignet-raw-copy-outputs ((n natp) aignet aignet2)
  :guard (and (<= n (num-outs aignet))
              (non-exec (equal aignet2 (append (aignet-outputs-aux n aignet)
                                               (aignet-fanins aignet)))))
  :guard-hints(("Goal" :in-theory (enable aignet-idp)
                :expand ((:free (n aignet2) (aignet-raw-copy-outputs n aignet aignet2))))
               (and stable-under-simplificationp
                     '(:expand ((aignet-outputs-aux (+ 1 n) aignet)))))

  :prepwork ((local (in-theory (enable aignet-outputs))))
  :enabled t
  (mbe :logic (non-exec (append (aignet-outputs aignet) (aignet-fanins aignet)))
       :exec (b* (((when (mbe :logic (zp (- (num-outs aignet) (nfix n)))
                              :exec (eql n (num-outs aignet))))
                   aignet2)
                  (fanin (outnum->fanin n aignet))
                  (aignet2 (aignet-add-out fanin aignet2)))
               (aignet-raw-copy-outputs (+ 1 (lnfix n)) aignet aignet2))))


(define aignet-raw-copy-nxsts ((n natp) aignet aignet2)
  :guard (and (<= n (num-regs aignet))
              (non-exec (equal aignet2 (append (aignet-nxsts-aux n aignet)
                                               (aignet-outputs aignet)
                                               (aignet-fanins aignet)))))
  :guard-hints(("Goal" :in-theory (enable aignet-idp)
                :expand ((:free (n aignet2) (aignet-raw-copy-nxsts n aignet aignet2))))
               (and stable-under-simplificationp
                     '(:expand ((aignet-nxsts-aux (+ 1 n) aignet)))))
  :prepwork ((local (in-theory (enable aignet-nxsts aignet-norm))))
  :enabled t
  (mbe :logic (non-exec (aignet-norm aignet))
       :exec (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                              :exec (eql n (num-regs aignet))))
                   aignet2)
                  (fanin (regnum->nxst n aignet))
                  (aignet2 (aignet-set-nxst fanin n aignet2)))
               (aignet-raw-copy-nxsts (+ 1 (lnfix n)) aignet aignet2))))

;; (defthm aignet-raw-copy-fanins-guard-ok
;;   (equal (aignet-init (num-outs aignet)
;;                                         (num-regs aignet)
;;                                         (num-ins aignet)
;;                                         (num-fanins aignet)
;;                                         aignet2)
;;          (aignet-fanins (lookup-id -1 aignet))))

;; (define aignet-raw-copy-start (aignet aignet2)
;;   :guard-hints (("goal" :in-theory nil))
;;   (b* ((aignet2 (aignet-init (num-outs aignet)
;;                              (num-regs aignet)
;;                              (num-ins aignet)
;;                              (num-fanins aignet)
;;                              aignet2)))
;;     (aignet-raw-copy-fanins 1 aignet aignet2)))

(define aignet-raw-copy (aignet aignet2)
  :enabled t
  ;; :guard-debug t
  :guard-hints (("goal" :in-theory (enable aignet-nxsts-aux aignet-outputs-aux)))
  (mbe :logic (non-exec (aignet-norm aignet))
       :exec (b* ((aignet2 (aignet-init (num-outs aignet)
                                        (num-regs aignet)
                                        (num-ins aignet)
                                        (num-fanins aignet)
                                        aignet2))
                  (aignet2 (aignet-raw-copy-fanins 1 aignet aignet2))
                  (aignet2 (aignet-raw-copy-outputs 0 aignet aignet2)))
               (aignet-raw-copy-nxsts 0 aignet aignet2))))


(fty::deffixcong aignet-equiv equal (id-eval id invals regvals aignet) aignet
  :hints (("goal" :induct (id-eval-ind id aignet)
           :expand ((:free (aignet) (id-eval id invals regvals aignet)))
           :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits
                              aignet-idp))))

(fty::deffixcong aignet-equiv equal (lit-eval lit invals regvals aignet) aignet
  :hints (("goal" :expand ((:free (aignet) (lit-eval lit invals regvals aignet))))))

(fty::deffixcong aignet-equiv equal (eval-and-of-lits lit1 lit2 invals regvals aignet) aignet
  :hints(("Goal" :in-theory (enable eval-and-of-lits))))

(fty::deffixcong aignet-equiv equal (eval-xor-of-lits lit1 lit2 invals regvals aignet) aignet
  :hints(("Goal" :in-theory (enable eval-xor-of-lits))))

(fty::deffixcong aignet-equiv equal (output-eval n invals regvals aignet) aignet
  :hints(("Goal" :in-theory (enable output-eval))))

(fty::deffixcong aignet-equiv equal (nxst-eval n invals regvals aignet) aignet
  :hints(("Goal" :in-theory (enable nxst-eval))))

(fty::defrefinement aignet-equiv outs-comb-equiv
  :hints(("Goal" :in-theory (enable outs-comb-equiv))))

(fty::defrefinement aignet-equiv nxsts-comb-equiv
  :hints(("Goal" :in-theory (enable nxsts-comb-equiv))))

(fty::defrefinement aignet-equiv comb-equiv
  :hints(("Goal" :in-theory (enable comb-equiv))))
