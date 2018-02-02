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

(define count-xors-rec ((start natp) aignet (acc natp))
  :guard (<= start (num-nodes aignet))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  :measure (nfix (- (num-nodes aignet) (nfix start)))
  :returns (count natp :rule-classes :type-prescription)
  (b* (((when (mbe :logic (zp (- (num-nodes aignet) (nfix start)))
                   :exec (eql start (num-nodes aignet))))
        (lnfix acc))
       (acc (if (and (eql (id->type start aignet) (gate-type))
                     (eql (id->regp start aignet) 1))
                (+ 1 (lnfix acc))
              (lnfix acc))))
    (count-xors-rec (+ 1 (lnfix start)) aignet acc))
  ///

  (local (defthm cdr-of-lookup-id
           (implies (and (posp n)
                         (< n (num-nodes aignet)))
                    (equal (cdr (lookup-id n aignet))
                           (lookup-id (+ -1 n) aignet)))
           :hints(("Goal" :in-theory (enable lookup-id) :induct t)
                  (and stable-under-simplificationp
                       '(:expand ((lookup-id (+ -1 (node-count aignet)) aignet)))))))

  (defret count-xors-rec-value
    (implies (<= (nfix start) (num-nodes aignet))
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
    (cw "~s0 network: Nodes: ~x8  Max fanin ~x9~%       ~
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
        (num-nodes aignet)
        (max-fanin aignet))))





(define aignet-raw-copy-aux ((n natp) aignet aignet2)
  :guard (and (<= n (num-nodes aignet))
              (non-exec (equal aignet2 (lookup-id (+ -1 n) aignet))))
  ;; :measure (nfix (- (num-nodes aignet) (nfix n)))
  :guard-hints (("goal" :in-theory (e/d (aignet-idp fanin co-node->fanin regp
                                                    gate-node->fanin0
                                                    gate-node->fanin1)
                                        (aignet-nodes-ok))
                 :expand ((:free (n aignet aignet2) (aignet-raw-copy-aux n aignet aignet2)))
                 :cases ((equal 0 n))
                 :use ((:instance aignet-nodes-ok (aignet (lookup-id n aignet))))))
  :returns new-aignet2
  :enabled t
  :prepwork ((local (defthm lookup-id-of-num-nodes
                      (implies (equal n (node-count aignet))
                               (equal (lookup-id n aignet)
                                      (node-list-fix aignet)))
                      :hints(("Goal" :in-theory (enable lookup-id)))))
             (local (defthm lookup-id-of-n-minus-1
                      (implies (and (natp n)
                                    (<= n (node-count aignet)))
                               (equal (lookup-id (+ -1 n) aignet)
                                      (cdr (lookup-id n aignet))))
                      :hints(("Goal" :in-theory (enable lookup-id)
                              :induct (lookup-id n aignet)))))
             (local (defret aignet-litp-in-extension-of-cdr-of-fanin
                      (implies (aignet-extension-p new (cdr aignet))
                               (aignet-litp lit new))
                      :hints(("Goal" :in-theory (enable fanin)))
                      :fn fanin))
             (local (defthm stype-is-pi-implies-equal-pi
                      (implies (node-p node)
                               (equal (equal (stype node) :pi)
                                      (equal node '(:pi))))
                      :hints(("Goal" :in-theory (enable node-p stype)))))
             (local (defthm stype-is-reg-implies-equal-reg
                      (implies (node-p node)
                               (equal (equal (stype node) :reg)
                                      (equal node '(:reg))))
                      :hints(("Goal" :in-theory (enable node-p stype)))))
             (local (defthm equal-of-cons-by-components
                      (implies (and (consp c)
                                    (equal (car c) a)
                                    (equal (cdr c) b))
                               (equal (equal (cons a b) c) t)))))
  (mbe :logic (non-exec aignet)
       :exec
       (b* (((when (mbe :logic (zp (- (num-nodes aignet) (nfix n)))
                        :exec (eql n (num-nodes aignet))))
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
                       :po (aignet-add-out (snode->fanin slot0) aignet2)
                       :nxst (aignet-set-nxst (snode->fanin slot0)
                                              (snode->regid slot1)
                                              aignet2)
                       :const aignet2)))
         (aignet-raw-copy-aux (+ 1 (lnfix n)) aignet aignet2))))

(define aignet-raw-copy (aignet aignet2)
  :enabled t
  (mbe :logic (non-exec aignet)
       :exec (b* ((aignet2 (aignet-init (num-outs aignet)
                                        (num-regs aignet)
                                        (num-ins aignet)
                                        (num-nodes aignet)
                                        aignet2)))
               (aignet-raw-copy-aux 0 aignet aignet2))))


