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

(include-book "aignet-absstobj")


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
