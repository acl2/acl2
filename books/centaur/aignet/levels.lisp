; AIGNET - And-Inverter Graph Networks -- reference counting
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
(include-book "arrays")
(include-book "aignet-absstobj")
(include-book "centaur/misc/iter" :dir :system)
(local (include-book "clause-processors/just-expand" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(local (in-theory (disable nth update-nth
                           acl2::nth-with-large-index
                           true-listp-update-nth)))

(defstobj-clone aignet-levels u32arr :suffix "-LEVELS")
(defstobj-clone levels u32arr :prefix "LEVELS-")

(define aignet-record-levels-aux ((n natp)
                                  (aignet)
                                  (aignet-levels))
  :guard (and (<= (num-fanins aignet) (u32-length aignet-levels))
              (<= n (num-fanins aignet)))
  :measure (nfix (- (num-fanins aignet) (nfix n)))
  :returns (aignet-levels-out (<= (len aignet-levels)
                                  (len aignet-levels-out))
                              :rule-classes :linear)
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (b* (((when (mbe :logic (zp (- (num-fanins aignet) (nfix n)))
                   :exec (eql n (num-fanins aignet))))
        aignet-levels)
       (aignet-levels
        (aignet-case (id->type n aignet)
          :gate (b* ((lev0 (get-u32 (lit-id (gate-id->fanin0 n aignet)) aignet-levels))
                     (lev1 (get-u32 (lit-id (gate-id->fanin1 n aignet)) aignet-levels))
                     (level (+ 1 (max lev0 lev1))))
                  (set-u32 n level aignet-levels))
          :in (set-u32 n 0 aignet-levels)
          :const (set-u32 n 0 aignet-levels))))
    (aignet-record-levels-aux (+ 1 (lnfix n)) aignet aignet-levels))

  ///
  (defthm aignet-record-levels-aux-of-nfix
    (equal (aignet-record-levels-aux (nfix n) aignet aignet-levels)
           (aignet-record-levels-aux n aignet aignet-levels))
    :hints (("goal" :induct (aignet-record-levels-aux n aignet aignet-levels)
             :expand ((aignet-record-levels-aux n aignet aignet-levels)
                      (aignet-record-levels-aux (nfix n) aignet aignet-levels)))))

  (defund aignet-node-level (n aignet)
    (declare (xargs :stobjs aignet
                    :measure (nfix n)
                    :verify-guards nil))
    (b* (((unless (id-existsp n aignet)) 0))
      (aignet-case (id->type n aignet)
        :gate (b* ((lev0 (aignet-node-level (lit-id (gate-id->fanin0 n aignet)) aignet))
                   (lev1 (aignet-node-level (lit-id (gate-id->fanin1 n aignet)) aignet)))
                (+ 1 (max lev0 lev1)))
        :in 0 :const 0 :out 0)))

  (local (defthm aignet-node-level-of-nfix
           (equal (aignet-node-level (nfix n) aignet)
                  (aignet-node-level n aignet))
           :hints(("Goal" :in-theory (enable (:i aignet-node-level))
                   :induct (aignet-node-level n aignet)
                   :expand ((aignet-node-level n aignet)
                            (aignet-node-level (nfix n) aignet))))))

  (defun-nx aignet-levels-correct-up-to (n aignet aignet-levels)
    (declare (xargs :verify-guards nil))
    (if (zp n)
        t
      (and (implies (not (equal (node->type (car (lookup-id (1- n) aignet)))
                                (out-type)))
                    (equal (nth (1- n) aignet-levels)
                           (aignet-node-level (1- n) aignet)))
           (aignet-levels-correct-up-to (1- n) aignet aignet-levels))))

  (defthm aignet-levels-correct-up-to-implies
    (implies (and (aignet-levels-correct-up-to m aignet aignet-levels)
                  (< (nfix n) (nfix m))
                  (not (equal (node->type (car (lookup-id n aignet)))
                              (out-type))))
             (equal (nth n aignet-levels)
                    (aignet-node-level n aignet)))
    :hints (("goal" :induct (aignet-levels-correct-up-to m aignet aignet-levels))))

  (local
   (progn
     (defthm aignet-levels-correct-up-to-of-nfix
       (equal (aignet-levels-correct-up-to (nfix n) aignet aignet-levels)
              (aignet-levels-correct-up-to n aignet aignet-levels)))

     (defthm aignet-levels-correct-up-to-of-update-past
       (implies (<= (nfix n) (nfix m))
                (equal (aignet-levels-correct-up-to n aignet (update-nth m val aignet-levels))
                       (aignet-levels-correct-up-to n aignet aignet-levels))))

     (defthm id-of-gate-fanin0-less-than-n
       (implies (equal (stype (car (lookup-id n aignet))) :gate)
                (< (lit-id (aignet-lit-fix (gate-node->fanin0 (car (lookup-id n aignet)))
                                           (cdr (lookup-id n aignet))))
                   n)))

     (defthm id-of-gate-fanin1-less-than-n
       (implies (equal (stype (car (lookup-id n aignet))) :gate)
                (< (lit-id (aignet-lit-fix (gate-node->fanin1 (car (lookup-id n aignet)))
                                           (cdr (lookup-id n aignet))))
                   n)))

     ;; (defthm not-output-when-aignet-litp
     ;;   (implies (aignet-litp x aignet)
     ;;            (not (equal (ctype (stype (car (lookup-id (lit-id x) aignet))))
     ;;                        :output)))
     ;;   :hints(("Goal" :in-theory (enable aignet-litp))))

     
     (defthm not-output-of-lookup-lit
       (implies (aignet-extension-p aignet aignet2)
                (not (equal (ctype (stype (car (lookup-id (lit-id (aignet-lit-fix lit aignet2))
                                                          aignet))))
                            :output))))))

  (defthm aignet-levels-correct-up-to-of-aignet-record-levels-aux
    (implies (aignet-levels-correct-up-to n aignet aignet-levels)
             (aignet-levels-correct-up-to (+ 1 (fanin-count aignet))
                                          aignet
                                          (aignet-record-levels-aux n aignet aignet-levels)))
    :hints (("goal" :induct (aignet-record-levels-aux n aignet aignet-levels)
             :expand ((aignet-node-level n aignet)))))

  (defthm aignet-levels-correct-of-aignet-record-levels-aux
    (aignet-levels-correct-up-to (+ 1 (fanin-count aignet))
                                 aignet
                                 (aignet-record-levels-aux 0 aignet aignet-levels))))


(define aignet-record-levels (aignet
                              aignet-levels)
  :parents (utilities)
  :short "Records the level of each node in aignet-levels, where combinational
          inputs and constants have level 0 and a node has level n+1 if its children
          have maximum level n."
  :long "<p>Does not record a level value for combinational outputs.  Look up the
         level of its fanin node instead.</p>"
  :returns (aignet-levels
            (< (fanin-count aignet)
               (len aignet-levels))
            :rule-classes :linear)
  (b* ((aignet-levels (resize-u32 (num-fanins aignet) aignet-levels)))
    (aignet-record-levels-aux 0 aignet aignet-levels))
  ///
  (defthm aignet-levels-correct-of-aignet-record-levels
    (aignet-levels-correct-up-to (+ 1 (fanin-count aignet))
                                 aignet
                                 (aignet-record-levels aignet aignet-levels))))

  
