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
(include-book "aignet-absstobj")



(define aignet-rollback-one-gate (aignet)
  :guard (and (equal (num-nxsts aignet) 0)
              (equal (num-outs aignet) 0)
              (let ((id (1- (num-fanins aignet))))
                (equal (id->type id aignet) (gate-type))))
  :prepwork ((local (defthm stype-count-of-lookup-id-of-fanin-count
                      (implies (not (equal (ctype stype) :output))
                               (equal (stype-count stype (lookup-id (fanin-count aignet) aignet))
                                      (stype-count stype aignet)))
                      :hints(("Goal" :induct (len aignet)
                              :in-theory (e/d (len fanin-node-p)
                                               (fanin-count-of-cdr-strong
                                                lookup-id-in-extension-inverse))
                              :expand ((fanin-count aignet)
                                       (:free (n) (lookup-id n aignet))
                                       (stype-count stype aignet))))))
             (local (defthm ctype-gate-implies-pi-count-same
                      (implies (and (equal (ctype (stype (car (lookup-id (fanin-count aignet) aignet)))) :gate)
                                    (not (equal (ctype stype) :gate))
                                    (not (equal (ctype stype) :output)))
                               (equal (stype-count stype (lookup-id (+ -1 (fanin-count aignet)) aignet))
                                      (stype-count stype aignet)))
                      :hints (("goal" :induct (len aignet)
                               :in-theory (e/d (len fanin-node-p)
                                               (fanin-count-of-cdr-strong
                                                lookup-id-in-extension-inverse))
                               :expand ((stype-count stype aignet)
                                        (fanin-count aignet)
                                        (:free (n) (lookup-id n aignet))
                                        ;; (AIGNET::STYPE-COUNT
                                        ;;  AIGNET::STYPE
                                        ;;  (AIGNET::LOOKUP-ID (AIGNET::FANIN-COUNT (CDR ACL2::AIGNET))
                                        ;;                     (CDR ACL2::AIGNET)))
                                        ))))))
  ;; :guard-hints (("Goal" :expand ((stype-count :pi aignet)
  ;;                                (stype-count :reg aignet)
  ;;                                ;; (lookup-id (fanin-count aignet) aignet)
  ;;                                )))
  (aignet-rollback (1- (num-fanins aignet)) aignet))
