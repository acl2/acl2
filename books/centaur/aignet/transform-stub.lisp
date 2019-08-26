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

(encapsulate
  (((aignet-comb-transform!-stub aignet * state) => (mv aignet state)
    :guard t :formals (aignet config state)))

  (local (define aignet-comb-transform!-stub (aignet config state)
           :returns (mv new-aignet new-state)
           (Declare (ignore config))
           (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                             :exec aignet)))
             (mv aignet state))))

  (local (in-theory (enable aignet-comb-transform!-stub)))

  (defret comb-equiv-of-<fn>
    (comb-equiv new-aignet
                aignet))

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(encapsulate
  (((aignet-comb-transform-stub aignet aignet2 * state) => (mv aignet2 state)
    :guard t :formals (aignet aignet2 config state)))

  (local (define aignet-comb-transform-stub (aignet aignet2 config state)
           :returns (mv new-aignet2 new-state)
           (Declare (ignore config aignet2))
           (b* ((aignet2 (non-exec (node-list-fix aignet))))
             (mv aignet2 state))))

  (local (in-theory (enable aignet-comb-transform-stub)))

  (defret comb-equiv-of-<fn>
    (comb-equiv new-aignet2
                aignet))

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))
