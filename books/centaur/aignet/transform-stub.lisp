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

(include-book "raw-copy")
(include-book "semantics")

(local (in-theory (disable w)))

(encapsulate
  (((apply-comb-transform aignet aignet2 * state) => (mv aignet2 state)
    :guard t :formals (aignet aignet2 config state)))
  (local (define apply-comb-transform (aignet aignet2 config state)
           :returns (mv new-aignet2 new-state)
           (Declare (ignore config aignet2))
           (b* ((aignet2 (non-exec (node-list-fix aignet))))
             (mv aignet2 state))))

  (local (in-theory (enable apply-comb-transform)))
  
  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (<fn> aignet nil config state))))

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret <fn>-comb-equivalent
    (comb-equiv new-aignet2 aignet))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state)))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet2 new-state) <call>)))


(define apply-comb-transform! (aignet
                               transform
                               state)
  :returns (mv new-aignet new-state)
  :enabled t
  (mbe :logic (non-exec (apply-comb-transform aignet nil transform state))
       :exec (b* (((acl2::local-stobjs aignet2)
                   (mv aignet aignet2 state))
                  ((mv aignet2 state) (apply-comb-transform aignet aignet2 transform state))
                  ((mv aignet aignet2) (swap-stobjs aignet aignet2)))
               (mv aignet aignet2 state))))

(define apply-comb-transforms! (aignet
                                transforms
                                state)
  :returns (mv new-aignet new-state)
  (b* (((when (atom transforms))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv aignet state)))
       ((mv aignet state) (apply-comb-transform! aignet (car transforms) state)))
    (apply-comb-transforms! aignet (cdr transforms) state))
  ///
  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret <fn>-comb-equivalent
    (comb-equiv new-aignet aignet))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state)))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet new-state) <call>)))

(define apply-comb-transforms-in-place (aignet aignet2 transforms state)
  :returns (mv new-aignet new-aignet2 new-state)
  (b* (((when (atom transforms))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet))
             (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv aignet aignet2 state))))
    (mbe :logic (non-exec
                 (b* (((mv new-aignet state) (apply-comb-transform aignet nil (car transforms) state)))
                   (apply-comb-transforms-in-place new-aignet aignet (cdr transforms) state)))
         :exec (b* (((mv aignet2 state) (apply-comb-transform aignet aignet2 (car transforms) state))
                    ((mv aignet aignet2) (swap-stobjs aignet aignet2)))
                 (apply-comb-transforms-in-place aignet aignet2 (cdr transforms) state))))
  ///
  (defret <fn>-equals-apply-comb-transforms!
    (b* (((mv new-aignet-spec new-state-spec) (apply-comb-transforms! aignet transforms state)))
      (and (equal new-aignet new-aignet-spec)
           (equal new-state new-state-spec)))
    :hints(("Goal" :in-theory (enable apply-comb-transforms!))))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet new-aignet2 new-state) <call>)
    :hints(("Goal" :in-theory (disable <fn>-equals-apply-comb-transforms!)))))

(defstobj-clone aignet3 aignet :suffix "3")

(define apply-comb-transforms (aignet
                               aignet2
                               transforms
                               state)
  :returns (mv new-aignet2 new-state)
  :guard-hints (("goal" :expand ((apply-comb-transforms! aignet transforms state))))
  (b* (((unless (consp transforms))
        (b* ((aignet2 (aignet-raw-copy aignet aignet2)))
          (mv aignet2 state))))
    (mbe :logic (non-exec (apply-comb-transforms! aignet transforms state))
         :exec (b* (((mv aignet2 state) (apply-comb-transform aignet aignet2 (car transforms) state))
                    ((acl2::local-stobjs aignet3)
                     (mv aignet2 aignet3 state)))
                 (apply-comb-transforms-in-place aignet2 aignet3 (cdr transforms) state))))
  ///
  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (let ((aignet2 nil)) <call>))))

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret <fn>-comb-equivalent
    (comb-equiv new-aignet2 aignet))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state)))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet2 new-state) <call>)))





(encapsulate
  (((apply-n-output-comb-transform * aignet aignet2 * state) => (mv aignet2 state)
    :guard (and (natp n) (<= n (num-outs aignet)))
    :formals (n aignet aignet2 config state)))

  (local (define apply-n-output-comb-transform ((n natp) aignet aignet2 config state)
           :guard (<= n (num-outs aignet))
           :returns (mv new-aignet2 new-state)
           (Declare (ignore n config aignet2))
           (b* ((aignet2 (non-exec (node-list-fix aignet))))
             (mv aignet2 state))))

  (local (in-theory (enable apply-n-output-comb-transform)))
  
  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (<fn> n aignet nil config state))))

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret <fn>-outputs-equivalent
    (implies (< (nfix i) (nfix n))
             (equal (output-eval i invals regvals new-aignet2)
                    (output-eval i invals regvals aignet))))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state)))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet2 new-state) <call>)))


(define apply-n-output-comb-transform! ((n natp)
                                   aignet
                                   transform
                                   state)
  :guard (<= n (num-outs aignet))
  :returns (mv new-aignet new-state)
  :enabled t
  (mbe :logic (non-exec (apply-n-output-comb-transform n aignet nil transform state))
       :exec (b* (((acl2::local-stobjs aignet2)
                   (mv aignet aignet2 state))
                  ((mv aignet2 state) (apply-n-output-comb-transform n aignet aignet2 transform state))
                  ((mv aignet aignet2) (swap-stobjs aignet aignet2)))
               (mv aignet aignet2 state))))

(define apply-n-output-comb-transforms! ((n natp)
                                    aignet
                                    transforms
                                    state)
  :guard (<= n (num-outs aignet))  
  :returns (mv new-aignet new-state)
  (b* (((when (atom transforms))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv aignet state)))
       ((mv aignet state) (apply-n-output-comb-transform! n aignet (car transforms) state)))
    (apply-n-output-comb-transforms! n aignet (cdr transforms) state))
  ///
  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret <fn>-outputs-equivalent
    (implies (< (nfix i) (nfix n))
             (equal (output-eval i invals regvals new-aignet)
                    (output-eval i invals regvals aignet))))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state)))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet new-state) <call>)))

(define apply-n-output-comb-transforms-in-place ((n natp) aignet aignet2 transforms state)
  :guard (<= n (num-outs aignet))
  :returns (mv new-aignet new-aignet2 new-state)
  (b* (((when (atom transforms))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet))
             (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv aignet aignet2 state))))
    (mbe :logic (non-exec
                 (b* (((mv new-aignet state) (apply-n-output-comb-transform n aignet nil (car transforms) state)))
                   (apply-n-output-comb-transforms-in-place n new-aignet aignet (cdr transforms) state)))
         :exec (b* (((mv aignet2 state) (apply-n-output-comb-transform n aignet aignet2 (car transforms) state))
                    ((mv aignet aignet2) (swap-stobjs aignet aignet2)))
                 (apply-n-output-comb-transforms-in-place n aignet aignet2 (cdr transforms) state))))
  ///
  (defret <fn>-equals-apply-n-output-comb-transforms!
    (b* (((mv new-aignet-spec new-state-spec) (apply-n-output-comb-transforms! n aignet transforms state)))
      (and (equal new-aignet new-aignet-spec)
           (equal new-state new-state-spec)))
    :hints(("Goal" :in-theory (enable apply-n-output-comb-transforms!))))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet new-aignet2 new-state) <call>)
    :hints(("Goal" :in-theory (disable <fn>-equals-apply-n-output-comb-transforms!)))))

(define apply-n-output-comb-transforms ((n natp) aignet aignet2 transforms state)
  :guard (<= n (num-outs aignet))
  :returns (mv new-aignet2 new-state)
  :guard-hints (("goal" :expand ((apply-n-output-comb-transforms! n aignet transforms state))))
  (b* (((unless (consp transforms))
        (b* ((aignet2 (aignet-raw-copy aignet aignet2)))
          (mv aignet2 state))))
    (mbe :logic (non-exec (apply-n-output-comb-transforms! n aignet transforms state))
         :exec (b* (((mv aignet2 state) (apply-n-output-comb-transform n aignet aignet2 (car transforms) state))
                    ((acl2::local-stobjs aignet3)
                     (mv aignet2 aignet3 state)))
                 (apply-n-output-comb-transforms-in-place n aignet2 aignet3 (cdr transforms) state))))
  ///
  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (let ((aignet2 nil)) <call>))))

  (defret num-ins-of-<fn>
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-<fn>
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-<fn>
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret <fn>-outputs-equivalent
    (implies (< (nfix i) (nfix n))
             (equal (output-eval i invals regvals new-aignet2)
                    (output-eval i invals regvals aignet))))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state)))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet2 new-state) <call>)))


