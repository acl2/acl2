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

(include-book "rewrite")
(include-book "fraig")
(include-book "balance")
(include-book "obs-constprop")
(include-book "constprop")
(include-book "abc-wrappers")
(include-book "transform-stub")
(include-book "internal-observability-super")

(defxdoc aignet-comb-transforms
  :parents (aignet)
  :short "Aignet transforms that simplify the network while preserving combinational equivalence"
  :long "<p>The functions @(see apply-comb-transforms) and @(see
apply-comb-transforms!) may be used to apply several transforms to an aignet
network, each of which preserves combinational equivalence with the original
network.  The transforms are chosen by listing several @(see comb-transform)
objects, each of which is a configuration object for one of the supported
transforms.  The currently supported transforms are:</p>
<ul>
<li>@(see balance)</li>
<li>@(see fraig)</li>
<li>@(see rewrite)</li>
<li>@(see obs-constprop)</li>
<li>@(see observability-fix)</li>
<li>@(see constprop)</li>
<li>@(see prune)</li>
<li>@(see abc-comb-simplify)</li>
</ul>

<p>An additional \"transform\" that simply writes a snapshot of the network to
an aiger file is also supported.</p>")

(local (xdoc::set-default-parents aignet-comb-transforms))

(fty::defprod snapshot-config
  :parents (comb-transform)
  :short "Aignet transform that returns the same network and simply writes a snapshot
          into an aiger file for debugging."
  ((filename stringp))
  :layout :tree
  :tag :snapshot-config)

(fty::defprod prune-config
  :parents (comb-transform)
  :short "Aignet transform that prunes out unused logic in the network."
  ((gatesimp gatesimp-p))
  :layout :tree
  :tag :prune-config)

(define prune ((aignet  "Input aignet")
               (aignet2 "New aignet -- will be emptied")
               (config prune-config-p
                       "Settings for the transform"))
  :parents (aignet-comb-transforms)
  :returns new-aignet2
  :short "Apply combinational pruning to remove unused nodes in the input network."
  :long "<p>Pruning simply marks the nodes that are in the fanin cones of the
combinational outputs and selectively copies only those nodes (but including
all combinational inputs).  This transform is usually redundant because most
transforms result in pruned networks.  One use is to restore xor nodes after
applying the @(see abc-comb-simplify) transform, since the aiger format used
for translating between ABC and aignet does not support xors.</p>"
  (aignet-prune-comb aignet aignet2 (prune-config->gatesimp config))
  ///
  (defret num-ins-of-prune
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-prune
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-prune
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret prune-comb-equivalent
    (comb-equiv new-aignet2 aignet))

  (defthm normalize-input-of-prune
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (prune aignet aignet2 config)
                    (prune aignet nil config)))))


(define prune! ((aignet  "Input aignet -- will be replaced with transformation result")
                (config prune-config-p))
  :guard-debug t
  :returns new-aignet
  :parents (prune)
  :short "Like @(see prune), but overwrites the original network instead of returning a new one."
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet aignet-tmp))
       (aignet-tmp (aignet-raw-copy aignet aignet-tmp))
       (aignet (aignet-prune-comb aignet-tmp aignet (prune-config->gatesimp config))))
    (mv aignet aignet-tmp))
  ///
  (defret num-ins-of-prune!
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-regs-of-prune!
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret num-outs-of-prune!
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret prune!-comb-equivalent
    (comb-equiv new-aignet aignet)))


(fty::deftranssum comb-transform
  :short "Configuration object for any combinational transform supported by @(see apply-comb-transforms)."
  (balance-config
   fraig-config
   rewrite-config
   abc-comb-simp-config
   obs-constprop-config
   observability-config
   constprop-config
   snapshot-config
   prune-config
   unreachability-config))

(define comb-transform->name ((x comb-transform-p))
  :returns (name stringp :rule-classes :type-prescription)
  (case (tag (comb-transform-fix x))
    (:balance-config "Balance")
    (:fraig-config "Fraig")
    (:rewrite-config "Rewrite")
    (:obs-constprop-config "Observability")
    (:observability-config "Observability")
    (:constprop-config "Constprop")
    (:snapshot-config "Snapshot")
    (:prune-config "Prune")
    (:unreachability-config "Unreachability")
    (t "Abc simplify")))



(local (in-theory (disable w)))

(define apply-comb-transform ((aignet)
                              (aignet2)
                              (transform comb-transform-p)
                              (state))
  :returns (mv new-aignet2 new-state)
  (b* ((name (comb-transform->name transform)))
    (time$
     (b* (((mv aignet2 state)
           (case (tag transform)
             (:balance-config (b* ((aignet2 (balance aignet aignet2 transform)))
                                (mv aignet2 state)))
             (:fraig-config (fraig aignet aignet2 transform state))
             (:rewrite-config (b* ((aignet2 (rewrite aignet aignet2 transform)))
                                (mv aignet2 state)))
             (:obs-constprop-config (obs-constprop aignet aignet2 transform state))
             (:observability-config (observability-fix aignet aignet2 transform state))
             (:constprop-config (b* ((aignet2 (constprop aignet aignet2 transform)))
                                  (mv aignet2 state)))
             (:snapshot-config (b* ((state (aignet-write-aiger (snapshot-config->filename transform)
                                                               aignet state))
                                    (aignet2 (aignet-raw-copy aignet aignet2)))
                                 (mv aignet2 state)))
             (:prune-config (b* ((aignet2 (prune aignet aignet2 transform)))
                              (mv aignet2 state)))
             (:unreachability-config (b* ((aignet2 (unreachability aignet aignet2 transform)))
                                      (mv aignet2 state)))
             (otherwise (abc-comb-simplify aignet aignet2 transform state))))
          (- (print-aignet-stats name aignet2)))
       (mv aignet2 state))
     :msg "~s0 transform: ~st seconds, ~sa bytes.~%"
     :args (list name)))
  ///
  (defthm normalize-inputs-of-apply-comb-transform
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (apply-comb-transform aignet aignet2 transform state)
                    (apply-comb-transform aignet nil transform state))))

  (defret num-ins-of-apply-comb-transform
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-apply-comb-transform
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-apply-comb-transform
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret apply-comb-transform-comb-equivalent
    (comb-equiv new-aignet2 aignet))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state)))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet2 new-state) <call>)))

(define apply-comb-transform! ((aignet)
                               (transform comb-transform-p)
                               (state))
  :returns (mv new-aignet new-state)
  :enabled t
  (mbe :logic (non-exec (apply-comb-transform aignet nil transform state))
       :exec (b* (((acl2::local-stobjs aignet2)
                   (mv aignet aignet2 state))
                  ((mv aignet2 state) (apply-comb-transform aignet aignet2 transform state))
                  ((mv aignet aignet2) (swap-stobjs aignet aignet2)))
               (mv aignet aignet2 state))))

(fty::deflist comb-transformlist :elt-type comb-transform :true-listp t)


(define apply-comb-transforms! (aignet
                                (transforms comb-transformlist-p)
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

(define apply-comb-transforms-in-place (aignet aignet2 
                                               (transforms comb-transformlist-p)
                                               state)
  :returns (mv new-aignet new-aignet2 new-state)
  (b* (((when (atom transforms))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet))
             (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv aignet aignet2 state)))
       ((mv aignet aignet2 state)
        (mbe :logic (non-exec
                     (mv (mv-nth 0 (apply-comb-transform aignet nil (car transforms) state))
                         aignet
                         (mv-nth 1 (apply-comb-transform aignet nil (car transforms) state))))
             :exec (b* (((mv aignet2 state) (apply-comb-transform aignet aignet2 (car transforms) state))
                        ((mv aignet aignet2) (swap-stobjs aignet aignet2)))
                     (mv aignet aignet2 state)))))
    (apply-comb-transforms-in-place aignet aignet2 (cdr transforms) state))
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
                               (transforms comb-transformlist-p)
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


(define aignet-comb-transform-default (aignet aignet2 config state)
  :returns (mv new-aignet2 new-state)
  (if (comb-transformlist-p config)
      (time$ (apply-comb-transforms aignet aignet2 config state)
             :msg "All transforms: ~st seconds, ~sa bytes.~%")
    (prog2$ (er hard? 'aignet-comb-transform-default
                "Config must satisfy ~x0, but did not: ~x1"
                'comb-transformlist-p config)
            (b* ((aignet2 (aignet-raw-copy aignet aignet2)))
              (mv aignet2 state))))
  ///
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
           (w state))))

(defattach aignet-comb-transform-stub aignet-comb-transform-default)




(defxdoc aignet-n-output-comb-transforms
  :parents (aignet)
  :short "Aignet transforms that simplify the network while preserving combinational equivalence of the first N primary outputs."
  :long "<p>The functions @(see apply-n-output-comb-transforms) and @(see
apply-n-output-comb-transforms!) may be used to apply several transforms to an aignet
network, each of which preserves combinational equivalence with the original
network on the first N primary outputs.  Generally the rest of the outputs and the register nextstates may not be equivalent, but there may be heuristic uses for them.  The transforms are chosen by listing several @(see n-output-comb-transform)
objects, each of which is a configuration object for one of the supported
transforms.  The currently supported transforms include the @(see aignet-comb-transforms), which preserve complete cominbational equivalence, and an n-output unreachability transform.</p>
")


(fty::deftranssum n-output-comb-transform
  :short "Configuration object for any combinational transform supported by @(see apply-comb-transforms)."
  (comb-transform
   n-outputs-unreachability-config))

(define n-output-comb-transform->name ((x n-output-comb-transform-p))
  :returns (name stringp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable n-output-comb-transform-p)))
  (case (tag (n-output-comb-transform-fix x))
    (:n-outputs-unreachability-config "N-output Unreachability")
    (otherwise (comb-transform->name x))))


(define apply-n-output-comb-transform ((n natp)
                                       (aignet)
                                       (aignet2)
                                       (transform n-output-comb-transform-p)
                                       (state))
  :guard (<= n (num-outs aignet))
  :returns (mv new-aignet2 new-state)
  (b* ((name (n-output-comb-transform->name transform)))
    (time$
     (b* (((mv aignet2 state)
           (case (tag transform)
             (:balance-config (b* ((aignet2 (balance aignet aignet2 transform)))
                                (mv aignet2 state)))
             (:fraig-config (fraig aignet aignet2 transform state))
             (:rewrite-config (b* ((aignet2 (rewrite aignet aignet2 transform)))
                                (mv aignet2 state)))
             (:obs-constprop-config (obs-constprop aignet aignet2 transform state))
             (:observability-config (observability-fix aignet aignet2 transform state))
             (:constprop-config (b* ((aignet2 (constprop aignet aignet2 transform)))
                                  (mv aignet2 state)))
             (:snapshot-config (b* ((state (aignet-write-aiger (snapshot-config->filename transform)
                                                               aignet state))
                                    (aignet2 (aignet-raw-copy aignet aignet2)))
                                 (mv aignet2 state)))
             (:prune-config (b* ((aignet2 (prune aignet aignet2 transform)))
                              (mv aignet2 state)))
             (:unreachability-config (b* ((aignet2 (unreachability aignet aignet2 transform)))
                                      (mv aignet2 state)))
             (:n-outputs-unreachability-config
              (b* ((aignet2 (n-outputs-unreachability n aignet aignet2 transform)))
                (mv aignet2 state)))
             (otherwise (abc-comb-simplify aignet aignet2 transform state))))
          (- (print-aignet-stats name aignet2)))
       (mv aignet2 state))
     :msg "~s0 transform: ~st seconds, ~sa bytes.~%"
     :args (list name)))
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

(define apply-n-output-comb-transform! ((n natp)
                                        (aignet)
                                        (transform n-output-comb-transform-p)
                                        (state))
  :guard (<= n (num-outs aignet))
  :returns (mv new-aignet new-state)
  :enabled t
  (mbe :logic (non-exec (apply-n-output-comb-transform n aignet nil transform state))
       :exec (b* (((acl2::local-stobjs aignet2)
                   (mv aignet aignet2 state))
                  ((mv aignet2 state) (apply-n-output-comb-transform n aignet aignet2 transform state))
                  ((mv aignet aignet2) (swap-stobjs aignet aignet2)))
               (mv aignet aignet2 state))))


(fty::deflist n-output-comb-transformlist :elt-type n-output-comb-transform :true-listp t)

(define apply-n-output-comb-transforms! ((n natp)
                                         aignet
                                         (transforms n-output-comb-transformlist-p)
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

(define apply-n-output-comb-transforms-in-place ((n natp)
                                                 aignet aignet2 
                                                 (transforms n-output-comb-transformlist-p)
                                                 state)
  :guard (<= n (num-outs aignet))
  :returns (mv new-aignet new-aignet2 new-state)
  (b* (((when (atom transforms))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet))
             (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv aignet aignet2 state)))
       ((mv aignet aignet2 state)
        (mbe :logic (non-exec
                     (mv (mv-nth 0 (apply-n-output-comb-transform n aignet nil (car transforms) state))
                         aignet
                         (mv-nth 1 (apply-n-output-comb-transform n aignet nil (car transforms) state))))
             :exec (b* (((mv aignet2 state) (apply-n-output-comb-transform n aignet aignet2 (car transforms) state))
                        ((mv aignet aignet2) (swap-stobjs aignet aignet2)))
                     (mv aignet aignet2 state)))))
    (apply-n-output-comb-transforms-in-place n aignet aignet2 (cdr transforms) state))
  ///
  (defret <fn>-equals-apply-n-output-comb-transforms!
    (b* (((mv new-aignet-spec new-state-spec) (apply-n-output-comb-transforms! n aignet transforms state)))
      (and (equal new-aignet new-aignet-spec)
           (equal new-state new-state-spec)))
    :hints(("Goal" :in-theory (enable apply-n-output-comb-transforms!))))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet new-aignet2 new-state) <call>)
    :hints(("Goal" :in-theory (disable <fn>-equals-apply-n-output-comb-transforms!)))))

(define apply-n-output-comb-transforms ((n natp)
                               aignet
                               aignet2
                               (transforms n-output-comb-transformlist-p)
                               state)
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



(define aignet-n-output-comb-transform-default ((n natp) aignet aignet2 config state)
  :guard (<= n (num-outs aignet))
  :returns (mv new-aignet2 new-state)
  (if (n-output-comb-transformlist-p config)
      (time$ (apply-n-output-comb-transforms n aignet aignet2 config state)
             :msg "All transforms: ~st seconds, ~sa bytes.~%")
    (prog2$ (er hard? 'aignet-n-output-comb-transform-default
                "Config must satisfy ~x0, but did not: ~x1"
                'n-output-comb-transformlist-p config)
            (b* ((aignet2 (aignet-raw-copy aignet aignet2)))
              (mv aignet2 state))))
  ///
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
           (w state))))

(defattach aignet-n-output-comb-transform-stub aignet-n-output-comb-transform-default)
