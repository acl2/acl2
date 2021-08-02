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
(include-book "unreachability")
(include-book "dom-supergate-sweep")

(defxdoc aignet-comb-transforms
  :parents (aignet-transforms)
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
  :parents (aignet-comb-transforms)
  (balance-config
   fraig-config
   rewrite-config
   abc-comb-simp-config
   obs-constprop-config
   observability-config
   constprop-config
   snapshot-config
   prune-config
   unreachability-config
   dom-supergates-sweep-config))

(fty::deflist comb-transformlist :elt-type comb-transform :true-listp t)

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
    (:dom-supergates-sweep-config "Observability supergate sweep")
    (t "Abc simplify")))



(local (in-theory (disable w)))

(define apply-comb-transform-default ((aignet)
                                      (aignet2)
                                      (transform)
                                      (state))
  :returns (mv new-aignet2 new-state)
  (b* (((unless (comb-transform-p transform))
        (raise "Bad transform config object; should satisfy ~x1: ~x0~%"
               transform 'comb-transform-p)
        (b* ((aignet2 (aignet-raw-copy aignet aignet2)))
          (mv aignet2 state)))
       (name (comb-transform->name transform)))
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
             (:dom-supergates-sweep-config
              (b* ((aignet2 (dom-supergates-sweep aignet aignet2 transform)))
                (mv aignet2 state)))
             (otherwise (abc-comb-simplify aignet aignet2 transform state))))
          (- (print-aignet-stats name aignet2)))
       (mv aignet2 state))
     :msg "~s0 transform: ~st seconds, ~sa bytes.~%"
     :args (list name)))
  ///
  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (<fn> aignet aignet2 transform state)
                    (<fn> aignet nil transform state))))

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

(defattach apply-comb-transform apply-comb-transform-default)





(defxdoc aignet-n-output-comb-transforms
  :parents (aignet-transforms)
  :short "Aignet transforms that simplify the network while preserving combinational
          equivalence of the first N primary outputs.")


(fty::deftranssum n-output-comb-transform
  :short "Configuration object for any combinational transform supported by @(see apply-comb-transforms)."
  :parents (aignet-n-output-comb-transforms)
  (comb-transform
   n-outputs-unreachability-config
   n-outputs-dom-supergates-sweep-config))

(fty::deflist n-output-comb-transformlist :elt-type n-output-comb-transform :true-listp t)

(define n-output-comb-transform->name ((x n-output-comb-transform-p))
  :returns (name stringp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable n-output-comb-transform-p)))
  (case (tag (n-output-comb-transform-fix x))
    (:n-outputs-unreachability-config "N-output Unreachability")
    (:n-outputs-dom-supergates-sweep-config "N-output observability supergate sweep")
    (otherwise (comb-transform->name x))))


(define apply-n-output-comb-transform-default ((n natp)
                                               (aignet)
                                               (aignet2)
                                               (transform)
                                               (state))
  :guard (<= n (num-outs aignet))
  :returns (mv new-aignet2 new-state)
  (b* (((unless (n-output-comb-transform-p transform))
        (raise "Bad transform config object; should satisfy ~x1: ~x0~%"
               transform 'n-output-comb-transform-p)
        (b* ((aignet2 (aignet-raw-copy aignet aignet2)))
          (mv aignet2 state)))
       (name (n-output-comb-transform->name transform)))
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
             (:dom-supergates-sweep-config
              (b* ((aignet2 (dom-supergates-sweep aignet aignet2 transform)))
                (mv aignet2 state)))
             (:n-outputs-unreachability-config
              (b* ((aignet2 (n-outputs-unreachability n aignet aignet2 transform)))
                (mv aignet2 state)))
             (:n-outputs-dom-supergates-sweep-config
              (b* ((aignet2 (n-outputs-dom-supergates-sweep n aignet aignet2 transform)))
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



(defattach apply-n-output-comb-transform apply-n-output-comb-transform-default)


(defxdoc aignet-m-assumption-n-output-transforms
  :parents (aignet-transforms)
  :short "Aignet transforms that simplify the network while preserving combinational
          equivalence of the first M primary outputs and combinational equivalence
          when assuming the first M primary outputs true on the next N primary
          outputs.")



(fty::deftranssum m-assumption-n-output-comb-transform
  :short "Configuration object for any combinational transform supported by @(see
          apply-m-assumption-n-output-output-transform-default)."
  :parents (aignet-m-assumption-n-output-transforms)
  (comb-transform
   n-outputs-unreachability-config
   n-outputs-dom-supergates-sweep-config
   m-assum-n-output-observability-config))

(fty::deflist m-assumption-n-output-comb-transformlist
  :elt-type m-assumption-n-output-comb-transform :true-listp t)

(define m-assumption-n-output-comb-transform->name ((x m-assumption-n-output-comb-transform-p))
  :returns (name stringp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable m-assumption-n-output-comb-transform-p)))
  (case (tag (m-assumption-n-output-comb-transform-fix x))
    (:n-outputs-unreachability-config "N-output Unreachability")
    (:n-outputs-dom-supergates-sweep-config "N-output observability supergate sweep")
    (:m-assum-n-output-observability-config "M-assumption N-output observability")
    (otherwise (comb-transform->name x))))

(define apply-m-assumption-n-output-output-transform-default ((m natp)
                                                             (n natp)
                                                             (aignet)
                                                             (aignet2)
                                                             (transform)
                                                             (state))
  :guard (<= (+ m n) (num-outs aignet))
  :returns (mv new-aignet2 new-state)
  (b* (((unless (m-assumption-n-output-comb-transform-p transform))
        (raise "Bad transform config object; should satisfy ~x1: ~x0~%"
               transform 'm-assumption-n-output-comb-transform-p)
        (b* ((aignet2 (aignet-raw-copy aignet aignet2)))
          (mv aignet2 state)))
       (name (m-assumption-n-output-comb-transform->name transform)))
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
             (:dom-supergates-sweep-config
              (b* ((aignet2 (dom-supergates-sweep aignet aignet2 transform)))
                (mv aignet2 state)))
             (:n-outputs-unreachability-config
              (b* ((aignet2 (n-outputs-unreachability (+ (lnfix m) (lnfix n)) aignet aignet2 transform)))
                (mv aignet2 state)))
             (:n-outputs-dom-supergates-sweep-config
              (b* ((aignet2 (n-outputs-dom-supergates-sweep (+ (lnfix m) (lnfix n)) aignet aignet2 transform)))
                (mv aignet2 state)))
             (:m-assum-n-output-observability-config
              (m-assum-n-output-observability m n aignet aignet2 transform state))
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

  (defret <fn>-eval-assumptions
    (implies (< (nfix i) (nfix m))
             (equal (output-eval i invals regvals new-aignet2)
                    (output-eval i invals regvals aignet))))

  (defret <fn>-eval-conclusion
    (implies (And (< (nfix i) (+ (nfix m) (nfix n)))
                  (equal (conjoin-output-range 0 m invals regvals aignet) 1))
             (equal (output-eval i invals regvals new-aignet2)
                    (output-eval i invals regvals aignet))))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state)))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet2 new-state) <call>)))



(defattach apply-m-assumption-n-output-transform apply-m-assumption-n-output-output-transform-default)
