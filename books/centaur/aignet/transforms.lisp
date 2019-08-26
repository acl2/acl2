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
   prune-config))

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
           (w state))))

(define apply-comb-transform! ((aignet)
                               (transform comb-transform-p)
                               (state))
  :returns (mv new-aignet new-state)
  (b* ((name (comb-transform->name transform)))
    (time$
     (b* (((mv aignet state)
           (case (tag transform)
             (:balance-config (b* ((aignet (balance! aignet transform)))
                                (mv aignet state)))
             (:fraig-config (fraig! aignet transform state))
             (:rewrite-config (b* ((aignet (rewrite! aignet transform)))
                                (mv aignet state)))
             (:obs-constprop-config (obs-constprop! aignet transform state))
             (:observability-config (observability-fix! aignet transform state))
             (:constprop-config (b* ((aignet (constprop! aignet transform)))
                                  (mv aignet state)))
             (:snapshot-config (b* ((state (aignet-write-aiger (snapshot-config->filename transform)
                                                               aignet state)))
                                 (mv aignet state)))
             (:prune-config (b* ((aignet (prune! aignet transform)))
                              (mv aignet state)))
             (otherwise (abc-comb-simplify! aignet transform state))))
          (- (print-aignet-stats name aignet)))
       (mv aignet state))
     :msg "~s0 transform: ~st seconds, ~sa bytes.~%"
     :args (list name)))
  ///

  (defret num-ins-of-apply-comb-transform!
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-regs-of-apply-comb-transform!
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret num-outs-of-apply-comb-transform!
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret apply-comb-transform!-comb-equivalent
    (comb-equiv new-aignet aignet))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))


(fty::deflist comb-transformlist :elt-type comb-transform :true-listp t)

(define apply-comb-transforms-aux ((aignet)
                                   (aignet2)
                                   (transforms comb-transformlist-p
                                               "executed in reverse order!")
                                   (state))
  :guard (consp transforms)
  :returns (mv new-aignet2 new-state)
  (if (atom (cdr transforms))
      (apply-comb-transform aignet aignet2 (car transforms) state)
    (b* (((local-stobjs aignet-tmp)
          (mv aignet-tmp aignet2 state))
         ;; Doing it this way is awkward, but makes it so that we don't keep
         ;; around a stack of completed aignets, just a stack of empty ones:
         ;; each call of apply-comb-transforms-aux only populates its input
         ;; aignet2 as its last step, and all the previous transforms are done
         ;; in a recursive call that writes to an empty local aignet.
         ((mv aignet-tmp state)
          (apply-comb-transforms-aux aignet aignet-tmp (cdr transforms) state))
         ((mv aignet2 state)
          (apply-comb-transform aignet-tmp aignet2 (car transforms) state)))
      (mv aignet-tmp aignet2 state))))




(define apply-comb-transforms-logic ((aignet)
                                     (transforms comb-transformlist-p)
                                     (state))
  ;; :verify-guards nil
  :returns (mv new-aignet new-state)
  (b* (((when (atom transforms)) (mv aignet state))
       ((mv aignet state) (non-exec (apply-comb-transform aignet nil (car transforms) state))))
    (apply-comb-transforms-logic aignet (cdr transforms) state))
  ///
  (defthm apply-comb-transforms-logic-of-append-transforms
    (equal (apply-comb-transforms-logic aignet (append x y) state)
           (b* (((mv next state) (apply-comb-transforms-logic aignet x state)))
             (apply-comb-transforms-logic next y state))))

  (defret num-ins-of-apply-comb-transforms-logic
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-regs-of-apply-comb-transforms-logic
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret num-outs-of-apply-comb-transforms-logic
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret apply-comb-transforms-logic-comb-equivalent
    (comb-equiv new-aignet aignet))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))






(define apply-comb-transforms ((aignet)
                               (aignet2)
                               (transforms comb-transformlist-p)
                               (state))
  :short "Apply a sequence of combinational transforms to a network and return
          a transformed copy, preserving the original network."
  :long "<p>See @(see apply-comb-transforms!) for a version that overwrites the original network.</p>"
  :verify-guards nil
  :enabled t
  :returns (mv new-aignet2 new-state)
  (if (atom transforms)
      (b* ((aignet2 (aignet-raw-copy aignet aignet2)))
        (mv aignet2 state))
    (mbe :logic (non-exec (apply-comb-transforms-logic aignet transforms state))
         :exec (apply-comb-transforms-aux aignet aignet2 (acl2::rev transforms) state)))
  ///
  

  (local (defthmd mv-list-of-apply-comb-transform
           (equal (list (mv-nth 0 (apply-comb-transform aignet aignet2 transform state))
                        (mv-nth 1 (apply-comb-transform aignet aignet2 transform state)))
                  (apply-comb-transform aignet aignet2 transform state))
           :hints(("Goal" :in-theory (enable apply-comb-transform fraig)))))

  (defthm apply-comb-transforms-aux-is-apply-comb-transforms-logic
    (implies (consp transforms)
             (equal (apply-comb-transforms-aux aignet aignet2 transforms state)
                    (apply-comb-transforms-logic aignet (acl2::rev transforms) state)))
    :hints(("Goal" :in-theory (enable apply-comb-transforms-aux acl2::rev
                                      apply-comb-transforms-logic)
            :induct (apply-comb-transforms-aux aignet aignet2 transforms state)
            ;; :expand ((apply-comb-transforms-aux aignet aignet2 (acl2::rev transforms) state))
            )
           (and stable-under-simplificationp
                '(:in-theory (enable mv-list-of-apply-comb-transform)))))

  (verify-guards apply-comb-transforms
    :hints (("goal" :expand ((apply-comb-transforms-logic aignet nil state)))))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))



(define apply-comb-transforms!-rec ((aignet)
                                (transforms comb-transformlist-p)
                                (state))
  :returns (mv new-aignet new-state)
  (if (atom transforms)
      (mv aignet state)
    (b* (((mv aignet state) (apply-comb-transform! aignet (car transforms) state)))
      (apply-comb-transforms!-rec aignet (cdr transforms) state)))
  ///

  (defret num-ins-of-apply-comb-transforms!-rec
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-regs-of-apply-comb-transforms!-rec
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret num-outs-of-apply-comb-transforms!-rec
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret apply-comb-transforms!-rec-comb-equivalent
    (comb-equiv new-aignet aignet))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state))))

(define apply-comb-transforms! ((aignet)
                                (transforms comb-transformlist-p)
                                (state))
  :parents (apply-comb-transforms)
  :short "Apply a sequence of combinational transforms to a network and return
          the transformed network, overwriting the original network."
  :long "<p>See @(see apply-comb-transforms) for a version that preserves the original network.</p>"
  :returns (mv new-aignet new-state)
  :enabled t
  (prog2$ (print-aignet-stats "Input" aignet)
          (apply-comb-transforms!-rec aignet transforms state)))

(defconst *default-transforms*
  (list (make-balance-config) *fraig-default-config*))



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

(define aignet-comb-transform!-default (aignet config state)
  :returns (mv new-aignet new-state)
  (if (comb-transformlist-p config)
      (time$ (apply-comb-transforms! aignet config state)
             :msg "All transforms: ~st seconds, ~sa bytes.~%")
    (prog2$ (er hard? 'aignet-comb-transform!-default
                "Config must satisfy ~x0, but did not: ~x1"
                'comb-transformlist-p config)
            (mv aignet state)))
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
           (w state))))

(defattach aignet-comb-transform!-stub aignet-comb-transform!-default)
