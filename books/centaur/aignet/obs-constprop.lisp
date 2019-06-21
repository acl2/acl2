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

(include-book "constprop")
(include-book "observability")

(local (include-book "std/lists/resize-list" :dir :system ))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/util/termhints" :dir :system))
(local (include-book "std/lists/nth" :dir :System))

(local (in-theory (disable nth update-nth nfix ifix (tau-system)
                           resize-list
                           acl2::resize-list-when-atom
                           ;; acl2::resize-list-when-empty
                           )))
(local (std::add-default-post-define-hook :fix))

(local (defthm aignet-copies-in-bounds-of-empty
         (aignet-copies-in-bounds nil aignet)
         :hints(("Goal" :in-theory (enable aignet-copies-in-bounds
                                           nth-lit)))))

(defthm aignet-input-copies-in-bounds-of-set-regs-and-ins
  (b* ((copy (aignet-copy-set-ins 0 aignet copy aignet2))
       (copy (aignet-copy-set-regs 0 aignet copy aignet2)))
    (aignet-input-copies-in-bounds copy aignet aignet2))
  :hints(("Goal" :in-theory (enable aignet-input-copies-in-bounds))))

(defthmd aignet-copy-set-ins-of-aignet2-ext
  (implies (and (aignet-extension-binding)
                (<= (num-ins aignet) (num-ins orig)))
           (equal (aignet-copy-set-ins n aignet copy new)
                  (aignet-copy-set-ins n aignet copy orig)))
  :hints(("Goal" :in-theory (enable aignet-copy-set-ins))))

(defthmd aignet-copy-set-regs-of-aignet2-ext
  (implies (and (aignet-extension-binding)
                (<= (num-regs aignet) (num-regs orig)))
           (equal (aignet-copy-set-regs n aignet copy new)
                  (aignet-copy-set-regs n aignet copy orig)))
  :hints(("Goal" :in-theory (enable aignet-copy-set-regs))))

(defthmd aignet-copy-set-ins-of-aignet-ext
  (implies (and (aignet-extension-binding)
                (equal (num-ins orig) (num-ins new)))
           (equal (aignet-copy-set-ins n new copy aignet2)
                  (aignet-copy-set-ins n orig copy aignet2)))
  :hints(("Goal" :in-theory (enable aignet-copy-set-ins))))

(defthmd aignet-copy-set-regs-of-aignet-ext
  (implies (and (aignet-extension-binding)
                (equal (num-regs orig) (num-regs new)))
           (equal (aignet-copy-set-regs n new copy aignet2)
                  (aignet-copy-set-regs n orig copy aignet2)))
  :hints(("Goal" :in-theory (enable aignet-copy-set-regs))))


(defthmd aignet-copy-set-ins-of-aignet2-ext-regs-hack
  (implies (and (aignet-extension-binding)
                (<= (num-regs aignet) (num-regs orig))
                (<= (num-ins aignet) (num-ins orig)))
           (equal (aignet-copy-set-ins n aignet copy new)
                  (aignet-copy-set-ins n aignet copy orig)))
  :hints(("Goal" :in-theory (enable aignet-copy-set-ins))))


(encapsulate nil
  (local (defthm len-equal-0
           (equal (Equal (len x) 0)
                  (not (consp x)))))
  (local (defthm nth-of-bit-list-fix
           (equal (nth n (bit-list-fix x))
                  (if (< (nfix n) (len x))
                      (bfix (nth n x))
                    nil))
           :hints(("Goal" :in-theory (enable nth bit-list-fix)
                   :induct (nth n x)))))
  (defthm bits-equiv-of-bit-list-fix
    (bits-equiv (bit-list-fix x) x)
    :hints(("Goal" :in-theory (enable bits-equiv)))))

(local (in-theory (disable w)))

(define aignet-lit-constprop/observability ((lit litp :type (integer 0 *))
                                            aignet
                                            aignet2
                                            (config observability-config-p)
                                            state)
  :guard (fanin-litp lit aignet)
  :returns (mv (new-lit litp :rule-classes :type-prescription)
               new-aignet2 new-state)
  :prepwork ((local (defthmd less-when-aignet-idp
                      (implies (and (aignet-idp id aignet)
                                    (natp id))
                               (< id (+ 1 (fanin-count aignet))))
                      :hints(("Goal" :in-theory (enable aignet-idp)))
                      :rule-classes (:rewrite :linear)))
             (local (in-theory (disable acl2::mv-nth-cons-meta))))
  :guard-hints (("Goal" :in-theory (enable less-when-aignet-idp)))
  (b* (((acl2::local-stobjs copy copy2 strash strash2 mark aignet-tmp)
        (mv new-lit aignet2 state copy copy2 strash strash2 mark aignet-tmp))
       (gatesimp (observability-config->gatesimp config))
       
       ((mv constr-lit strash2 copy2 aignet-tmp)
        (aignet-lit-constprop-init-and-sweep lit aignet gatesimp strash2 copy2 aignet-tmp))

       (gate-lit (get-lit (lit->var lit) copy2))

       (aignet2 (aignet-init 1 (num-ins aignet) (num-regs aignet)
                             (+ 10 (ash (* 5 (num-fanins aignet)) -2))
                             aignet2))
       (aignet2 (aignet-add-ins (num-ins aignet) aignet2))
       (aignet2 (aignet-add-regs (num-regs aignet) aignet2))

       ((mv obs-lit copy strash aignet2 aignet-tmp state)
        (observability-fix-lit gate-lit config aignet-tmp copy strash aignet2 state))

       (copy (aignet-copy-set-ins 0 aignet-tmp copy aignet2))
       (copy (aignet-copy-set-regs 0 aignet-tmp copy aignet2))

       (mark (resize-bits (num-fanins aignet-tmp) mark))

       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-rec (lit->var constr-lit) aignet-tmp mark copy strash gatesimp aignet2))

       ((mv and-lit strash aignet2)
        (aignet-hash-and obs-lit (lit-copy constr-lit copy) gatesimp strash aignet2))
       (ans (lit-negate-cond and-lit (lit->neg lit)))

       ((acl2::hintcontext :end)))
    (mv ans
        aignet2 state copy copy2 strash strash2 mark aignet-tmp))
  ///
  (set-ignore-ok t)

  (defret stype-count-of-<fn>
    (and (equal (stype-count :pi new-aignet2)
                (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2)
                (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2)
                0)
         (equal (stype-count :nxst new-aignet2)
                0)))
         

  (defret aignet-litp-of-<fn>
    (aignet-litp new-lit new-aignet2))


  (defret aignet-lit-constprop/observability-correct
    (implies (aignet-litp lit aignet)
             (equal (lit-eval new-lit invals regvals new-aignet2)
                    (lit-eval lit invals regvals aignet)))
    :hints (("goal" :in-theory (enable aignet-copy-set-ins-of-aignet2-ext-regs-hack
                                       aignet-copy-set-regs-of-aignet2-ext
                                       aignet-copy-set-ins-of-aignet-ext
                                       aignet-copy-set-regs-of-aignet-ext))
            (acl2::function-termhint
             aignet-lit-constprop/observability
             (:end
              (if (equal 1 (lit-eval constr-lit invals regvals aignet-tmp))
                  nil
                '(:cases ((equal 1 (lit-eval (lit-abs lit) invals regvals aignet)))
                  )))))
    :otf-flg t)

  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (let ((aignet2 nil)) <call>))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(define aignet-constprop/observability (aignet
                                        aignet2
                                        (config observability-config-p)
                                        state)
  :returns (mv new-aignet2 new-state)
  (b* (((unless (and (eql (num-outs aignet) 1)
                     (eql (num-regs aignet) 0)))
        (b* ((aignet2 (aignet-raw-copy aignet aignet2))
             (aignet2 (aignet-fix aignet2)))
          (mv aignet2 state)))
       ((mv new-lit aignet2 state)
        (aignet-lit-constprop/observability (outnum->fanin 0 aignet)
                                            aignet aignet2 config state))
       (aignet2 (aignet-add-out new-lit aignet2)))
    (mv aignet2 state))
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

  (local (defthm lookup-stype-when-zp
           (implies (and (syntaxp (not (equal n ''0)))
                         (zp n))
                    (equal (lookup-stype n stype aignet)
                           (lookup-stype 0 stype aignet)))
           :hints(("Goal" :in-theory (enable lookup-stype)))))


  (defret <fn>-comb-equiv
    (comb-equiv new-aignet2 aignet)
    :hints(("Goal" :in-theory (enable comb-equiv outs-comb-equiv nxsts-comb-equiv output-eval
                                      lookup-stype))))

  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (let ((aignet2 nil)) <call>))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(fty::defprod obs-constprop-config
  ((gatesimp gatesimp-p :default (default-gatesimp)
             "Gate simplification parameters.  Warning: This transform will do
              nothing good if hashing is turned off.")
   (constprop-iterations natp :rule-classes :type-prescription :default 1
                    "Number of constant propagation iterations.")
   (obs-hyp-max-size acl2::maybe-natp :rule-classes :type-prescription
                     "Maximum fanin cone size for the hyp"
                     :default 3000)
   (obs-concl-min-size acl2::maybe-natp :rule-classes :type-prescription
                       "Minimum fanin cone size for the conclusion"
                       :default 5000)
   (obs-min-ratio rationalp :rule-classes :type-prescription
                  "Minimum ratio of conclusion to hyp"
                  :default 10))
  :parents (obs-constprop comb-transform)
  :short "Configuration object for the @see obs-constprop) aignet transform."
  :tag :obs-constprop-config)


(define obs-constprop-config-to-observability-config ((config obs-constprop-config-p))
  :returns (obs-config observability-config-p)
  (b* (((obs-constprop-config config)))
    (make-observability-config
     :hyp-max-size config.obs-hyp-max-size
     :concl-min-size config.obs-concl-min-size
     :min-ratio config.obs-min-ratio
     :gatesimp config.gatesimp)))

(define obs-constprop-config-to-constprop-config ((config obs-constprop-config-p))
  :returns (constprop-config constprop-config-p)
  (b* (((obs-constprop-config config)))
    (make-constprop-config
     :iterations (max (- config.constprop-iterations 1) 1)
     :gatesimp config.gatesimp)))

(define obs-constprop-core (aignet
                            aignet2
                            (config obs-constprop-config-p)
                            state)
  :returns (mv new-aignet2 new-state)
  (b* (((obs-constprop-config config))
       (obs-config (obs-constprop-config-to-observability-config config))
       ((when (eql config.constprop-iterations 0))
        (b* (((acl2::local-stobjs aignet-tmp)
              (mv aignet2 aignet-tmp state))
             (aignet-tmp (aignet-raw-copy aignet aignet-tmp)))
          (observability-fix-core aignet-tmp aignet2 obs-config state)))
       ((when (eql config.constprop-iterations 1))
        (aignet-constprop/observability aignet aignet2 obs-config state))
       ((acl2::local-stobjs aignet-tmp)
        (mv aignet2 state aignet-tmp))
       (aignet-tmp (constprop-core aignet aignet-tmp (obs-constprop-config-to-constprop-config config)))
       ((mv aignet2 state)
        (aignet-constprop/observability aignet-tmp aignet2 obs-config state)))
    (mv aignet2 state aignet-tmp))
  ///
  (defret <fn>-comb-equiv
    (comb-equiv new-aignet2 aignet))

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

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))




(define obs-constprop ((aignet  "Input aignet")
                       (aignet2 "New aignet -- will be emptied")
                       (config obs-constprop-config-p
                               "Settings for the transform")
                       state)
  :parents (aignet-comb-transforms)
  :short "Combine @(see constprop) and @(see observability-fix) for a transform that is
          sometimes somewhat better than simply running both in sequence."
  :guard-debug t
  :returns (mv new-aignet2 new-state)
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet2 state aignet-tmp))
       ((mv aignet-tmp state) (obs-constprop-core aignet aignet-tmp config state))
       (aignet2 (aignet-prune-comb aignet-tmp aignet2 (obs-constprop-config->gatesimp config))))
    (mv aignet2 state aignet-tmp))
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

  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (let ((aignet2 nil)) <call>))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(define obs-constprop! ((aignet  "Input aignet -- will be replaced with transformation result")
                        (config obs-constprop-config-p)
                        state)
  :guard-debug t
  :returns (mv new-aignet new-state)
  :parents (obs-constprop)
  :short "Like @(see obs-constprop), but overwrites the original network instead of returning a new one."
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet state aignet-tmp))
       ((mv aignet-tmp state) (obs-constprop-core aignet aignet-tmp config state))
       (aignet (aignet-prune-comb aignet-tmp aignet (obs-constprop-config->gatesimp config))))
    (mv aignet state aignet-tmp))
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
    (equal (w new-state) (w state))))


