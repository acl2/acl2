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

(include-book "centaur/aignet/prune" :dir :system)
(include-book "centaur/aignet/ipasir" :dir :system)
(include-book "transform-utils")
(include-book "transform-stub")
(include-book "count")
(include-book "supergate-construction")

(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "centaur/aignet/cnf" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system ))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))


(local (in-theory (disable nth update-nth nfix ifix (tau-system)
                           resize-list
                           acl2::resize-list-when-atom
                           ;; acl2::resize-list-when-empty
                           )))
(local (std::add-default-post-define-hook :fix))

(local (xdoc::set-default-parents observability-fix))



(define observability-fixed-inputs ((n natp)
                                    (invals) (inmasks)
                                    (hyp-lit litp)
                                    (aignet)
                                    (copy)
                                    (gatesimp gatesimp-p)
                                    (strash)
                                    (aignet2))
  :guard (and (<= (nfix n) (num-ins aignet))
              (fanin-litp hyp-lit aignet2)
              (aignet-copies-in-bounds copy aignet2)
              (<= (num-ins aignet) (num-ins aignet2))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-ins aignet) (bits-length inmasks))
              (<= (num-fanins aignet) (lits-length copy)))
  :measure (nfix (- (num-ins aignet) (nfix n)))
  :returns (mv new-copy new-strash new-aignet2)
  :prepwork ((local (defthm lit->var-of-bit
                      (implies (bitp b)
                               (equal (lit->var b) 0))
                      :hints(("Goal" :in-theory (enable bitp))))))
  ;; :prepwork ((local (defthm aignet-litp-of-bit
  ;;                     (implies (bitp b)
  ;;                              (aignet-litp b aignet))
  ;;                     :hints(("Goal" :in-theory (enable aignet-litp bitp)))))
  ;;            (local (defthm aignet-litp-of-input-lit
  ;;                     (implies (equal (stype (car (lookup-id id aignet))) :pi)
  ;;                              (aignet-litp (make-lit id neg) aignet))
  ;;                     :hints(("Goal" :in-theory (enable aignet-litp))))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable aignet-idp))))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (eql (num-ins aignet) n)))
        (b* ((aignet2 (aignet-fix aignet2)))
          (mv copy strash aignet2)))
       (input-lit (get-lit (innum->id n aignet) copy))
       ((mv fixed-lit strash aignet2)
        (if (eql 1 (get-bit n inmasks))
            (aignet-hash-mux hyp-lit input-lit (get-bit n invals) gatesimp strash aignet2)
          (mv input-lit strash aignet2)))
       (orig-id (innum->id n aignet))
       (copy (set-lit orig-id fixed-lit copy)))
    (observability-fixed-inputs (1+ (lnfix n)) invals inmasks hyp-lit aignet copy gatesimp strash aignet2))
  ///
  (defret copies-in-bounds-of-observability-fixed-inputs
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-litp hyp-lit aignet2)
                  (<= (num-ins aignet) (num-ins aignet2)))
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret copy-length-of-observability-fixed-inputs
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints(("Goal" :in-theory (enable update-nth-lit))))

  (defret aignet-extension-p-of-observability-fixed-inputs
    (aignet-extension-p new-aignet2 aignet2))

  (local (defret input-copy-preserved-of-observability-fixed-inputs
           (implies (< (nfix innum) (nfix n))
                    (equal (nth-lit (fanin-count (lookup-stype innum :pi aignet)) new-copy)
                           (nth-lit (fanin-count (lookup-stype innum :pi aignet)) copy)))))


  (defret stypes-preserved-of-observability-fixed-inputs
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (local (defthm lit-eval-of-bit
           (implies (bitp b)
                    (equal (lit-eval b invals regvals aignet)
                           b))
           :hints(("Goal" :in-theory (enable bitp)))))

  (local (defthm lit-eval-of-make-lit-0
           (equal (lit-eval (make-lit n 0) invals regvals aignet)
                  (id-eval n invals regvals aignet))
           :hints (("goal" :expand ((lit-eval (make-lit n 0) invals regvals aignet))))))

  (defret non-input-copy-of-observability-fixed-inputs
    (implies (not (equal (stype (car (lookup-id id aignet))) :pi))
             (equal (nth-lit id new-copy) (nth-lit id copy))))

  (defret input-copy-of-observability-fixed-inputs
    (implies (and (<= (nfix n) (nfix innum))
                  (< (nfix innum) (num-ins aignet))
                  (aignet-litp hyp-lit aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (equal 1 (lit-eval hyp-lit some-invals some-regvals aignet2)))
             (equal (lit-eval (nth-lit (fanin-count (lookup-stype innum :pi aignet)) new-copy)
                              some-invals some-regvals new-aignet2)
                    (lit-eval (nth-lit (fanin-count (lookup-stype innum :pi aignet)) copy)
                              some-invals some-regvals aignet2)))
    :hints(("Goal" :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable* acl2::b-ite
                                      acl2::arith-equiv-forwarding)))))

  ;; weird thing needed for deffixequiv
  (local (defthm not-equal-nfix-plus-1
           (not (equal n (+ 1 (nfix n))))
           :hints(("Goal" :in-theory (enable nfix)))))

  (local (defthm input-copy-values-of-update-lower-input
           (implies (< (nfix m) (nfix n))
                    (equal (input-copy-values n invals regvals aignet
                                            (update-nth-lit (fanin-count (lookup-stype m :pi aignet)) val copy)
                                            aignet2)
                           (input-copy-values n invals regvals aignet copy aignet2)))
           :hints(("Goal" :in-theory (enable input-copy-values)))))

  (defret input-copy-values-of-observability-fixed-inputs
    (implies (and (aignet-litp hyp-lit aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (equal 1 (lit-eval hyp-lit some-invals some-regvals aignet2)))
             (equal (input-copy-values n some-invals some-regvals aignet new-copy new-aignet2)
                    (input-copy-values n some-invals some-regvals aignet copy aignet2)))
    :hints(("Goal" :in-theory (enable input-copy-values)
            :induct <call>
            :expand (<call>))))

  (defret reg-copy-values-of-observability-fixed-inputs
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-litp hyp-lit aignet2)
                  (<= (num-ins aignet) (num-ins aignet2)))
             (equal (reg-copy-values 0 some-invals some-regvals aignet new-copy new-aignet2)
                    (reg-copy-values 0 some-invals some-regvals aignet copy aignet2)))))


(define observability-fixed-regs ((n natp)
                                 (regvals) (regmasks)
                                 (hyp-lit litp)
                                 (aignet)
                                 (copy)
                                 (gatesimp gatesimp-p)
                                 (strash)
                                 (aignet2))
  :guard (and (<= (nfix n) (num-regs aignet))
              (fanin-litp hyp-lit aignet2)
              (<= (num-regs aignet) (num-regs aignet2))
              (<= (num-regs aignet) (bits-length regvals))
              (<= (num-regs aignet) (bits-length regmasks))
                  (aignet-copies-in-bounds copy aignet2)
              (<= (num-fanins aignet) (lits-length copy)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :returns (mv new-copy new-strash new-aignet2)
  :prepwork ((local (defthm lit->var-of-bit
                      (implies (bitp b)
                               (equal (lit->var b) 0))
                      :hints(("Goal" :in-theory (enable bitp))))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable aignet-litp))))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql (num-regs aignet) n)))
        (b* ((aignet2 (aignet-fix aignet2)))
          (mv copy strash aignet2)))
       (reg-lit (get-lit (regnum->id n aignet) copy))
       ((mv fixed-lit strash aignet2)
        (if (eql 1 (get-bit n regmasks))
            (aignet-hash-mux hyp-lit reg-lit (get-bit n regvals) gatesimp strash aignet2)
          (mv reg-lit strash aignet2)))
       (orig-id (regnum->id n aignet))
       (copy (set-lit orig-id fixed-lit copy)))
    (observability-fixed-regs (1+ (lnfix n)) regvals regmasks hyp-lit aignet copy gatesimp strash aignet2))
  ///
  (defret copies-in-bounds-of-observability-fixed-regs
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-litp hyp-lit aignet2)
                  (<= (num-regs aignet) (num-regs aignet2)))
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret copy-length-of-observability-fixed-regs
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints(("Goal" :in-theory (enable update-nth-lit))))

  (defret aignet-extension-p-of-observability-fixed-regs
    (aignet-extension-p new-aignet2 aignet2))

  (local (defret reg-copy-preserved-of-observability-fixed-regs
           (implies (< (nfix regnum) (nfix n))
                    (equal (nth-lit (fanin-count (lookup-stype regnum :reg aignet)) new-copy)
                           (nth-lit (fanin-count (lookup-stype regnum :reg aignet)) copy)))))

  (defret stypes-preserved-of-observability-fixed-regs
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (local (defthm lit-eval-of-bit
           (implies (bitp b)
                    (equal (lit-eval b regvals regvals aignet)
                           b))
           :hints(("Goal" :in-theory (enable bitp)))))

  (local (defthm lit-eval-of-make-lit-0
           (equal (lit-eval (make-lit n 0) regvals regvals aignet)
                  (id-eval n regvals regvals aignet))
           :hints (("goal" :expand ((lit-eval (make-lit n 0) regvals regvals aignet))))))

  (defret non-reg-copy-of-observability-fixed-inputs
    (implies (not (equal (stype (car (lookup-id id aignet))) :reg))
             (equal (nth-lit id new-copy) (nth-lit id copy))))

  (defret reg-copy-of-observability-fixed-regs
    (implies (and (<= (nfix n) (nfix regnum))
                  (< (nfix regnum) (num-regs aignet))
                  (aignet-litp hyp-lit aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (num-regs aignet) (num-regs aignet2))
                  (equal 1 (lit-eval hyp-lit some-invals some-regvals aignet2)))
             (equal (lit-eval (nth-lit (fanin-count (lookup-stype regnum :reg aignet)) new-copy)
                              some-invals some-regvals new-aignet2)
                    (lit-eval (nth-lit (fanin-count (lookup-stype regnum :reg aignet)) copy)
                              some-invals some-regvals aignet2)))
    :hints(("Goal" :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable* acl2::b-ite acl2::arith-equiv-forwarding)))))

  ;; weird thing needed for deffixequiv
  (local (defthm not-equal-nfix-plus-1
           (not (equal n (+ 1 (nfix n))))
           :hints(("Goal" :in-theory (enable nfix)))))

  (local (defthm reg-copy-values-of-update-lower-reg
           (implies (< (nfix m) (nfix n))
                    (equal (reg-copy-values n invals regvals aignet
                                            (update-nth-lit (fanin-count (lookup-stype m :reg aignet)) val copy)
                                            aignet2)
                           (reg-copy-values n invals regvals aignet copy aignet2)))
           :hints(("Goal" :in-theory (enable reg-copy-values)))))

  (defret reg-copy-values-of-observability-fixed-regs
    (implies (and (aignet-litp hyp-lit aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (num-regs aignet) (num-regs aignet2))
                  (equal 1 (lit-eval hyp-lit some-invals some-regvals aignet2)))
             (equal (reg-copy-values n some-invals some-regvals aignet new-copy new-aignet2)
                    (reg-copy-values n some-invals some-regvals aignet copy aignet2)))
    :hints(("Goal" :in-theory (enable reg-copy-values)
            :induct <call>
            :expand (<call>))))

  (defret input-copy-values-of-observability-fixed-regs
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-litp hyp-lit aignet2)
                  (<= (num-regs aignet) (num-regs aignet2)))
             (equal (input-copy-values 0 some-invals some-regvals aignet new-copy new-aignet2)
                    (input-copy-values 0 some-invals some-regvals aignet copy aignet2)))))

(local (in-theory (disable w)))

(define observability-fix-input-copies ((lit litp)
                                        (aignet)
                                        (copy)
                                        (strash)
                                        (aignet2)
                                        (state))
  ;; Lit is a literal in aignet2.  Find a satisfying assignment for it if one
  ;; exists.  Update the copies of the PIs and regs of aignet to be new ones of
  ;; the form: if (lit or dont-care in minimized counterex) then
  ;; previous-copy-value, else satisfying-assign-value.
  ;; If unsat, map all inputs to false.  If sat check fails, don't remap the inputs.

  ;; Correctness: if lit is true, then input copy values are the same as the previous ones.
  :returns (mv (status (or (equal status :failed)
                           (equal status :unsat)
                           (equal status :sat))
                       :rule-classes ((:forward-chaining :trigger-terms (status))))
               (new-copy)
               (new-strash)
               (new-aignet2)
               (new-state))
  :guard (and (fanin-litp lit aignet2)
              (<= (num-fanins aignet) (lits-length copy))
              (<= (num-ins aignet) (num-ins aignet2))
              (<= (num-regs aignet) (num-regs aignet2))
              (aignet-copies-in-bounds copy aignet2))
  (b* (((acl2::local-stobjs invals regvals inmasks regmasks)
        (mv invals regvals inmasks regmasks status copy strash aignet2 state))
       ((mv status invals regvals inmasks regmasks state)
        (aignet-lit-ipasir-sat-minimize lit invals regvals inmasks regmasks aignet2 state))
       (aignet2 (aignet-fix aignet2))
       ((unless (eql status :sat))
        ;; BOZO for unsat, map to constants or something?
        (mv invals regvals inmasks regmasks status copy strash aignet2 state))
       ((mv copy strash aignet2)
        (observability-fixed-inputs 0 invals inmasks lit aignet copy (default-gatesimp) strash aignet2))
       ((mv copy strash aignet2)
        (observability-fixed-regs 0 regvals regmasks lit aignet copy (default-gatesimp) strash aignet2)))
    (mv invals regvals inmasks regmasks status copy strash aignet2 state))
  ///

  (defret copies-in-bounds-of-observability-fix-input-copies
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-litp lit aignet2)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret copy-length-of-observability-fix-input-copies
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints(("Goal" :in-theory (enable update-nth-lit))))

  (defret aignet-extension-p-of-observability-fix-input-copies
    (aignet-extension-p new-aignet2 aignet2))

  (defret stypes-preserved-of-observability-fix-input-copies
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret non-input-copy-of-observability-fix-input-copies
    (implies (not (equal (ctype (stype (car (lookup-id id aignet)))) (in-ctype)))
             (equal (nth-lit id new-copy) (nth-lit id copy))))

  (defret pi-copy-of-observability-fix-input-copies
    (implies (and (< (nfix innum) (num-ins aignet))
                  (aignet-litp lit aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (equal 1 (lit-eval lit some-invals some-regvals aignet2)))
             (equal (lit-eval (nth-lit (fanin-count (lookup-stype innum :pi aignet)) new-copy)
                              some-invals some-regvals new-aignet2)
                    (lit-eval (nth-lit (fanin-count (lookup-stype innum :pi aignet)) copy)
                              some-invals some-regvals aignet2))))

  (defret reg-copy-of-observability-fix-input-copies
    (implies (and (< (nfix regnum) (num-regs aignet))
                  (aignet-litp lit aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (num-regs aignet) (num-regs aignet2))
                  (<= (num-ins aignet) (num-ins aignet2))
                  (equal 1 (lit-eval lit some-invals some-regvals aignet2)))
             (equal (lit-eval (nth-lit (fanin-count (lookup-stype regnum :reg aignet)) new-copy)
                              some-invals some-regvals new-aignet2)
                    (lit-eval (nth-lit (fanin-count (lookup-stype regnum :reg aignet)) copy)
                              some-invals some-regvals aignet2))))

  (defret reg-copy-values-of-observability-fix-input-copies
    (implies (and (aignet-litp lit aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (num-regs aignet) (num-regs aignet2))
                  (<= (num-ins aignet) (num-ins aignet2))
                  (equal 1 (lit-eval lit some-invals some-regvals aignet2)))
             (equal (reg-copy-values 0 some-invals some-regvals aignet new-copy new-aignet2)
                    (reg-copy-values 0 some-invals some-regvals aignet copy aignet2))))

  (defret input-copy-values-of-observability-fix-input-copies
    (implies (and (aignet-litp lit aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (num-regs aignet) (num-regs aignet2))
                  (<= (num-ins aignet) (num-ins aignet2))
                  (equal 1 (lit-eval lit some-invals some-regvals aignet2)))
             (equal (input-copy-values 0 some-invals some-regvals aignet new-copy new-aignet2)
                    (input-copy-values 0 some-invals some-regvals aignet copy aignet2))))

  (defret observability-fix-input-copies-not-unsat-when-sat
    (implies (and (equal (lit-eval lit some-invals some-regvals aignet2) 1)
                  (aignet-litp lit aignet2))
             (not (equal status :unsat))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



(set-state-ok t)

(fty::defprod observability-config
  ((hyp-max-size acl2::maybe-natp :rule-classes :type-prescription
                 "Maximum fanin cone size for the hyp"
                 :default 3000)
   (concl-min-size acl2::maybe-natp :rule-classes :type-prescription
                   "Minimum fanin cone size for the conclusion"
                   :default 5000)
   (min-ratio rationalp :rule-classes :type-prescription
              "Minimum ratio of conclusion to hyp"
              :default 10)
   (gatesimp gatesimp-p :default (default-gatesimp)
             "Gate simplification parameters.  Warning: This transform will do
              nothing good if hashing is turned off."))
  :parents (observability-fix comb-transform)
  :short "Configuration object for the @(see observability-fix) aignet transform."
  :tag :observability-config)

(define observability-size-check ((lit-size natp)
                                  (full-size natp)
                                  (config observability-config-p))
  (b* (((observability-config config)))
    (and (or (not config.hyp-max-size)
             (<= (lnfix lit-size) config.hyp-max-size))
         (or (not config.concl-min-size)
             (>= (lnfix full-size) config.concl-min-size))
         (<= (* (numerator config.min-ratio) (lnfix lit-size))
             (* (denominator config.min-ratio) (lnfix full-size))))))

(local (defthm aignet-lit-listp-implies-lits-max-id-val-bound
         (implies (aignet-lit-listp x aignet)
                  (<= (lits-max-id-val x) (fanin-count aignet)))
         :hints(("Goal" :in-theory (enable lits-max-id-val aignet-idp)))
         :rule-classes :forward-chaining))

(local #!satlink
       (fty::deflist lit-list :pred lit-listp :elt-type litp :true-listp t
         :parents (litp)
         :short "List of literals"))

(local
 (encapsulate
   ()

   (local
    (defthm lemma
      (< (lit-eval nil invals regvals aignet)
         1)
      :hints (("goal" :in-theory (enable nth lit-eval-list lit-eval)))
      :rule-classes :linear))

   (defthm nth-of-lit-eval-list
     (bit-equiv (nth n (lit-eval-list lits invals regvals aignet))
                (lit-eval (nth n lits) invals regvals aignet))
     :hints(("Goal" :in-theory (enable nth lit-eval-list))))))

(define observability-fix-hyps/concls ((hyps lit-listp)
                                       (concls lit-listp)
                                       (aignet)
                                       (copy)
                                       (gatesimp gatesimp-p)
                                       (strash)
                                       (aignet2)
                                       (state))

  :guard (and (<= (num-fanins aignet) (lits-length copy))
              (aignet-copies-in-bounds copy aignet2)
              (aignet-lit-listp hyps aignet)
              (aignet-lit-listp concls aignet)
              (<= (num-ins aignet) (num-ins aignet2))
              (<= (num-regs aignet) (num-regs aignet2)))
  :returns (mv (hyp-copy litp)
               (new-hyps lit-listp)
               (new-concls lit-listp)
               new-copy new-strash new-aignet2 new-state)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp)
                       :do-not-induct t)))
  (b* (((mv copy strash aignet2)
        (b* (((acl2::local-stobjs mark)
              (mv mark copy strash aignet2))
             (mark (resize-bits (num-fanins aignet) mark))
             ;; (litarr (resize-lits (+ 1 (lit-id hyp)) litarr))
             ((mv mark copy strash aignet2)
              (aignet-copy-dfs-list hyps aignet mark copy strash gatesimp aignet2)))
          (mv mark copy strash aignet2)))
       (hyp-copies (lit-list-copies hyps copy))
       ((mv hyp-copy strash aignet2)
        (aignet-hash-and-supergate hyp-copies gatesimp strash aignet2))
       ((mv ?status copy strash aignet2 state)
        (observability-fix-input-copies hyp-copy aignet copy strash aignet2 state))
       ((when (eq status :unsat))
        (mv 0
            hyp-copies
            (make-list (len concls) :initial-element 0)
            copy strash aignet2 state))
       ((mv copy strash aignet2)
        (b* (((acl2::local-stobjs mark)
              (mv mark copy strash aignet2))
             (mark (resize-bits (num-fanins aignet) mark)))
          (aignet-copy-dfs-list concls aignet mark copy strash gatesimp aignet2)))
       (concl-copies (lit-list-copies concls copy)))
    (mv hyp-copy hyp-copies concl-copies copy strash aignet2 state))
  ///

  (local (acl2::use-trivial-ancestors-check))

  (defret aignet-extension-of-<fn>
    (aignet-extension-p new-aignet2 aignet2)
    :hints ('(:expand (<call>))))

  (defret stype-counts-of-<fn>
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2)))
    :hints ('(:expand (<call>))))

  (defret copy-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len copy))
                  (aignet-lit-listp hyps aignet)
                  (aignet-lit-listp concls aignet))
             (equal (len new-copy) (len copy))))


  ;; (local (defthm aignet-idp-when-lte-max-fanin
  ;;          (implies (<= (nfix n) (max-fanin aignet))
  ;;                   (aignet-idp n aignet))
  ;;          :hints(("Goal" :in-theory (enable aignet-idp)))))

  (local (in-theory (disable bound-when-aignet-idp)))

  (local (defthm len-of-update-nth-lit
           (implies (< (nfix n) (len x))
                    (equal (len (update-nth-lit n val x))
                           (len x)))
           :hints(("Goal" :in-theory (enable update-nth-lit)))))

  ;; (defret copy-size-of-<fn>
  ;;   (implies (and (<= (num-fanins aignet) (len copy))
  ;;                 (< (lit-id hyp) (num-fanins aignet))
  ;;                 (< (lit-id concl) (num-fanins aignet)))
  ;;            (equal (len new-copy) (len copy)))
  ;;   :hints ('(:expand (<call>))))

  (defret copies-in-bounds-of-<fn>
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-lit-listp hyps aignet)
                  (aignet-lit-listp concls aignet)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (and (aignet-copies-in-bounds new-copy new-aignet2)
                  (aignet-litp hyp-copy new-aignet2)
                  (aignet-lit-listp new-hyps new-aignet2)
                  (aignet-lit-listp new-concls new-aignet2)))
    :hints ('(:expand (<call>))))

  (local (defthm id-eval-of-input
           (implies (equal (ctype (stype (car (lookup-id n aignet)))) :input)
                    (equal (id-eval n invals regvals aignet)
                           (if (eql 1 (regp (stype (car (lookup-id n aignet)))))
                               (bfix (nth (stype-count :reg (cdr (lookup-id n aignet))) regvals))
                             (bfix (nth (stype-count :pi (cdr (lookup-id n aignet))) invals)))))
           :hints (("goal" :expand ((id-eval n invals regvals aignet))))))

  (defthm dfs-copy-onto-invar-of-empty-mark
    (dfs-copy-onto-invar aignet (resize-list nil n 0) copy aignet2)
    :hints(("Goal" :in-theory (enable dfs-copy-onto-invar))))

  (local (defthm b-xor-id-eval-equals-lit-eval
           (equal (b-xor (lit->neg x)
                         (id-eval (lit->var x) invals regvals aignet))
                  (lit-eval x invals regvals aignet))
           :hints(("Goal" :in-theory (enable lit-eval)))))

  (local (defun search-matching-lit (pat clause alist)
           (b* (((when (atom clause)) nil)
                ((mv ok subst) (acl2::simple-one-way-unify pat (car clause) alist)))
             (if ok
                 subst
               (search-matching-lit pat (cdr clause) alist)))))

  (defret new-concls-len-of-<fn>
    (equal (len new-concls)
           (len concls)))

  (defret new-hyps-len-of-<fn>
    (equal (len new-hyps)
           (len hyps)))

  (local (defthm len-<-0
           (equal (< 0 (len x))
                  (consp x))))
  (local (defthm equal-of-consp-by-equal-of-len
           (implies (equal (len x) (len y))
                    (equal (equal (consp x) (consp y)) t))))

  (defret new-concls-consp-of-<fn>
    (equal (consp new-concls)
           (consp concls)))

  (defret new-hyps-consp-of-<fn>
    (equal (consp new-hyps)
           (consp hyps)))

  (defret hyp-eval-of-<fn>
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  ;; (aignet-litp hyp aignet)
                  ;; (aignet-lit-listp concls aignet)
                  (aignet-lit-listp hyps aignet)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (and (equal (lit-eval hyp-copy invals regvals new-aignet2)
                         (aignet-eval-conjunction hyps
                                                  (input-copy-values 0 invals regvals aignet copy aignet2)
                                                  (reg-copy-values 0 invals regvals aignet copy aignet2)
                                                  aignet))
                  (equal (lit-eval-list new-hyps invals regvals new-aignet2)
                         (lit-eval-list hyps
                                        (input-copy-values 0 invals regvals aignet copy aignet2)
                                        (reg-copy-values 0 invals regvals aignet copy aignet2)
                                        aignet))))
    :hints ((and stable-under-simplificationp
                 (let ((subst (search-matching-lit '(not (equal (mv-nth '0 (observability-fix-input-copies
                                                                            lit aignet copy strash aignet2 state))
                                                                ':unsat))
                                                   clause
                                                   '((aignet . aignet) (state . state)))))
                   (and subst
                        `(:use ((:instance observability-fix-input-copies-not-unsat-when-sat
                                 ,@(pairlis$ (strip-cars subst)
                                             (pairlis$ (strip-cdrs subst) nil))
                                 (some-invals invals) (some-regvals regvals)))
                          :in-theory (disable observability-fix-input-copies-not-unsat-when-sat)))))))


  (defret eval-of-<fn>
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  ;; (aignet-litp hyp aignet)
                  (aignet-lit-listp concls aignet)
                  (aignet-lit-listp hyps aignet)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2))
                  (equal (aignet-eval-conjunction
                          hyps
                          (input-copy-values 0 invals regvals aignet copy aignet2)
                          (reg-copy-values 0 invals regvals aignet copy aignet2)
                          aignet) 1))
             (equal (lit-eval-list new-concls invals regvals new-aignet2)
                    (lit-eval-list concls
                                   (input-copy-values 0 invals regvals aignet copy aignet2)
                                   (reg-copy-values 0 invals regvals aignet copy aignet2)
                                   aignet)))
    :hints ((and stable-under-simplificationp
                 (let ((subst (search-matching-lit '(not (equal (mv-nth '0 (observability-fix-input-copies
                                                                            lit aignet copy strash aignet2 state))
                                                                ':unsat))
                                                   clause
                                                   '((aignet . aignet) (state . state)))))
                   (and subst
                        `(:use ((:instance observability-fix-input-copies-not-unsat-when-sat
                                 ,@(pairlis$ (strip-cars subst)
                                             (pairlis$ (strip-cdrs subst) nil))
                                 (some-invals invals) (some-regvals regvals)))
                          :in-theory (disable observability-fix-input-copies-not-unsat-when-sat)))))
            ;; (and stable-under-simplificationp
            ;;      '(:cases ((EQUAL 1
            ;;                       (LIT-EVAL HYP
            ;;                                 (INPUT-COPY-VALUES 0 INVALS REGVALS AIGNET COPY AIGNET2)
            ;;                                 (REG-COPY-VALUES 0 INVALS REGVALS AIGNET COPY AIGNET2)
            ;;                                 AIGNET)))))
            ))


  (encapsulate nil
    (local (defthm lit-eval-of-nth
             (equal (lit-eval (nth n lits) invals regvals aignet)
                    (bfix (nth n (lit-eval-list lits invals regvals aignet))))))
    (local (in-theory (disable nth-of-lit-eval-list
                               observability-fix-hyps/concls)))
    (defret nth-hyp-eval-of-<fn>
      (implies (and (aignet-copies-in-bounds copy aignet2)
                    ;; (aignet-litp hyp aignet)
                    ;; (aignet-lit-listp concls aignet)
                    (aignet-lit-listp hyps aignet)
                    (<= (num-ins aignet) (num-ins aignet2))
                    (<= (num-regs aignet) (num-regs aignet2)))
               (equal (lit-eval (nth n new-hyps) invals regvals new-aignet2)
                      (lit-eval (nth n hyps)
                                (input-copy-values 0 invals regvals aignet copy aignet2)
                                (reg-copy-values 0 invals regvals aignet copy aignet2)
                                aignet))))
    (defret nth-concl-eval-of-<fn>
      (implies (and (aignet-copies-in-bounds copy aignet2)
                    ;; (aignet-litp hyp aignet)
                    (aignet-lit-listp concls aignet)
                    (aignet-lit-listp hyps aignet)
                    (<= (num-ins aignet) (num-ins aignet2))
                    (<= (num-regs aignet) (num-regs aignet2))
                    (equal (aignet-eval-conjunction
                            hyps
                            (input-copy-values 0 invals regvals aignet copy aignet2)
                            (reg-copy-values 0 invals regvals aignet copy aignet2)
                            aignet) 1))
               (equal (lit-eval (nth n new-concls) invals regvals new-aignet2)
                      (lit-eval (nth n concls)
                                (input-copy-values 0 invals regvals aignet copy aignet2)
                                (reg-copy-values 0 invals regvals aignet copy aignet2)
                                aignet)))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(define observability-fix-hyp/concl ((hyp litp)
                                     (concl litp)
                                     (aignet)
                                     (copy)
                                     (gatesimp gatesimp-p)
                                     (strash)
                                     (aignet2)
                                     (state))

    :guard (and (<= (num-fanins aignet) (lits-length copy))
                (aignet-copies-in-bounds copy aignet2)
                (fanin-litp hyp aignet)
                (fanin-litp concl aignet)
                (<= (num-ins aignet) (num-ins aignet2))
                (<= (num-regs aignet) (num-regs aignet2)))
    :returns (mv (conj litp)
                 new-copy new-strash new-aignet2 new-state)
    :guard-hints (("goal" :use ((:instance copies-in-bounds-of-observability-fix-hyps/concls
                                 (hyps (list hyp)) (concls (list concl))))
                   :in-theory (disable copies-in-bounds-of-observability-fix-hyps/concls)))
    ;; (and stable-under-simplificationp
    ;; '(:in-theory (enable aignet-idp)
    ;;   :do-not-induct t))

    (b* (((mv new-hyp ?hyp-copies new-concls copy strash aignet2 state)
          (observability-fix-hyps/concls (list hyp) (list concl)
                                         aignet copy gatesimp strash aignet2 state))
         ((mv conj strash aignet2)
          (aignet-hash-and new-hyp (car new-concls) gatesimp strash aignet2)))
      (mv conj copy strash aignet2 state))
    ///

  (local (acl2::use-trivial-ancestors-check))

  (defret aignet-extension-of-<fn>
    (aignet-extension-p new-aignet2 aignet2)
    :hints ('(:expand (<call>))))

  (defret stype-counts-of-<fn>
      (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
               (equal (stype-count stype new-aignet2)
                      (stype-count stype aignet2)))
      :hints ('(:expand (<call>))))

  (defret copy-length-of-<fn>
    (implies (and (<= (num-fanins aignet) (len copy))
                  (aignet-litp hyp aignet)
                  (aignet-litp concl aignet))
             (equal (len new-copy) (len copy)))
    :hints(("Goal" :in-theory (enable aignet-idp))))


  ;; (local (defthm aignet-idp-when-lte-max-fanin
  ;;          (implies (<= (nfix n) (max-fanin aignet))
  ;;                   (aignet-idp n aignet))
  ;;          :hints(("Goal" :in-theory (enable aignet-idp)))))

  (local (in-theory (disable bound-when-aignet-idp)))

  (local (defthm len-of-update-nth-lit
           (implies (< (nfix n) (len x))
                    (equal (len (update-nth-lit n val x))
                           (len x)))
           :hints(("Goal" :in-theory (enable update-nth-lit)))))


  (defret copies-in-bounds-of-<fn>
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-litp hyp aignet)
                  (aignet-litp concl aignet)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (and (aignet-copies-in-bounds new-copy new-aignet2)
                  (aignet-litp conj new-aignet2)))
    :hints ('(:expand (<call>))))

  (local (defthm id-eval-of-input
           (implies (equal (ctype (stype (car (lookup-id n aignet)))) :input)
                    (equal (id-eval n invals regvals aignet)
                           (if (eql 1 (regp (stype (car (lookup-id n aignet)))))
                               (bfix (nth (stype-count :reg (cdr (lookup-id n aignet))) regvals))
                             (bfix (nth (stype-count :pi (cdr (lookup-id n aignet))) invals)))))
           :hints (("goal" :expand ((id-eval n invals regvals aignet))))))

  (defthm dfs-copy-onto-invar-of-empty-mark
    (dfs-copy-onto-invar aignet (resize-list nil n 0) copy aignet2)
    :hints(("Goal" :in-theory (enable dfs-copy-onto-invar))))

  (local (defthm b-xor-id-eval-equals-lit-eval
           (equal (b-xor (lit->neg x)
                         (id-eval (lit->var x) invals regvals aignet))
                  (lit-eval x invals regvals aignet))
           :hints(("Goal" :in-theory (enable lit-eval)))))

  (local (defun search-matching-lit (pat clause alist)
           (b* (((when (atom clause)) nil)
                ((mv ok subst) (acl2::simple-one-way-unify pat (car clause) alist)))
             (if ok
                 subst
               (search-matching-lit pat (cdr clause) alist)))))

  (local (defthm lit-eval-list-when-consp
           (implies (consp x)
                    (equal (lit-eval-list x invals regvals aignet)
                           (cons (lit-eval (car x) invals regvals aignet)
                                 (lit-eval-list (cdr x) invals regvals aignet))))
           :hints(("Goal" :in-theory (enable lit-eval-list)))))


  (defret eval-of-<fn>
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-litp hyp aignet)
                  (aignet-litp concl aignet)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (equal (lit-eval conj invals regvals new-aignet2)
                    (b-and (lit-eval hyp
                                     (input-copy-values 0 invals regvals aignet copy aignet2)
                                     (reg-copy-values 0 invals regvals aignet copy aignet2)
                                     aignet)
                           (lit-eval concl
                                     (input-copy-values 0 invals regvals aignet copy aignet2)
                                     (reg-copy-values 0 invals regvals aignet copy aignet2)
                                     aignet))))
    :hints (("goal" :use ((:instance eval-of-observability-fix-hyps/concls
                           (hyps (list hyp)) (concls (list concl)))
                          (:instance hyp-eval-of-observability-fix-hyps/concls
                           (hyps (list hyp)) (concls (list concl))))
             :in-theory (e/d (lit-eval-list aignet-eval-conjunction)
                             (eval-of-observability-fix-hyps/concls
                              hyp-eval-of-observability-fix-hyps/concls)))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(define observability-split-supergate-aux ((lits lit-listp)
                                           (config observability-config-p)
                                           (full-size natp)
                                           (aignet))
  :returns (mv (hyps lit-listp)
               (rest lit-listp))
  :guard (aignet-lit-listp lits aignet)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp))))
  (b* (((when (atom lits)) (mv nil nil))
       (lit (lit-fix (car lits)))
       (size (count-gates-mark (lit-id lit) aignet))
       (ok (observability-size-check size full-size config))
       ((mv hyps rest) (observability-split-supergate-aux (cdr lits) config full-size aignet)))
    (if ok
        (mv (cons lit hyps) rest)
      (mv hyps (cons lit rest))))
  ///
  (defret aignet-lit-listp-of-observability-split-supergate-aux
    (implies (aignet-lit-listp lits aignet)
             (and (aignet-lit-listp hyps aignet)
                  (aignet-lit-listp rest aignet))))

  (local (defthm b-and-assoc-lit-eval
           (equal (b-and a (b-and (lit-eval lit invals regvals aignet) b))
                  (b-and  (lit-eval lit invals regvals aignet) (b-and a b)))
           :hints(("Goal" :in-theory (enable b-and)))))

  (defret eval-of-observability-split-supergate-aux
    (equal (b-and (aignet-eval-conjunction hyps invals regvals aignet)
                  (aignet-eval-conjunction rest invals regvals aignet))
           (aignet-eval-conjunction lits invals regvals aignet))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))

(define observability-split-supergate ((id natp)
                                       (config observability-config-p)
                                       (aignet))
  :returns (mv (hyps lit-listp)
               (rest lit-listp))
  :guard (and (id-existsp id aignet)
              (not (equal (id->type id aignet) (out-type))))
  :verify-guards nil
  (b* ((full-size (count-gates-mark id aignet))
       ((acl2::local-stobjs aignet-refcounts)
        (mv hyps rest aignet-refcounts))
       (aignet-refcounts (resize-u32 (+ 1 (lnfix id)) aignet-refcounts)) ;; empty
       ((mv lits &)
        (lit-collect-supergate (make-lit id 0) t nil 1000 nil aignet-refcounts aignet))
       (- (cw "Observability supergate: ~x0 lits~%" (len lits)))
       ((mv hyps rest) (observability-split-supergate-aux lits config full-size aignet))
       (- (cw "Observability hyp lits: ~x0 concl: ~x1~%" (len hyps) (len rest))))
    (mv hyps rest aignet-refcounts))
  ///
  (local (defthm id-less-than-max-fanin-when-not-output
           (implies (and (aignet-idp id aignet)
                         (not (equal (id->type id aignet) (out-type))))
                    (and (<= (nfix id) (fanin-count aignet))
                         (implies (natp id)
                                  (<= id (fanin-count aignet)))))
           :hints(("Goal" :in-theory (enable lookup-id aignet-idp)))))

  (verify-guards observability-split-supergate
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret aignet-lit-listp-of-observability-split-supergate
    (implies (and (aignet-idp id aignet)
                  (not (equal (ctype (stype (car (lookup-id id aignet)))) :output)))
             (and (aignet-lit-listp hyps aignet)
                  (aignet-lit-listp rest aignet))))

  (defret eval-of-observability-split-supergate
    (equal (b-and (aignet-eval-conjunction hyps invals regvals aignet)
                  (aignet-eval-conjunction rest invals regvals aignet))
           (id-eval id invals regvals aignet))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction lit-eval)))))


(define aignet-build-wide-and ((lits lit-listp)
                               (gatesimp gatesimp-p)
                               (strash)
                               (aignet))
  :guard (aignet-lit-listp lits aignet)
  :returns (mv (and-lit litp) new-strash new-aignet)
  :verify-guards nil
  (b* (((when (atom lits))
        (b* ((aignet (aignet-fix aignet)))
          (mv 1 strash aignet)))
       ((mv rest strash aignet) (aignet-build-wide-and (cdr lits) gatesimp strash aignet)))
    (aignet-hash-and (car lits) rest gatesimp strash aignet))
  ///
  (defret aignet-extension-p-of-aignet-build-wide-and
    (aignet-extension-p new-aignet aignet))

  (defret aignet-litp-of-aignet-build-wide-and
    (implies (aignet-lit-listp lits aignet)
             (aignet-litp and-lit new-aignet)))

  (verify-guards aignet-build-wide-and)

  (defret lit-eval-of-aignet-build-wide-and
    (implies (aignet-lit-listp lits aignet)
             (equal (lit-eval and-lit invals regvals new-aignet)
                    (aignet-eval-conjunction lits invals regvals aignet)))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction))))

  (defret stype-counts-of-aignet-build-wide-and
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet)))))

(local (defthm id-eval-of-bit-list-fix-ins
         (equal (id-eval id (bit-list-fix ins) regs aignet)
                (id-eval id ins regs aignet))
         :hints (("goal" :induct (id-eval-ind id aignet)
                  :expand ((:free (ins) (id-eval id ins regs aignet))
                           (:free (lit ins) (lit-eval lit ins regs aignet))
                           (:free (lit1 lit2 ins) (eval-and-of-lits lit1 lit2 ins regs aignet))
                           (:free (lit1 lit2 ins) (eval-xor-of-lits lit1 lit2 ins regs aignet)))))))

(local (defthm id-eval-of-bit-list-fix-regs
         (equal (id-eval id ins (bit-list-fix regs) aignet)
                (id-eval id ins regs aignet))
         :hints (("goal" :induct (id-eval-ind id aignet)
                  :expand ((:free (regs) (id-eval id ins regs aignet))
                           (:free (lit regs) (lit-eval lit ins regs aignet))
                           (:free (lit1 lit2 regs) (eval-and-of-lits lit1 lit2 ins regs aignet))
                           (:free (lit1 lit2 regs) (eval-xor-of-lits lit1 lit2 ins regs aignet)))))))

(local (defthm b-xor-id-eval-equals-lit-eval
         (equal (b-xor (lit->neg x)
                       (id-eval (lit->var x) invals regvals aignet))
                (lit-eval x invals regvals aignet))
         :hints(("Goal" :in-theory (enable lit-eval)))))

(define observability-fix-lit ((lit litp)
                               (config observability-config-p)
                               (aignet)
                               (copy)
                               (strash)
                               (aignet2)
                               (state))
  :returns (mv (new-lit litp) new-copy new-strash new-aignet2 new-aignet new-state)
  :guard (and (fanin-litp lit aignet)
              (aignet-copies-in-bounds copy aignet2)
              (<= (num-ins aignet) (num-ins aignet2))
              (<= (num-regs aignet) (num-regs aignet2)))
  :prepwork ((local (defthm aignet-copies-in-bounds-of-resize
                      (implies (aignet-copies-in-bounds copy aignet)
                               (aignet-copies-in-bounds
                                (resize-list copy n 0) aignet))
                      :hints ((and stable-under-simplificationp
                                   `(:expand (,(car (last clause)))
                                     :in-theory (e/d (nth-lit) (aignet-copies-in-bounds-necc))
                                     :do-not-induct t
                                     :use ((:instance aignet-copies-in-bounds-necc
                                            (n (aignet-copies-in-bounds-witness
                                                (resize-list copy n 0) aignet)))))))))
             (local (defret aignet-litp-linear-of-aignet-build-wide-and
                      (implies (aignet-lit-listp lits aignet)
                               (<= (lit->var and-lit) (fanin-count new-aignet)))
                      :hints (("goal" :use aignet-litp-of-aignet-build-wide-and
                               :in-theory (e/d (aignet-idp)
                                               (aignet-litp-of-aignet-build-wide-and))))
                      :fn aignet-build-wide-and
                      :rule-classes :linear))
             ;; (local (defthm max-fanin-less-than-lit->var
             ;;          (implies (aignet-litp lit aignet)
             ;;                   (<= (lit-id lit) (fanin-count aignet)))
             ;;          :hints(("Goal" :in-theory (e/d (aignet-litp find-max-fanin fanin-count)
             ;;                                         (FANIN-IF-CO-ID-LTE-MAX-FANIN))))))
             (local (defthm fanin-count-<-plus-1
                      (< (fanin-count x) (+ 1 (fanin-count x))))))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp))))
  (b* (((mv hyps rest) (observability-split-supergate (lit-id lit) config aignet))
       ((observability-config config))
       ((mv hyp concl aignet)
        (b* (((acl2::local-stobjs strash)
              (mv strash hyp concl aignet))
             ((mv hyp strash aignet) (aignet-build-wide-and hyps config.gatesimp strash aignet))
             ((mv concl strash aignet) (aignet-build-wide-and rest config.gatesimp strash aignet)))
          (mv strash hyp concl aignet)))
       (- (cw "Observability input: hyp size ~x0, concl ~x1~%"
              (count-gates-mark (lit-id hyp) aignet)
              (count-gates-mark (lit-id concl) aignet)))
       (copy (resize-lits (num-fanins aignet) copy))
       (copy (aignet-copy-set-ins 0 aignet copy aignet2))
       (copy (aignet-copy-set-regs 0 aignet copy aignet2))
       ((mv conjunction copy strash aignet2 state)
        (observability-fix-hyp/concl hyp concl aignet copy config.gatesimp strash aignet2 state)))
    (mv (lit-negate-cond conjunction (lit-neg lit))
        copy strash aignet2 aignet state))
  ///
  (defret aignet-extension-p-of-observability-fix-lit-1
    (aignet-extension-p new-aignet aignet))

  (defret stype-counts-of-observability-fix-lit-1
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (defret aignet-extension-p-of-observability-fix-lit-2
    (aignet-extension-p new-aignet2 aignet2))

  (defret stype-counts-of-observability-fix-lit-2
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret copy-length-of-<fn>
    (implies (aignet-litp lit aignet)
             (equal (len new-copy)
                    (num-fanins new-aignet))))

  ;; (defret copy-size-of-observability-fix-lit
  ;;   (implies (aignet-litp lit aignet)
  ;;            (< (max-fanin new-aignet) (len new-copy)))
  ;;   :hints ('(:expand (<call>)))
  ;;   :rule-classes :linear)

  (defret copies-in-bounds-of-observability-fix-lit
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-litp lit aignet)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (and (aignet-copies-in-bounds new-copy new-aignet2)
                  (aignet-litp new-lit new-aignet2)))
    :hints ('(:expand (<call>))))

  (local (defthm aignet-eval-conjunction-of-extension
           (implies (and (aignet-extension-binding)
                         (aignet-lit-listp lits orig))
                    (equal (aignet-eval-conjunction lits invals regvals new)
                           (aignet-eval-conjunction lits invals regvals orig)))
           :hints(("Goal" :in-theory (enable aignet-eval-conjunction)))))

  (defret eval-of-observability-fix-lit
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  ;; (aignet-litp hyp aignet)
                  (aignet-litp lit aignet)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (equal (lit-eval new-lit invals regvals new-aignet2)
                    (lit-eval lit invals regvals aignet))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))





(define observability-fix-outs ((n natp)
                                (config observability-config-p)
                                (aignet)
                                (copy)
                                (strash)
                                (aignet2)
                                (state))
  :guard (and (<= (num-ins aignet) (num-ins aignet2))
              (<= (num-regs aignet) (num-regs aignet2))
              (aignet-copies-in-bounds copy aignet2)
              (<= n (num-outs aignet)))
  :measure (nfix (- (num-outs aignet) (nfix n)))
  :returns (mv new-copy new-strash new-aignet2 new-aignet new-state)
  (b* ((aignet (aignet-fix aignet))
       (aignet2 (aignet-fix aignet2))
       ((when (mbe :logic (zp (- (num-outs aignet) (nfix n)))
                   :exec (Eql (num-outs aignet) n)))
        (mv copy strash aignet2 aignet state))
       (fanin-lit (outnum->fanin n aignet))
       ((mv copy-lit copy strash aignet2 aignet state)
        (observability-fix-lit fanin-lit config aignet copy strash aignet2 state))
       (aignet2 (aignet-add-out copy-lit aignet2)))
    (observability-fix-outs (1+ (lnfix n)) config aignet copy strash aignet2 state))
  ///
  (fty::deffixequiv observability-fix-outs)

  (defret aignet-extension-p-of-observability-fix-outs-2
    (aignet-extension-p new-aignet2 aignet2))

  (defret aignet-extension-p-of-observability-fix-outs-1
    (aignet-extension-p new-aignet aignet))

  (defret stype-counts-of-observability-fix-outs-2
    (implies (and (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
                  (not (equal (stype-fix stype) :po)))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret stype-counts-of-observability-fix-outs-1
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (defret copies-in-bounds-of-observability-fix-outs
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret num-outs-of-observability-fix-outs
    (equal (stype-count :po new-aignet2)
           (+ (max 0 (- (num-outs aignet) (nfix n))) (num-outs aignet2))))

  ;; (local (include-book "arithmetic/top" :dir :system))

  (local (in-theory (disable lookup-id-implies-aignet-idp)))

  (defret output-eval-of-observability-fix-outs
    (implies (and (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2))
                  (aignet-copies-in-bounds copy aignet2))
             (equal (output-eval m invals regvals new-aignet2)
                    (if (or (< (nfix m) (num-outs aignet2))
                            (<= (+ (num-outs aignet2) (- (num-outs aignet) (nfix n))) (nfix m)))
                        (output-eval m invals regvals aignet2)
                      (output-eval (+ (- (nfix m) (num-outs aignet2)) (nfix n)) invals regvals aignet))))
    :hints(("Goal" :in-theory (enable output-eval)
            :induct <call>
            :expand (<call>))
           (and stable-under-simplificationp
                '(:expand ((:free (a b) (lookup-stype m :po (cons a b))))))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(define observability-fix-nxsts ((n natp)
                                 (config observability-config-p)
                                 (aignet)
                                 (copy)
                                 (strash)
                                 (aignet2)
                                 (state))
  :guard (and (<= (num-ins aignet) (num-ins aignet2))
              (<= (num-regs aignet) (num-regs aignet2))
              (aignet-copies-in-bounds copy aignet2)
              (<= n (num-regs aignet)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :returns (mv new-copy new-strash new-aignet2 new-aignet new-state)
  (b* ((aignet (aignet-fix aignet))
       (aignet2 (aignet-fix aignet2))
       ((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (Eql (num-regs aignet) n)))
        (mv copy strash aignet2 aignet state))
       (fanin-lit (regnum->nxst n aignet))
       ((mv copy-lit copy strash aignet2 aignet state)
        (observability-fix-lit fanin-lit config aignet copy strash aignet2 state))
       (aignet2 (aignet-set-nxst copy-lit n aignet2)))
    (observability-fix-nxsts (1+ (lnfix n)) config aignet copy strash aignet2 state))
  ///
  (fty::deffixequiv observability-fix-nxsts)

  (defret aignet-extension-p-of-observability-fix-nxsts-2
    (aignet-extension-p new-aignet2 aignet2))

  (defret stype-counts-of-observability-fix-nxsts-2
    (implies (and (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
                  (not (equal (stype-fix stype) :nxst)))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret aignet-extension-p-of-observability-fix-nxsts-1
    (aignet-extension-p new-aignet aignet))

  (defret stype-counts-of-observability-fix-nxsts-1
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (defret copies-in-bounds-of-observability-fix-nxsts
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (local (include-book "arithmetic/top" :dir :system))

  (local (defthmd stype-count-of-cdr-lookup-stype-dumb
           (implies (and (natp n)
                         (< n (stype-count :reg aignet))
                         (<= (stype-count :reg aignet) (stype-count :reg aignet2)))
                    (equal (stype-count :reg (cdr (lookup-stype n :reg aignet2)))
                           n))))

  (local (defret lookup-reg->nxst-of-observability-fix-nxsts-out-of-range
           (implies (and (<= (nfix k) (num-regs aignet2))
                         (<= (num-regs aignet) (num-regs aignet2))
                         (< (nfix k) (nfix n)))
                    (equal (lookup-reg->nxst k new-aignet2)
                           (lookup-reg->nxst k aignet2)))
           :hints (("goal" :induct <call> :expand (<call>)
                    :in-theory (enable aignet-idp
                                       stype-count-of-cdr-lookup-stype-dumb))
                   (and stable-under-simplificationp
                        '(:expand ((:free (a b) (lookup-reg->nxst k (cons a b)))))))))

  ;; (local (defthm reg-id->nxst-lit-of-lookup-stype
  ;;          (equal (reg-id->nxst-lit (fanin-count (lookup-stype n :reg aignet)) aignet)
  ;;                 (fanin-if-co (lookup-regnum->nxst n aignet)))
  ;;          :hints(("Goal" :in-theory (enable fanin-if-co reg-id->nxst-lit)))))

  (local (in-theory (disable lookup-id-implies-aignet-idp)))


  (defret nxst-eval-of-observability-fix-nxsts
    (implies (and (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2))
                  (aignet-copies-in-bounds copy aignet2))
             (equal (nxst-eval m invals regvals new-aignet2)
                    (if (or (< (nfix m) (nfix n))
                            (<= (num-regs aignet) (nfix m)))
                        (nxst-eval m invals regvals aignet2)
                      (nxst-eval m invals regvals aignet))))
    :hints(("Goal" :in-theory (enable* nxst-eval
                                       acl2::arith-equiv-forwarding
                                       lookup-reg->nxst-out-of-bounds)
            :induct <call>
            :expand (<call>))
           (and stable-under-simplificationp
                '(:expand ((:free (a b) (lookup-reg->nxst m (cons a b))))))
           (and stable-under-simplificationp
                '(:cases ((< (nfix m) (num-regs aignet2)))))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(define observability-fix-core ((aignet)
                                (aignet2)
                                (config observability-config-p)
                                (state))
  :returns (mv new-aignet2 new-aignet new-state)
  :prepwork ((local (defthm aignet-copies-in-bounds-of-nil
                      (aignet-copies-in-bounds nil aignet)
                      :hints(("Goal" :in-theory (enable aignet-copies-in-bounds nth-lit nth))))))
  (b* (((acl2::local-stobjs copy strash)
        (mv copy strash aignet2 aignet state))
       (aignet2 (aignet-init (num-outs aignet)
                             (num-regs aignet)
                             (num-ins aignet)
                             (num-fanins aignet)
                             aignet2))
       (aignet2 (aignet-add-ins (num-ins aignet) aignet2))
       (aignet2 (aignet-add-regs (num-regs aignet) aignet2))
       ((mv copy strash aignet2 aignet state)
        (observability-fix-outs 0 config aignet copy strash aignet2 state))
       ((mv copy strash aignet2 aignet state)
        (observability-fix-nxsts 0 config aignet copy strash aignet2 state)))
    (mv copy strash aignet2 aignet state))
  ///
  (defret num-ins-of-observability-fix-core
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-observability-fix-core
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-observability-fix-core
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (local (defthm output-eval-of-non-output-extension
           (implies (and (aignet-extension-binding)
                         (equal (stype-count :po new)
                                (stype-count :po orig)))
                    (equal (output-eval n invals regvals new)
                           (output-eval n invals regvals orig)))
           :hints(("Goal" :in-theory (enable output-eval)))))

  (local
   (defret outs-comb-equiv-of-observability-fix-core
     (outs-comb-equiv new-aignet2 aignet)
     :hints((and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:computed-hint-replacement
                     ((let ((witness (acl2::find-call-lst
                                      'outs-comb-equiv-witness
                                      clause)))
                        `(:clause-processor
                          (acl2::simple-generalize-cp
                           clause '(((mv-nth '0 ,witness) . outnum)
                                    ((mv-nth '1 ,witness) . invals)
                                    ((mv-nth '2 ,witness) . regvals))))))
                     :expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t))))))

  (local
   (defret nxsts-comb-equiv-of-observability-fix-core
     (nxsts-comb-equiv new-aignet2 aignet)
     :hints((and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:computed-hint-replacement
                     ((let ((witness (acl2::find-call-lst
                                      'nxsts-comb-equiv-witness
                                      clause)))
                        `(:clause-processor
                          (acl2::simple-generalize-cp
                           clause '(((mv-nth '0 ,witness) . regnum)
                                    ((mv-nth '1 ,witness) . invals)
                                    ((mv-nth '2 ,witness) . regvals))))))
                     :expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t))))))

  (defret comb-equiv-of-observability-fix-core
    (comb-equiv new-aignet2 aignet)
    :hints(("Goal" :in-theory (enable comb-equiv))))

  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (let ((aignet2 nil)) <call>))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



(define observability-fix ((aignet  "Input aignet")
                           (aignet2 "New aignet -- will be emptied")
                           (config observability-config-p
                                   "Settings for the transform")
                           (state))
  :guard-debug t
  :returns (mv new-aignet2 new-state)
  :parents (aignet-comb-transforms)
  :short "Transform the aignet so that some observability don't-care conditions
          don't affect the logical equivalence of nodes."
  :long "<p>This is mainly intended to be used on a single-output aignet, and
mainly as a precursor to fraiging.  Settings for the transform can be tweaked
using the @('config') input, which is an @(see observability-config)
object.</p>

<p>Suppose we have a single-output AIG whose function is @('A & B'), and that
@('A') is a small, simple function and @('B') a large, complicated function.
Sometimes it is the case that within @('B') there are nodes that are logically
inequivalent, but are equivalent when @('A') is assumed.  We'd like to be able
to apply @(see fraig)ing and get rid of these redundancies.  But they aren't
strictly equivalent, just equivalent under an observability condition.</p>

<p>The observability transform detects such situations and applies the
following transform, which restricts the inputs to @('B') so that it only sees
inputs satisfying @('A').  This makes such observability-equivalent nodes truly
equivalent and allows fraiging to collapse them together.</p>

<p>First, decompose the topmost AND in the output and sort conjuncts into small
and large ones according to some thresholds.  The small ones are conjoined
together as @('A') and the large ones as @('B').  If no conjuncts are smaller
enough, the transform exits without doing anything.</p>

<p>Next, find a satisfying assignment for @('A').  (If it is unsatisfiable, the
output is constant false.)  For each combinational input @('i') that is in the
minimized satisfying assignment with value @('v'), make a mux @('A ? i : v').
Then replace the occurrences of these inputs in @('B') with these muxes.
Finally, conjoin this modified copy of @('B') with @('A').</p>

<p>This provably produces a combinationally equivalent network, since @('B') is
only changed in cases where @('A') des not hold:</p>

@(thm observability-fix-comb-equivalent)"

  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet2 aignet-tmp state))
       (aignet2 (aignet-raw-copy aignet aignet2))
       ((mv aignet-tmp aignet2 state) (observability-fix-core aignet2 aignet-tmp config state))
       (aignet2 (aignet-prune-comb aignet-tmp aignet2 (observability-config->gatesimp config))))
    (mv aignet2 aignet-tmp state))
  ///
  (defret num-ins-of-observability-fix
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-observability-fix
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-observability-fix
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret observability-fix-comb-equivalent
    (comb-equiv new-aignet2 aignet))

  (defthm normalize-input-of-observability-fix
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (observability-fix aignet aignet2 config state)
                    (observability-fix aignet nil config state))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(define observability-fix! ((aignet  "Input aignet -- will be replaced with transformation result")
                            (config observability-config-p)
                            (state))
  :guard-debug t
  :returns (mv new-aignet new-state)
  :parents (observability-fix)
  :short "Like @(see observability-fix), but overwrites the original network instead of returning a new one."
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet aignet-tmp state))
       ((mv aignet-tmp aignet state) (observability-fix-core aignet aignet-tmp config state))
       (aignet (aignet-prune-comb aignet-tmp aignet (observability-config->gatesimp config))))
    (mv aignet aignet-tmp state))
  ///
  (defret num-ins-of-observability-fix!
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-regs-of-observability-fix!
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret num-outs-of-observability-fix!
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret observability-fix!-comb-equivalent
    (comb-equiv new-aignet aignet))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



(fty::defprod m-assum-n-output-observability-config
  ((gatesimp gatesimp-p :default (default-gatesimp)
             "Gate simplification parameters.  Warning: This transform will do
              nothing good if hashing is turned off."))
  :parents (observability-fix comb-transform)
  :short "Configuration object for the @(see m-assum-n-output-observability) aignet transform."
  :tag :m-assum-n-output-observability-config)




(define m-assum-n-output-observability ((m natp)
                                        (n natp)
                                        aignet
                                        aignet2
                                        (config m-assum-n-output-observability-config-p)
                                        state)
  :guard (<= (+ m n) (num-outs aignet))
  :returns (mv new-aignet2 new-state)
  (declare (ignorable n))
  (b* (((acl2::local-stobjs copy strash)
        (mv copy strash aignet2 state))
       ((mv copy aignet2) (init-copy-comb aignet copy aignet2))
       (m (mbe :logic (min (nfix m) (num-outs aignet))
               :exec m))
       (hyps (output-lit-range 0 m aignet))
       (concls (output-lit-range m (- (num-outs aignet) m) aignet))
       ((mv ?hyp new-hyps new-concls copy strash aignet2 state)
        (observability-fix-hyps/concls hyps concls aignet copy
                                       (m-assum-n-output-observability-config->gatesimp config)
                                       strash aignet2 state))
       (aignet2 (aignet-add-outs new-hyps aignet2))
       (aignet2 (aignet-add-outs new-concls aignet2)))
    (mv copy strash aignet2 state))
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

  ;; (local (defthm output-eval-of-aignet-add-outs
  ;;          (equal (output-eval i invals regvals
  ;;                              (aignet-add-outs lits aignet))
  ;;                 (cond ((< (nfix i) (num-outs aignet))
  ;;                        (output-eval i invals regvals aignet))
  ;;                       ((< (nfix i) (+ (num-outs aignet) (len lits)))
  ;;                        (lit-eval (nth (- (nfix i) (num-outs aignet)) lits)
  ;;                                  invals regvals aignet))
  ;;                       (t 0)))
  ;;          :hints(("Goal" :in-theory (enable output-eval)))))

  (defret <fn>-eval-assumptions
    (implies (< (nfix i) (nfix m))
             (equal (output-eval i invals regvals new-aignet2)
                    (output-eval i invals regvals aignet)))
    :hints(("Goal" :in-theory (enable output-eval))))

  (local (in-theory (enable output-range-equiv-by-badguy)))

  (local (defthm aignet-litp-of-nth
           (implies (aignet-lit-listp lits aignet)
                    (aignet-litp (nth n lits) aignet))
           :hints(("Goal" :in-theory (enable nth aignet-lit-listp)))))

  (defret <fn>-eval-conclusion
    (implies (And (< (nfix i) (+ (nfix m) (nfix n)))
                  (equal (conjoin-output-range 0 m invals regvals aignet) 1))
             (equal (output-eval i invals regvals new-aignet2)
                    (output-eval i invals regvals aignet)))
    :hints(("Goal" :in-theory (enable output-eval))))

  (defret w-state-of-<fn>
    (equal (w new-state)
           (w state)))

  (defret list-of-outputs-of-<fn>
    (equal (list new-aignet2 new-state) <call>)))
