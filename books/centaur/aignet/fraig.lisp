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

(include-book "sweep")
(include-book "transform-utils")
(include-book "centaur/aignet/ipasir" :dir :system)
(include-book "equiv-classes")
(include-book "centaur/aignet/prune" :dir :system)
(include-book "centaur/bitops/extra-defs" :dir :system)
(include-book "std/stobjs/nested-stobjs" :dir :system)
(include-book "centaur/misc/seed-random" :dir :system)
(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system ))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (in-theory (disable nth update-nth nfix ifix (tau-system)
                           resize-list
                           acl2::resize-list-when-atom)))
(local (std::add-default-post-define-hook :fix))

;; BOZO skipping node-list-fix congruence proofs here
(local (table fty::fixtypes 'fty::fixtype-alist
              (b* ((fixtype-alist (cdr (assoc 'fty::fixtype-alist (table-alist 'fty::fixtypes world)))))
                (remove-equal (assoc 'aignet fixtype-alist)
                              fixtype-alist))))

(local (xdoc::set-default-parents fraig))


(fty::defprod fraig-config
  ((initial-sim-words posp "Number of 32-bit simulation words per node for initial simulation" :default 4)
   (initial-sim-rounds posp "Number of times to simulate initially" :default 10)
   (sim-words posp "Number of 32-bit simulation words per node for simulation during fraiging" :default 1)
   (ipasir-limit acl2::maybe-natp "Ipasir effort limit" :default 8)
   (ipasir-recycle-count acl2::maybe-natp "Number of callbacks after which to recycle the solver" :default 1000)
   (ctrex-queue-limit acl2::maybe-natp "Limit to number of counterexamples that may be queued before resimulation" :default 16)
   (ctrex-force-resim booleanp "Force resimulation of a counterexample before checking another node in the same equivalence class" :default t)
   (random-seed-name symbolp "Name to use for seed-random, or NIL to not reseed the random number generator")
   (outs-only booleanp "Only check the combinational outputs of the network" :default nil)
   (gatesimp gatesimp-p :default (default-gatesimp)
             "Gate simplification parameters.  Warning: This transform will do
              nothing good if hashing is turned off."))
  :parents (fraig comb-transform)
  :short "Configuration object for the @(see fraig) aignet transform."
  :tag :fraig-config)

(defconst *fraig-default-config* (make-fraig-config))

      



(defsection fraig-stats
  (make-event
   (b* ((fields '((fraig-initial-nclasses :type (integer 0 *) :initially 0)
                  (fraig-initial-nclass-lits :type (integer 0 *) :initially 0)
                  (fraig-initial-nconst-lits :type (integer 0 *) :initially 0)
                  (fraig-gates-processed :type (integer 0 *) :initially 0)
                  (fraig-coincident-nodes :type (integer 0 *) :initially 0)
                  (fraig-unsat-checks :type (integer 0 *) :initially 0)
                  (fraig-sat-checks :type (integer 0 *) :initially 0)
                  (fraig-failed-checks :type (integer 0 *) :initially 0)
                  (fraig-class-lits-refined :type (integer 0 *) :initially 0)
                  (fraig-const-lits-refined :type (integer 0 *) :initially 0)
                  (fraig-resims          :type (integer 0 *) :initially 0)
                  (fraig-classes-refined :type (integer 0 *) :initially 0)
                  (fraig-ipasir-recycles :type (integer 0 *) :initially 0)
                  (fraig-ipasir-prev-callbacks :type (integer 0 *) :initially 0)
                  (fraig-last-chance-refines :type (integer 0 *) :initially 0)
                  (fraig-last-chance-refines-forced :type (integer 0 *) :initially 0)
                  (fraig-last-chance-refines-forced-proved :type (integer 0 *) :initially 0))))
     `(progn (defstobj fraig-stats ,@fields)
             (local (defund unhide (x) x))
             (local (defthm unhide-of-hide
                      (equal (unhide (hide x)) x)
                      :hints (("goal" :in-theory (enable unhide)
                               :expand ((:free (x) (hide x)))))))
             (local (defthm open-nth
                      (equal (nth n x)
                             (if (zp n)
                                 (car x)
                               (unhide (hide (nth (+ -1 n) (cdr x))))))
                      :hints(("Goal" :in-theory (enable nth)))))
             (defthmd fraig-stats-implies-natp-of-nth
               (implies (and (fraig-statsp fraig-stats)
                             (< (nfix n) ,(len fields)))
                        (natp (nth n fraig-stats)))
               :rule-classes ((:rewrite :backchain-limit-lst (0 nil))
                              :type-prescription))))))

(define fraig-total-checks (fraig-stats)
  :returns (checks natp :rule-classes :type-prescription)
  (lnfix (+ (fraig-unsat-checks fraig-stats)
            (fraig-sat-checks fraig-stats)
            (fraig-failed-checks fraig-stats))))

(local (in-theory (e/d (fraig-stats-implies-natp-of-nth)
                       (fraig-statsp))))
                              

(define print-fraig-stats-initial (fraig-stats)
  (cw "Fraig initial equiv classes: ~x0     const lits: ~x1    class lits: ~x2~%"
      (fraig-initial-nclasses fraig-stats)
      (fraig-initial-nconst-lits fraig-stats)
      (fraig-initial-nclass-lits fraig-stats)))

(define print-fraig-stats-noninitial (classes ipasir fraig-stats &key ((start-node natp) '0))
  :guard (and (non-exec (not (eq (ipasir::ipasir$a->status ipasir) :undef)))
              (<= start-node (classes-size classes)))
  (b* (((mv nclasses nconst-lits nclass-lits) (classes-counts classes :start-node start-node)))
    (cw! "Current gates: ~x0  built: ~x1 coincident: ~x2 proved: ~x3~%"
        (fraig-gates-processed fraig-stats)
        (- (fraig-gates-processed fraig-stats)
           (+ (fraig-coincident-nodes fraig-stats)
              (fraig-unsat-checks fraig-stats)))
        (fraig-coincident-nodes fraig-stats)
        (fraig-unsat-checks fraig-stats))
    (cw! "       classes: ~x0     const lits: ~x1    class lits: ~x2~%"
        nclasses nconst-lits nclass-lits)
    (cw! "       Refinements: resims: ~x0 class lits: ~x1 const lits: ~x2 classes: ~x3 last-chance: ~x4 last-chance(forced): ~x5 last-chance/forced/proved: ~x6~%"
        (fraig-resims fraig-stats)
        (fraig-class-lits-refined fraig-stats)
        (fraig-const-lits-refined fraig-stats)
        (fraig-classes-refined fraig-stats)
        (fraig-last-chance-refines fraig-stats)
        (fraig-last-chance-refines-forced fraig-stats)
        (fraig-last-chance-refines-forced-proved fraig-stats))
    (cw! "       SAT checks: ~x0  unsat: ~x1 sat: ~x2 failed: ~x3~%"
        (+ (fraig-unsat-checks fraig-stats)
           (fraig-sat-checks fraig-stats)
           (fraig-failed-checks fraig-stats))
        (fraig-unsat-checks fraig-stats)
        (fraig-sat-checks fraig-stats)
        (fraig-failed-checks fraig-stats))
    (cw! "                     recycles: ~x0 callbacks: ~x1~%"
        (fraig-ipasir-recycles fraig-stats)
        (+ (ipasir-callback-count ipasir)
           (fraig-ipasir-prev-callbacks fraig-stats)))))



(define aignet-maybe-update-refs ((prev-count natp)
                                  (aignet-refcounts)
                                  (aignet))
  ;; Assuming at most 1 node has been added, update the refcounts for that
  ;; node.  Note: even if we don't use that node (because another node is
  ;; proven equivalent), we leave its refcounts because they may have already
  ;; affected the cnf generation.
  :returns (new-refcounts)
  (b* ((aignet-refcounts (if (< (u32-length aignet-refcounts) (num-fanins aignet))
                             (resize-u32 (max 16 (* 2 (num-fanins aignet))) aignet-refcounts)
                           aignet-refcounts))
       ((unless (< (lnfix prev-count) (num-fanins aignet)))
        aignet-refcounts)
       (id (1- (num-fanins aignet))))
    (aignet-case
      (id->type id aignet)
      :gate  (b* ((aignet-refcounts (set-u32 id 0 aignet-refcounts))
                  (id0 (lit-id (gate-id->fanin0 id aignet)))
                  (id1 (lit-id (gate-id->fanin1 id aignet)))
                  (aignet-refcounts
                   (set-u32 id0 (nfix (+ 1 (get-u32 id0 aignet-refcounts)))
                            aignet-refcounts)))
               (set-u32 id1 (nfix (+ 1 (get-u32 id0 aignet-refcounts)))
                        aignet-refcounts))
      :const aignet-refcounts
      :in aignet-refcounts
      :out aignet-refcounts))
  ///
  (defret new-refcounts-length-of-aignet-maybe-udpate-refs
    (< (fanin-count aignet) (len new-refcounts))
    :rule-classes :linear))

    ;; (aignet-count-refs-step n aignet-refcounts aignet)))


(defthm aignet-copies-ok-implies-linear
  (implies (aignet-copies-in-bounds copy aignet)
           (<= (lit-id (nth-lit m copy)) (fanin-count aignet)))
  :hints(("Goal" :use ((:instance aignet-copies-in-bounds-necc
                        (n m)))
          :in-theory (disable aignet-copies-in-bounds-necc)))
  :rule-classes :linear)

;; (defthmd lit-id-bound-by-max-fanin-when-aignet-litp
;;   (implies (aignet-litp lit aignet)
;;            (<= (lit-id lit) (max-fanin aignet))))

(defthm aignet-hash-and-bound-by-max-fanin
  (b* (((mv and-lit & new-aignet)
        (aignet-hash-and lit0 lit1 gatesimp strash aignet)))
    (implies (and (aignet-litp lit0 aignet)
                  (aignet-litp lit1 aignet))
             (<= (lit-id and-lit) (fanin-count new-aignet))))
  :hints (("goal" :in-theory (e/d (aignet-idp)
                                  (aignet-litp-of-aignet-hash-and))
           :use ((:instance aignet-litp-of-aignet-hash-and (lit1 lit0) (lit2 lit1)))))
  :rule-classes (:rewrite :linear))

(defthm aignet-hash-xor-bound-by-max-fanin
  (b* (((mv and-lit & new-aignet)
        (aignet-hash-xor lit0 lit1 gatesimp strash aignet)))
    (implies (and (aignet-litp lit0 aignet)
                  (aignet-litp lit1 aignet))
             (<= (lit-id and-lit) (fanin-count new-aignet))))
  :hints (("goal" :in-theory (e/d (aignet-idp)
                                  (aignet-litp-of-aignet-hash-xor))
           :use ((:instance aignet-litp-of-aignet-hash-xor (lit1 lit0) (lit2 lit1)))))
  :rule-classes (:rewrite :linear))


(defthm aignet-copies-ok-implies-aignet-litp
  (implies (and (aignet-copies-in-bounds copy aignet)
                (aignet-extension-p aignet2 aignet))
           (aignet-litp (nth-lit m copy) aignet2)))

;; (defthm aignet-cogpies-ok-of-update-later
;;   (implies (and (aignet-copies-ok node copy aignet)
;;                 (<= (nfix node) (nfix m)))
;;            (aignet-copies-ok node (update-nth-lit m lit copy) aignet))
;;   :hints(("Goal" :in-theory (enable aignet-copies-ok))))

;; (defthm aignet-copies-ok-of-less
;;   (implies (and (aignet-copies-ok n copy aignet)
;;                 (<= (nfix m) (nfix n)))
;;            (aignet-copies-ok m copy aignet))
;;   :hints(("Goal" :in-theory (enable aignet-copies-ok))))
           





(defthm ipasir-check-equivalence-unsat-when-cnf-for-aignet
  (b* (((mv status ?new-ipasir) (ipasir::ipasir-check-equivalence ipasir lit1 lit2)))
    (implies (and (syntaxp
                   (or (acl2::rewriting-negative-literal-fn
                        `(equal (mv-nth '0 (ipasir::ipasir-check-equivalence ,ipasir ,lit1 ,lit2)) ':unsat)
                        mfc state)
                       (acl2::rewriting-negative-literal-fn
                        `(equal ':unsat (mv-nth '0 (ipasir::ipasir-check-equivalence ,ipasir ,lit1 ,lit2)))
                        mfc state)))
                  (syntaxp (or (cw "passed negative-literal test~%") t))
                  (eval-formula-equiv formula (double-rewrite (ipasir::ipasir$a->formula ipasir)))
                  (syntaxp (or (cw "bound formula: ~x0~%" formula) t))
                  (cnf-for-aignet aignet formula sat-lits)
                  (syntaxp (or (cw "bound aignet: ~x0~%sat-lits: ~x1" aignet sat-lits) t))
                  (sat-lits-wfp sat-lits aignet)
                  (sat-litp lit1 sat-lits)
                  (sat-litp lit2 sat-lits))
             (equal (equal status :unsat)
                    (and (hide (equal status :unsat))
                         (aignet-lits-comb-equivalent (sat-lit->aignet-lit lit1 sat-lits)
                                                      aignet
                                                      (sat-lit->aignet-lit lit2 sat-lits)
                                                      aignet)))))
  :hints (("goal" :expand ((:free (x) (hide x))))
          (and stable-under-simplificationp
               `(:expand (,(car (last clause)))))
          (and stable-under-simplificationp
               (let ((witness (acl2::find-call-lst
                               'aignet-lits-comb-equivalent-witness
                               clause)))
                 `(:clause-processor
                   (acl2::simple-generalize-cp
                    clause '(((mv-nth '0 ,witness) . invals)
                             ((mv-nth '1 ,witness) . regvals))))))
          (and stable-under-simplificationp
               '(:use ((:instance ipasir::ipasir-check-equivalence-unsat
                        (env (aignet->cnf-vals
                              invals regvals cnf-vals sat-lits aignet))
                        (lit1 lit1) (lit2 lit2) (ipasir ipasir)))
                 :in-theory (e/d ()
                                 (ipasir::ipasir-check-equivalence-unsat)))))
  :rule-classes ((:rewrite :match-free :all)))


;; BOZO
(defthm aignet-litp-of-lit-fix
  (equal (aignet-litp (lit-fix x) aignet)
         (aignet-litp x aignet)))


(define ipasir-maybe-recycle ((config fraig-config-p)
                              sat-lits
                              ipasir
                              fraig-stats)
  :returns (mv new-sat-lits new-ipasir new-fraig-stats)
  :guard (non-exec (and (not (eq (ipasir::ipasir$a->status ipasir) :undef))
                        (not (ipasir::ipasir$a->new-clause ipasir))
                        (not (ipasir::ipasir$a->assumption ipasir))))
  (b* (((fraig-config config))
       ((unless (and config.ipasir-recycle-count
                     (<= config.ipasir-recycle-count (ipasir-callback-count ipasir))))
        (b* ((ipasir (ipasir::ipasir-cancel-new-clause ipasir))
             (ipasir (ipasir::ipasir-cancel-assumption ipasir))
             (ipasir (ipasir-input ipasir)))
          (mv sat-lits ipasir fraig-stats)))
       (fraig-stats (update-fraig-ipasir-recycles (+ 1 (fraig-ipasir-recycles fraig-stats)) fraig-stats))
       (fraig-stats (update-fraig-ipasir-prev-callbacks (+ (ipasir-callback-count ipasir)
                                                           (fraig-ipasir-prev-callbacks fraig-stats))
                                                        fraig-stats))
       (ipasir (ipasir-release ipasir))
       (ipasir (ipasir-reinit ipasir))
       (ipasir (ipasir-set-limit ipasir config.ipasir-limit))
       (sat-lits (sat-lits-empty (aignet->sat-length sat-lits) sat-lits)))
    (mv sat-lits ipasir fraig-stats))
  ///
  (defret sat-lits-wfp-of-ipasir-maybe-recycle
    (implies (sat-lits-wfp sat-lits aignet)
             (sat-lits-wfp new-sat-lits aignet)))

  (defret ipasir-new-clause-of-ipasir-maybe-recycle
    (equal (ipasir::ipasir$a->new-clause new-ipasir) nil))

  (defret ipasir-assumption-of-ipasir-maybe-recycle
    (equal (ipasir::ipasir$a->assumption new-ipasir) nil))

  (defret ipasir-status-of-ipasir-maybe-recycle
    (equal (ipasir::ipasir$a->status new-ipasir) :input))

  (defret ipasir-formula-wfp-of-ipasir-maybe-recycle
    (implies (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
             (sat-lit-list-listp (ipasir::ipasir$a->formula new-ipasir) new-sat-lits)))

  (defret cnf-for-aignet-of-ipasir-maybe-recycle
    (implies (cnf-for-aignet aignet (ipasir::ipasir$a->formula ipasir) sat-lits)
             (cnf-for-aignet aignet (ipasir::ipasir$a->formula new-ipasir) new-sat-lits))))
        
(define fraig-stats-count-sat-call ((status symbolp) fraig-stats)
  :hooks nil
  (case status
    (:sat (update-fraig-sat-checks (+ 1 (fraig-sat-checks fraig-stats)) fraig-stats))
    (:unsat (update-fraig-unsat-checks (+ 1 (fraig-unsat-checks fraig-stats)) fraig-stats))
    (otherwise (update-fraig-failed-checks (+ 1 (fraig-failed-checks fraig-stats)) fraig-stats))))
  

(define ipasir-check-aignet-equivalence ((lit1 litp)
                                         (lit2 litp)
                                         (config fraig-config-p)
                                          aignet aignet-refcounts sat-lits ipasir
                                          fraig-stats)
  :guard (and (fanin-litp lit1 aignet)
              (fanin-litp lit2 aignet)
              (sat-lits-wfp sat-lits aignet)
              (< (lit-id lit1) (u32-length aignet-refcounts))
              (< (lit-id lit2) (u32-length aignet-refcounts))
              (non-exec (and (not (eq (ipasir::ipasir$a->status ipasir) :undef))
                             (not (ipasir::ipasir$a->new-clause ipasir))
                             (not (ipasir::ipasir$a->assumption ipasir)))))
  :returns (mv (status (or (equal status :failed)
                           (equal status :unsat)
                           (equal status :sat))
                       :rule-classes ((:forward-chaining :trigger-terms (status))))
               new-sat-lits
               new-ipasir
               new-fraig-stats)
  (b* ((lit1 (lit-fix lit1))
       (lit2 (lit-fix lit2))
       ((mv sat-lits ipasir fraig-stats) (ipasir-maybe-recycle config sat-lits ipasir fraig-stats))
       ((mv sat-lits ipasir) (aignet-lit->ipasir lit1 t aignet-refcounts sat-lits aignet ipasir))
       ((mv sat-lits ipasir) (aignet-lit->ipasir lit2 t aignet-refcounts sat-lits aignet ipasir))
       (sat-lit1 (aignet-lit->sat-lit lit1 sat-lits))
       (sat-lit2 (aignet-lit->sat-lit lit2 sat-lits))
       ((mv status ipasir) (ipasir::ipasir-check-equivalence ipasir sat-lit1 sat-lit2))
       (fraig-stats (fraig-stats-count-sat-call status fraig-stats)))
    (mv status sat-lits ipasir fraig-stats))
  ///

  (defret ipasir-check-aignet-equivalence-ipasir-status
    (equal (ipasir::ipasir$a->status new-ipasir)
           (case status
             (:sat :sat)
             (:unsat :unsat)
             (otherwise :input))))

  (defret ipasir-check-aignet-equivalence-new-clause
    (equal (ipasir::ipasir$a->new-clause new-ipasir) nil))

  (defret ipasir-check-aignet-equivalence-assumption
    (equal (ipasir::ipasir$a->assumption new-ipasir) nil))

  (defret sat-lits-wfp-of-ipasir-check-aignet-equivalence
    (implies (and (sat-lits-wfp sat-lits aignet)
                  ;; (aignet-litp lit1 aignet)
                  ;; (aignet-litp lit2 aignet)
                  )
             (sat-lits-wfp new-sat-lits aignet)))

  ;; (local (acl2::use-trivial-ancestors-check))

  (defret ipasir-formula-wfp-of-ipasir-check-aignet-equivalence
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (aignet-litp lit1 aignet)
                  (aignet-litp lit2 aignet)
                  (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits))
             (sat-lit-list-listp (ipasir::ipasir$a->formula new-ipasir) new-sat-lits)))

  (defret cnf-for-aignet-of-ipasir-check-aignet-equivalence
    (implies (and (cnf-for-aignet aignet (ipasir::ipasir$a->formula ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-litp lit1 aignet)
                  (aignet-litp lit2 aignet)
                  (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits))
             (cnf-for-aignet aignet (ipasir::ipasir$a->formula new-ipasir) new-sat-lits)))

  ;; (local (defthm ipasir-check-equivalence-unsat-when-cnf-for-aignet-special
  ;;          (b* (((mv status ?new-ipasir) (ipasir::ipasir-check-equivalence ipasir lit1 lit2)))
  ;;            (implies (and (syntaxp
  ;;                           (or (acl2::rewriting-negative-literal-fn
  ;;                                `(equal (mv-nth '0 (ipasir::ipasir-check-equivalence ,ipasir ,lit1 ,lit2)) ':unsat)
  ;;                                mfc state)
  ;;                               (acl2::rewriting-negative-literal-fn
  ;;                                `(equal ':unsat (mv-nth '0 (ipasir::ipasir-check-equivalence ,ipasir ,lit1 ,lit2)))
  ;;                                mfc state)))
  ;;                          (cnf-for-aignet aignet (ipasir::ipasir$a->formula ipasir) sat-lits)
  ;;                          (sat-lits-wfp sat-lits aignet)
  ;;                          (sat-litp lit1 sat-lits)
  ;;                          (sat-litp lit2 sat-lits))
  ;;                     (equal (equal status :unsat)
  ;;                            (and (hide (equal status :unsat))
  ;;                                 (aignet-lits-comb-equivalent (sat-lit->aignet-lit lit1 sat-lits)
  ;;                                                              aignet
  ;;                                                              (sat-lit->aignet-lit lit2 sat-lits)
  ;;                                                              aignet)))))

  (local (DEFTHM SAT-LITS-WFP-IMPLIES-SAT-VARP-OF-LOOKUP-AIGNET-ID-bind
           (IMPLIES (AND (bind-free '((aignet . aignet)))
                         (SAT-LITS-WFP SAT-LITS AIGNET)
                         (AIGNET-ID-HAS-SAT-VAR N SAT-LITS))
                    (SAT-VARP (LIT->VAR (AIGNET-ID->SAT-LIT N SAT-LITS))
                              SAT-LITS))))

  (local (DEFTHM
                SAT-LITS-WFP-IMPLIES-LOOKUP-AIGNET-ID-bind
                (IMPLIES
                 (AND
                  (bind-free '((aignet . aignet)) (aignet))
                  (SAT-LITS-WFP SAT-LITS AIGNET)
                  (BIND-FREE (MATCH-EQUIV-OR-REFINEMENT
                                  'VAR-EQUIV
                                  'ID
                                  '(LIT->VAR (AIGNET-ID->SAT-LIT N SAT-LITS))
                                  MFC STATE)
                             (N))
                  (VAR-EQUIV ID
                             (LIT->VAR (AIGNET-ID->SAT-LIT N SAT-LITS)))
                  (AIGNET-ID-HAS-SAT-VAR N SAT-LITS))
                 (EQUAL (SAT-VAR->AIGNET-LIT ID SAT-LITS)
                        (MK-LIT N
                                (LIT->NEG (AIGNET-ID->SAT-LIT N SAT-LITS)))))
                :hints (("goal" :use ((:instance sat-lits-wfp-implies-lookup-aignet-id))
                         :in-theory (disable sat-lits-wfp-implies-lookup-aignet-id)))))

  (defret ipasir-check-aignet-equivalence-unsat
    (implies (and (cnf-for-aignet aignet (ipasir::ipasir$a->formula ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet)
                  (aignet-litp lit1 aignet)
                  (aignet-litp lit2 aignet)
                  (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits))
             (equal (equal status :unsat)
                    (and (hide (equal status :unsat))
                         (aignet-lits-comb-equivalent lit1 aignet lit2 aignet))))
    :hints (("goal" :expand ((:free (x) (hide x))))
            (and stable-under-simplificationp
                 '(:expand nil
                   :use ((:instance cnf-for-aignet-of-ipasir-check-aignet-equivalence))
                   :in-theory (disable CNF-FOR-AIGNET-PRESERVED-BY-AIGNET-LIT->CNF-NORMALIZED
                                       cnf-for-aignet-of-ipasir-check-aignet-equivalence
                                       )))))

  (defret ipasir-check-aignet-equivalence-lit1-has-sat-vars
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (equal id (lit-id lit1))
                  (aignet-litp lit1 aignet))
             (aignet-id-has-sat-var id new-sat-lits)))

  (defret ipasir-check-aignet-equivalence-lit2-has-sat-vars
    (implies (and (sat-lits-wfp sat-lits aignet)
                  (equal id (lit-id lit2))
                  (aignet-litp lit2 aignet))
             (aignet-id-has-sat-var id new-sat-lits))))

     
(define s32v-install-bit ((row natp)
                          (bitnum natp)
                          (val bitp)
                          s32v)
  :prepwork ((local (include-book "ihs/quotient-remainder-lemmas" :dir :system)))
  :guard (and (< row (s32v-nrows s32v))
              (< bitnum (* 32 (s32v-ncols s32v))))
  :guard-hints (("goal" :in-theory (enable acl2::logtail)))
  :returns (new-s32v)
  (b* ((col (ash (lnfix bitnum) -5))
       (bitcol (logand (lnfix bitnum) #x1f))
       (prev-val (s32v-get2 row col s32v))
       (new-val (acl2::fast-logext 32 (acl2::install-bit bitcol val prev-val))))
    (s32v-set2 row col new-val s32v))
  ///
  (defret ncols-of-s32v-install-bit
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v)))

  (defret nrows-of-s32v-install-bit
    (implies (< (nfix row) (len (stobjs::2darr->rows s32v)))
             (equal (len (stobjs::2darr->rows new-s32v))
                    (len (stobjs::2darr->rows s32v))))))

(define s32v-get-bit ((row natp)
                      (bitnum natp)
                      s32v)
  :prepwork ((local (include-book "ihs/quotient-remainder-lemmas" :dir :system)))
  :guard (and (< row (s32v-nrows s32v))
              (< bitnum (* 32 (s32v-ncols s32v))))
  :guard-hints (("goal" :in-theory (enable acl2::logtail)))
  :returns (bit bitp :rule-classes :type-prescription)
  (b* ((col (ash (lnfix bitnum) -5))
       (bitcol (logand (lnfix bitnum) #x1f))
       (s32-val (s32v-get2 row col s32v)))
    (acl2::logbit bitcol s32-val)))



(defstobj-clone ctrex-eval bitarr :prefix "CTREX-EVAL-")

(define fraig-record-sat-ctrex-rec ((id natp)
                                    mark ;; bitarr
                                    aignet2
                                    sat-lits
                                    ipasir
                                    ctrex-eval) ;; bitarr
  :measure (nfix id)
  :guard (and (id-existsp id aignet2)
              (<= (num-fanins aignet2) (bits-length ctrex-eval))
              (<= (num-fanins aignet2) (bits-length mark))
              (non-exec (eq (ipasir::ipasir$a->status ipasir) :sat))
              (sat-lits-wfp sat-lits aignet2)
              ;; Strong guards. Note: this is useful for debugging this function.
              ;; Uncomment the things marked Strong guards to enable.
              ;; (non-exec
              ;;  (and (ec-call (cnf-for-aignet aignet2 (ipasir::ipasir$a->formula ipasir) sat-lits))
              ;;       (b* ((env (ec-call (ipasir::cube-to-env
              ;;                                      (ipasir::ipasir$a->solution ipasir)
              ;;                                      nil))))
              ;;         (and (equal (eval-formula (ipasir::ipasir$a->formula ipasir)
              ;;                                   env)
              ;;                     1)
              ;;              (or (not val)
              ;;                  (equal val (lit-eval lit
              ;;                                       (ec-call (cnf->aignet-invals
              ;;                                                 nil env sat-lits aignet2))
              ;;                                       (ec-call (cnf->aignet-regvals
              ;;                                                 nil env sat-lits aignet2))
              ;;                                       aignet2)))))))
              )
  :verify-guards nil
  :returns (mv new-mark new-ctrex-eval)
  (b* (((when (eql 1 (get-bit id mark))) (mv mark ctrex-eval))
       (slot0 (id->slot id 0 aignet2))
       (slot1 (id->slot id 1 aignet2))
       (type (snode->type slot0))
       (regp (snode->regp slot1))
       (sat-val (b* ((has-sat-lit (aignet-id-has-sat-var id sat-lits))
                    ((unless has-sat-lit) nil)
                    (sat-lit (aignet-id->sat-lit id sat-lits)))
                 (ipasir::ipasir-val ipasir sat-lit))))
    (aignet-case type regp
      :pi
      (b* (((unless sat-val)
            (raise "Got to a primary input and had no assigned sat literal value.")
            (mv mark ctrex-eval))
           (ctrex-eval (set-bit id sat-val ctrex-eval))
           (mark (set-bit id 1 mark)))
        (mv mark ctrex-eval))
      :reg
      (b* (((unless sat-val)
            (raise "Got to a register and had no assigned sat literal value.")
            (mv mark ctrex-eval))
           (ctrex-eval (set-bit id sat-val ctrex-eval))
           (mark (set-bit id 1 mark)))
        (mv mark ctrex-eval))
      :co (progn$ (raise "Unexpectedly encountered a PO node")
                  (mv mark ctrex-eval))
      :const (mv mark ctrex-eval) ;; ctrex-eval should already have 0 here!
      :gate
      (b* ((fanin0 (snode->fanin slot0))
           (fanin1 (snode->fanin slot1))
           ((mv mark ctrex-eval)
            (fraig-record-sat-ctrex-rec (lit-id fanin0)
                                        mark aignet2 sat-lits ipasir ctrex-eval))
           ((mv mark ctrex-eval)
            (fraig-record-sat-ctrex-rec (lit-id fanin1)
                                        mark aignet2 sat-lits ipasir ctrex-eval))
           (fanin0-val (aignet-eval-lit fanin0 ctrex-eval))
           (fanin1-val (aignet-eval-lit fanin1 ctrex-eval))
           (computed-val (if (eql 1 (snode->regp slot1))
                             (b-xor fanin0-val fanin1-val)
                           (b-and fanin0-val fanin1-val)))
           (ctrex-eval (set-bit id computed-val ctrex-eval))
           (mark (set-bit id 1 mark)))
        (mbe :logic (mv mark ctrex-eval)
             :exec ;; extra debug checking
             (b* (((unless (or (not sat-val) (eql computed-val sat-val)))
                   (raise "Inconsistent values in satisfying assignment")
                   (mv mark ctrex-eval)))
               (mv mark ctrex-eval))))))
  ///
  (local (in-theory (disable (:d fraig-record-sat-ctrex-rec))))

  (local (defthm max-when-first-greater
           (implies (> a b)
                    (equal (max a b) a))))

  (local (defthm max-when-second-gte
           (implies (<= a b)
                    (equal (max a b) b))))
  
  (local (in-theory (disable max (tau-system))))

  (defret mark-length-of-fraig-record-sat-ctrex-rec
    (implies (and (<= (num-fanins aignet2) (len mark))
                  (<= (nfix id) (fanin-count aignet2)))
             (equal (len new-mark) (len mark)))
    :hints (("goal" :induct t
             :expand ((fraig-record-sat-ctrex-rec
                       id mark aignet2 sat-lits ipasir ctrex-eval)))))

  (defret eval-length-of-fraig-record-sat-ctrex-rec
    (implies (and (<= (+ 1 (fanin-count aignet2)) (len ctrex-eval))
                  (<= (nfix id) (fanin-count aignet2)))
             (equal (len new-ctrex-eval)
                    (len ctrex-eval)))
    :hints (("goal" :induct t
             :expand ((fraig-record-sat-ctrex-rec
                       id mark aignet2 sat-lits ipasir ctrex-eval)))))

  (verify-guards fraig-record-sat-ctrex-rec
    :hints(("Goal" :in-theory (enable aignet-idp))))

  ;; (local (defun-sk ctrex-eval-invariant (ctrex-eval mark aignet2 sat-lits ipasir)
  ;;          (forall (n invals regvals env)
  ;;                  (implies (equal 1 (nth n mark))
  ;;                           (b* ((env (ipasir::cube-to-env
  ;;                                      (ipasir::ipasir$a->solution ipasir) env)))
  ;;                             (bit-equiv (nth n ctrex-eval)
  ;;                                        (id-eval n
  ;;                                                 (cnf->aignet-invals invals env sat-lits aignet2)
  ;;                                                 (cnf->aignet-regvals regvals env sat-lits aignet2)
  ;;                                                 aignet2)))))
  ;;          :rewrite :direct))

  ;; ;; (local (defthm mv-nth-of-cons
  ;; ;;          (implies (syntaxp (quotep n))
  ;; ;;                   (equal (mv-nth n (cons a b))
  ;; ;;                          (if (zp n) a (mv-nth (1- n) b))))
  ;; ;;          :hints(("Goal" :in-theory (enable mv-nth)))))
  ;; ;; (local (in-theory (disable acl2::mv-nth-cons-meta)))

  ;; (local (in-theory (disable ctrex-eval-invariant
  ;;                            ;; SATLINK::EQUAL-OF-LIT-NEGATE-COND-COMPONENT-REWRITES
  ;;                            ;; SATLINK::EQUAL-OF-LIT-NEGATE-COMPONENT-REWRITES
  ;;                            ;; FRAIG-RECORD-SAT-CTREX-REC-OF-NFIX-ID-NORMALIZE-CONST
  ;;                            ;; SATLINK::LIT->VAR$INLINE-OF-LIT-FIX-LIT-NORMALIZE-CONST
  ;;                            ;; FRAIG-STATS-IMPLIES-NATP-OF-NTH
  ;;                            ;; aignet-lit-fix-when-aignet-litp
  ;;                            )))

  ;; (local (defthm ctrex-eval-invariant-of-update
  ;;          (implies (and (ctrex-eval-invariant ctrex-eval mark aignet2 sat-lits ipasir)
  ;;                        (b* ((env (ipasir::cube-to-env
  ;;                                      (ipasir::ipasir$a->solution ipasir) env)))
  ;;                          (equal val (id-eval n
  ;;                                              (cnf->aignet-invals invals env sat-lits aignet2)
  ;;                                              (cnf->aignet-regvals regvals env sat-lits aignet2)
  ;;                                              aignet2))))
  ;;                   (ctrex-eval-invariant
  ;;                    (update-nth n val ctrex-eval)
  ;;                    (update-nth n 1 mark)
  ;;                    aignet2 sat-lits ipasir))
  ;;          :hints ((and stable-under-simplificationp
  ;;                       `(:expand (,(car (last clause))))))))

  ;; (local (defret fraig-record-sat-ctrex-rec-preserves-ctrex-eval-invariant
  ;;          (implies (ctrex-eval-invariant ctrex-eval mark aignet2 sat-lits ipasir)
  ;;                   (ctrex-eval-invariant
  ;;                    new-ctrex-eval new-mark aignet2 sat-lits ipasir))
  ;;          :hints (("goal" :induct
  ;;                   (fraig-record-sat-ctrex-rec
  ;;                      id mark aignet2 sat-lits ipasir ctrex-eval)
  ;;                   :expand ((fraig-record-sat-ctrex-rec
  ;;                      id mark aignet2 sat-lits ipasir ctrex-eval)))
  ;;                  (and stable-under-simplificationp
  ;;                       `(:expand (,(car (last clause))
  ;;                                  (:free (invals regvals)
  ;;                                   (id-eval id invals regvals aignet2)))
  ;;                         :in-theory (enable ipasir::ipasir-val$a)
  ;;                         :do-not '(eliminate-destructors))))))
  )

(defstobj-clone ctrex-relevant bitarr :prefix "CTREX-RELEVANT-")


(local (in-theory (disable w)))

(local (defthm w-of-read-acl2-oracle
         (equal (w (mv-nth 2 (read-acl2-oracle state)))
                (w state))
         :hints(("Goal" :in-theory (enable read-acl2-oracle w update-acl2-oracle)))))

(local (defthm w-of-random$
         (equal (w (mv-nth 1 (random$ n state)))
                (w state))
         :hints(("Goal" :in-theory (enable random$)))))

(define fraig-minimize-sat-ctrex-rec ((id natp)
                                      ctrex-relevant
                                      aignet2
                                      ctrex-eval
                                      state)
  :measure (nfix id)
  :guard (and (id-existsp id aignet2)
              (<= (num-fanins aignet2) (bits-length ctrex-eval))
              (<= (num-fanins aignet2) (bits-length ctrex-relevant))
              ;; (non-exec (eq (ipasir::ipasir$a->status ipasir) :sat))
              ;; (sat-lits-wfp sat-lits aignet2)
              ;; Strong guards. Note: this is useful for debugging this function.
              ;; Uncomment the things marked Strong guards to enable.
              ;; (non-exec
              ;;  (and (ec-call (cnf-for-aignet aignet2 (ipasir::ipasir$a->formula ipasir) sat-lits))
              ;;       (b* ((env (ec-call (ipasir::cube-to-env
              ;;                                      (ipasir::ipasir$a->solution ipasir)
              ;;                                      nil))))
              ;;         (and (equal (eval-formula (ipasir::ipasir$a->formula ipasir)
              ;;                                   env)
              ;;                     1)
              ;;              (or (not val)
              ;;                  (equal val (lit-eval lit
              ;;                                       (ec-call (cnf->aignet-invals
              ;;                                                 nil env sat-lits aignet2))
              ;;                                       (ec-call (cnf->aignet-regvals
              ;;                                                 nil env sat-lits aignet2))
              ;;                                       aignet2)))))))
              )
  :verify-guards nil
  :returns (mv new-ctrex-relevant new-state)
  (b* (((when (eql 1 (get-bit id ctrex-relevant))) (mv ctrex-relevant state))
       (ctrex-relevant (set-bit id 1 ctrex-relevant))
       (slot0 (id->slot id 0 aignet2))
       (slot1 (id->slot id 1 aignet2))
       (type (snode->type slot0))
       ((unless (eql type (gate-type)))
        (mv ctrex-relevant state))
       
       (fanin0 (snode->fanin slot0))
       (fanin1 (snode->fanin slot1))
       ((when (or (eql 1 (snode->regp slot1))
                  (eql 1 (get-bit id ctrex-eval))))
        ;; Both branches are relevant because it's an XOR or because we need the AND to be 1.
        (b* (((mv ctrex-relevant state)
              (fraig-minimize-sat-ctrex-rec
               (lit-id fanin0) ctrex-relevant aignet2 ctrex-eval state)))
          (fraig-minimize-sat-ctrex-rec
           (lit-id fanin1) ctrex-relevant aignet2 ctrex-eval state)))
       ;; If one of the inputs is 1, then only the other is relevant
       ((when (eql 1 (aignet-eval-lit fanin0 ctrex-eval)))
        (fraig-minimize-sat-ctrex-rec
         (lit-id fanin1) ctrex-relevant aignet2 ctrex-eval state))
       ((when (eql 1 (aignet-eval-lit fanin1 ctrex-eval)))
        (fraig-minimize-sat-ctrex-rec
         (lit-id fanin0) ctrex-relevant aignet2 ctrex-eval state))
       ;; Both inputs are 0.  If either is already relevant, we're done.
       ((when (or (eql 1 (get-bit (lit-id fanin0) ctrex-relevant))
                  (eql 1 (get-bit (lit-id fanin1) ctrex-relevant))))
        (mv ctrex-relevant state))
       ;; Both inputs are 0 and neither is already relevant -- flip a coin to see which one to follow.
       ((mv coin state) (random$ 2 state))
       ((when (eql coin 0))
        (fraig-minimize-sat-ctrex-rec
         (lit-id fanin0) ctrex-relevant aignet2 ctrex-eval state)))
    (fraig-minimize-sat-ctrex-rec
     (lit-id fanin1) ctrex-relevant aignet2 ctrex-eval state))
  ///
  (local (in-theory (disable (:d fraig-minimize-sat-ctrex-rec))))

  (local (defthm max-when-first-greater
           (implies (> a b)
                    (equal (max a b) a))))

  (local (defthm max-when-second-gte
           (implies (<= a b)
                    (equal (max a b) b))))
  
  (local (in-theory (disable max (tau-system))))

  (defret ctrex-relevant-length-of-fraig-minimize-sat-ctrex-rec
    (implies (and (<= (num-fanins aignet2) (len ctrex-relevant))
                  (<= (nfix id) (fanin-count aignet2)))
             (equal (len new-ctrex-relevant) (len ctrex-relevant)))
    :hints (("goal" :induct t
             :expand ((fraig-minimize-sat-ctrex-rec
                       id ctrex-relevant aignet2 ctrex-eval state)))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))
    :hints (("goal" :induct t
             :expand ((fraig-minimize-sat-ctrex-rec
                       id ctrex-relevant aignet2 ctrex-eval state)))))

  (verify-guards fraig-minimize-sat-ctrex-rec
    :hints(("Goal" :in-theory (enable aignet-idp)))))

(defstobj-clone packed-relevants s32v :prefix "PACKED-RELEVANTS")
(defstobj-clone packed-vals s32v :prefix "PACKED-VALS")

(define fraig-ctrex-has-relevant-disagreement ((n natp)
                                        (ctrex-num natp)
                                        (ctrex-eval "input or reg values")
                                        (ctrex-relevant "input or reg relevant bits")
                                        (packed-vals)
                                        (packed-relevants))
  :returns (disagrees)
  :guard (and (< ctrex-num (* 32 (s32v-ncols packed-vals)))
              (< ctrex-num (* 32 (s32v-ncols packed-relevants)))
              (<= n (bits-length ctrex-eval))
              (<= n (bits-length ctrex-relevant))
              (<= n (s32v-nrows packed-vals))
              (<= n (s32v-nrows packed-relevants)))
  (b* (((when (zp n)) nil)
       (n (1- n))
       (ctrex-rel (get-bit n ctrex-relevant))
       ((when (eql 0 ctrex-rel))
        (fraig-ctrex-has-relevant-disagreement n ctrex-num ctrex-eval ctrex-relevant packed-vals packed-relevants))
       (packed-rel (s32v-get-bit n ctrex-num packed-relevants))
       ((when (eql 0 packed-rel))
        (fraig-ctrex-has-relevant-disagreement n ctrex-num ctrex-eval ctrex-relevant packed-vals packed-relevants))
       ;; both are relevant! do they agree?
       (ctrex-val (get-bit n ctrex-eval))
       (packed-val (s32v-get-bit n ctrex-num packed-vals)))
    (or (not (eql ctrex-val packed-val))
        (fraig-ctrex-has-relevant-disagreement n ctrex-num ctrex-eval ctrex-relevant packed-vals packed-relevants))))

(define fraig-ctrex-find-agreeable ((ctrex-num natp)
                                    (ctrex-eval)
                                    (ctrex-relevant)
                                    (packed-vals)
                                    (packed-relevants))
  ;; finds an existing counterexample that has no relevant disagreements with this one
  ;; The arrays here should correspond to concatenated inputs and registers
  :returns (good-ctrex-num (or (natp good-ctrex-num)
                               (not good-ctrex-num)) :rule-classes :type-prescription)
  :guard (and (<= ctrex-num (* 32 (s32v-ncols packed-vals)))
              (<= ctrex-num (* 32 (s32v-ncols packed-relevants)))
              (<= (s32v-nrows packed-relevants) (bits-length ctrex-eval))
              (<= (s32v-nrows packed-relevants) (bits-length ctrex-relevant))
              (<= (s32v-nrows packed-relevants) (s32v-nrows packed-vals)))
  (b* (((when (zp ctrex-num)) nil)
       (ctrex-num (1- ctrex-num))
       ((unless (fraig-ctrex-has-relevant-disagreement
                 (s32v-nrows packed-relevants) ctrex-num ctrex-eval ctrex-relevant packed-vals packed-relevants))
        ctrex-num))
    (fraig-ctrex-find-agreeable
     ctrex-num ctrex-eval ctrex-relevant packed-vals packed-relevants))
  ///
  (defret fraig-ctrex-find-agreeable-bound
    (implies good-ctrex-num
             (< good-ctrex-num (nfix ctrex-num)))
    :rule-classes :linear))

(define aignet-vals->regvals-after-invals ((n natp)
                                           (vals)    ;; full aignet evaluation vector
                                           (regvals) ;; write reg vals to here
                                           aignet)
  :returns (new-regvals)
  :guard (and (<= (num-fanins aignet) (bits-length vals))
              (<= (+ (num-ins aignet) (num-regs aignet)) (bits-length regvals))
              (<= n (num-regs aignet)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql n (num-regs aignet))))
        regvals)
       (id (regnum->id n aignet))
       (val (get-bit id vals))
       (regvals (set-bit (+ (lnfix n) (num-ins aignet)) val regvals)))
    (aignet-vals->regvals-after-invals
     (1+ (lnfix n)) vals regvals aignet))
  ///
  (defret length-of-aignet-vals->regvals-after-invals
    (implies (<= (+ (num-ins aignet) (num-regs aignet)) (len regvals))
             (equal (len new-regvals) (len regvals)))))
       

(define aignet-vals->in/regvals ((vals) ;; input -- full aignet eval vector
                                 (ctrex-eval) ;; output -- input and register values
                                 (aignet))
  :guard (and (<= (num-fanins aignet) (bits-length vals))
              (<= (+ (num-ins aignet) (num-regs aignet)) (bits-length ctrex-eval)))
  :returns (new-ctrex-eval)
  :verify-guards nil
  (b* ((ctrex-eval (aignet-vals->invals ctrex-eval vals aignet)))
    (aignet-vals->regvals-after-invals 0 vals ctrex-eval aignet))
  ///

  (verify-guards aignet-vals->in/regvals)

  (defret len-of-aignet-vals->in/regvals
    (implies (<= (+ (num-ins aignet) (num-regs aignet)) (bits-length ctrex-eval))
             (equal (len new-ctrex-eval) (len ctrex-eval)))))


(defstobj-clone in/reg-vals bitarr :prefix "IN/REG-VALS-")
(defstobj-clone in/reg-relevants bitarr :prefix "IN/REG-RELEVANTS-")

(define bitarr-to-s32v-col ((row natp)
                            (bitcol natp)
                            (bitarr)
                            (s32v))
  :guard (and (<= row (s32v-nrows s32v))
              (<= (s32v-nrows s32v) (bits-length bitarr))
              (< bitcol (* 32 (s32v-ncols s32v))))
  :measure (nfix (- (s32v-nrows s32v) (nfix row)))
  :returns (new-s32v)
  (b* (((when (mbe :logic (zp (- (s32v-nrows s32v) (nfix row)))
                   :exec (eql row (s32v-nrows s32v))))
        s32v)
       (bit (get-bit row bitarr))
       (s32v (s32v-install-bit row bitcol bit s32v)))
    (bitarr-to-s32v-col (1+ (lnfix row)) bitcol bitarr s32v))
  ///
  (defret s32v-nrows-of-bitarr-to-s32v-col
    (equal (len (stobjs::2darr->rows new-s32v))
           (len (stobjs::2darr->rows s32v))))

  (defret s32v-ncols-of-bitarr-to-s32v-col
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v))))

(define bitarr-copy-cares-to-s32v-col ((row natp)
                                       (bitcol natp)
                                       (ctrex-eval)
                                       (ctrex-relevant)
                                       (s32v))
  :guard (and (<= row (s32v-nrows s32v))
              (<= (s32v-nrows s32v) (bits-length ctrex-eval))
              (<= (s32v-nrows s32v) (bits-length ctrex-relevant))
              (< bitcol (* 32 (s32v-ncols s32v))))
  :measure (nfix (- (s32v-nrows s32v) (nfix row)))
  :returns (new-s32v)
  (b* (((when (mbe :logic (zp (- (s32v-nrows s32v) (nfix row)))
                   :exec (eql row (s32v-nrows s32v))))
        s32v)
       (rel (get-bit row ctrex-relevant))
       ((when (eql 0 rel))
        (bitarr-copy-cares-to-s32v-col (1+ (lnfix row)) bitcol ctrex-eval ctrex-relevant s32v))
       (val (get-bit row ctrex-eval))
       (s32v (s32v-install-bit row bitcol val s32v)))
    (bitarr-copy-cares-to-s32v-col (1+ (lnfix row)) bitcol ctrex-eval ctrex-relevant s32v))
  ///
  (defret s32v-nrows-of-bitarr-copy-cares-to-s32v-col
    (equal (len (stobjs::2darr->rows new-s32v))
           (len (stobjs::2darr->rows s32v))))

  (defret s32v-ncols-of-bitarr-copy-cares-to-s32v-col
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v))))

(define bitarr-or-cares-with-s32v-col ((row natp)
                                       (bitcol natp)
                                       (ctrex-relevant)
                                       (s32v))
  :guard (and (<= row (s32v-nrows s32v))
              (<= (s32v-nrows s32v) (bits-length ctrex-relevant))
              (< bitcol (* 32 (s32v-ncols s32v))))
  :measure (nfix (- (s32v-nrows s32v) (nfix row)))
  :returns (new-s32v)
  (b* (((when (mbe :logic (zp (- (s32v-nrows s32v) (nfix row)))
                   :exec (eql row (s32v-nrows s32v))))
        s32v)
       (rel (get-bit row ctrex-relevant))
       ((when (eql 0 rel))
        (bitarr-or-cares-with-s32v-col (1+ (lnfix row)) bitcol ctrex-relevant s32v))
       (s32v (s32v-install-bit row bitcol 1 s32v)))
    (bitarr-or-cares-with-s32v-col (1+ (lnfix row)) bitcol ctrex-relevant s32v))
  ///
  (defret s32v-nrows-of-bitarr-or-cares-with-s32v-col
    (equal (len (stobjs::2darr->rows new-s32v))
           (len (stobjs::2darr->rows s32v))))

  (defret s32v-ncols-of-bitarr-or-cares-with-s32v-col
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v))))
                            


(define fraig-store-ctrex-aux ((lit1 litp)
                           (lit2 litp)
                           (aignet2)
                           (sat-lits)
                           (ipasir)
                           (ctrex-count natp)
                           (packed-vals)
                           (packed-relevants)
                           state)
  :guard (and (fanin-litp lit1 aignet2)
              (fanin-litp lit2 aignet2)
              (non-exec (eq (ipasir::ipasir$a->status ipasir) :sat))
              (sat-lits-wfp sat-lits aignet2)
              (equal (+ (num-ins aignet2) (num-regs aignet2)) (s32v-nrows packed-relevants))
              (equal (s32v-nrows packed-relevants) (s32v-nrows packed-vals))
              (< ctrex-count (* 32 (s32v-ncols packed-relevants)))
              (equal (s32v-ncols packed-relevants) (s32v-ncols packed-vals)))
  :returns (mv (new-ctrex-count natp :rule-classes :type-prescription)
               new-packed-vals
               new-packed-relevants
               new-state)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp))))
  (b* (((acl2::local-stobjs mark ctrex-eval ctrex-relevant in/reg-vals in/reg-relevants)
        (mv mark ctrex-eval ctrex-relevant in/reg-vals in/reg-relevants
            new-ctrex-count packed-vals packed-relevants state))
       (ctrex-eval     (resize-bits (num-fanins aignet2) ctrex-eval))
       (ctrex-relevant (resize-bits (num-fanins aignet2) ctrex-relevant))
       (mark           (resize-bits (num-fanins aignet2) mark))
       ((mv mark ctrex-eval) (fraig-record-sat-ctrex-rec (lit-id lit1) mark aignet2 sat-lits ipasir ctrex-eval))
       ((mv mark ctrex-eval) (fraig-record-sat-ctrex-rec (lit-id lit2) mark aignet2 sat-lits ipasir ctrex-eval))
       ((mv ctrex-relevant state)
        (fraig-minimize-sat-ctrex-rec (lit-id lit1) ctrex-relevant aignet2 ctrex-eval state))
       ((mv ctrex-relevant state)
        (fraig-minimize-sat-ctrex-rec (lit-id lit2) ctrex-relevant aignet2 ctrex-eval state))
       (in/reg-vals      (resize-bits (+ (num-ins aignet2) (num-regs aignet2)) in/reg-vals))
       (in/reg-relevants (resize-bits (+ (num-ins aignet2) (num-regs aignet2)) in/reg-relevants))
       (in/reg-vals      (aignet-vals->in/regvals ctrex-eval in/reg-vals aignet2))
       (in/reg-relevants (aignet-vals->in/regvals ctrex-relevant in/reg-relevants aignet2))
       (agreeable-bitcol    (fraig-ctrex-find-agreeable ctrex-count in/reg-vals in/reg-relevants
                                                        packed-vals packed-relevants))
       ((mv bitcol ctrex-count)
        (if agreeable-bitcol
            (mv agreeable-bitcol (lnfix ctrex-count))
          (mv ctrex-count (+ 1 (lnfix ctrex-count)))))
       (packed-vals (bitarr-copy-cares-to-s32v-col 0 bitcol in/reg-vals in/reg-relevants packed-vals))
       (packed-relevants (bitarr-or-cares-with-s32v-col 0 bitcol in/reg-relevants packed-relevants)))
    (mv mark ctrex-eval ctrex-relevant in/reg-vals in/reg-relevants
        ctrex-count packed-vals packed-relevants state))
  ///
  (defret packed-vals-nrows-of-fraig-store-ctrex-aux
    (implies (equal (s32v-nrows packed-vals) (+ (num-ins aignet2) (num-regs aignet2)))
             (equal (len (stobjs::2darr->rows new-packed-vals))
                    (+ (num-ins aignet2) (num-regs aignet2)))))

  (defret packed-relevants-nrows-of-fraig-store-ctrex-aux
    (implies (equal (s32v-nrows packed-relevants) (+ (num-ins aignet2) (num-regs aignet2)))
             (equal (len (stobjs::2darr->rows new-packed-relevants))
                    (+ (num-ins aignet2) (num-regs aignet2)))))

  (defret packed-vals-ncols-of-fraig-store-ctrex-aux
    (equal (stobjs::2darr->ncols new-packed-vals)
           (stobjs::2darr->ncols packed-vals)))

  (defret packed-relevants-ncols-of-fraig-store-ctrex-aux
    (equal (stobjs::2darr->ncols new-packed-relevants)
           (stobjs::2darr->ncols packed-relevants)))

  (defret ctrex-count-bound-of-fraig-store-ctrex-aux
    (implies (< (nfix ctrex-count) (* 32 (s32v-ncols packed-relevants)))
             (<= new-ctrex-count (* 32 (s32v-ncols packed-relevants))))
    :rule-classes :linear)

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(defstobj fraig-ctrexes
  ;; number of counterexamples that haven't been resimulated yet. These can
  ;; overlap when multiple counterexes have no disagreeing relevant bits, so
  ;; adding a new counterex doesn't necessarily increase this number
  (fraig-ctrex-nbits :type (integer 0 *) :initially 0)
  (fraig-ctrex-count :type (integer 0 *) :initially 0)
  ;; s32v structure containing simulation memory
  (fraig-ctrex-data :type s32v)
  (fraig-ctrex-in/reg-vals :type s32v)
  (fraig-ctrex-in/reg-relevants :type s32v)
  (fraig-ctrex-resim-classes :type bitarr))

(define fraig-ctrex-data-rows (fraig-ctrexes)
  :returns (size natp :rule-classes :type-prescription)
  (b* (((acl2::stobj-get size)
        ((s32v (fraig-ctrex-data fraig-ctrexes)))
        (s32v-nrows s32v)))
    size))

(define fraig-ctrex-ncols (fraig-ctrexes)
  :returns (ncols natp :rule-classes :type-prescription)
  (b* (((acl2::stobj-get size)
        ((s32v (fraig-ctrex-data fraig-ctrexes)))
        (s32v-ncols s32v)))
    size))

(define fraig-ctrex-in/reg-rows (fraig-ctrexes)
  (b* (((acl2::stobj-get size)
        ((s32v (fraig-ctrex-in/reg-relevants fraig-ctrexes)))
        (s32v-nrows s32v)))
    size))


(define fraig-ctrexes-ok (fraig-ctrexes)
  :returns (ok)
  (b* ((nctrexes (lnfix (fraig-ctrex-nbits fraig-ctrexes)))
       ((acl2::stobj-get ncols data-and-resims-ok)
        ((s32v (fraig-ctrex-data fraig-ctrexes))
         (bitarr (fraig-ctrex-resim-classes fraig-ctrexes)))
        (mv (s32v-ncols s32v)
            (equal (s32v-nrows s32v) (bits-length bitarr))))
       ((acl2::stobj-get vals/relevants-ok)
        ((packed-vals (fraig-ctrex-in/reg-vals fraig-ctrexes))
         (packed-relevants (fraig-ctrex-in/reg-relevants fraig-ctrexes)))
        (and (equal (s32v-ncols packed-vals) ncols)
             (equal (s32v-ncols packed-relevants) ncols)
             (equal (s32v-nrows packed-vals) (s32v-nrows packed-relevants)))))
    (and (posp ncols)
         (<= nctrexes (* 32 ncols))
         data-and-resims-ok
         vals/relevants-ok))
  ///
  (defretd fraig-ctrexes-ok-implies-data-rows
    (implies ok
             (equal (len (stobjs::2darr->rows (nth *fraig-ctrex-data* fraig-ctrexes)))
                    (fraig-ctrex-data-rows fraig-ctrexes)))
    :hints(("Goal" :in-theory (enable fraig-ctrex-data-rows))))

  (defretd fraig-ctrexes-ok-implies-data-columns
    (implies ok
             (equal (stobjs::2darr->ncols (nth *fraig-ctrex-data* fraig-ctrexes))
                    (fraig-ctrex-ncols fraig-ctrexes)))
    :hints(("Goal" :in-theory (enable fraig-ctrex-ncols))))

  (defretd fraig-ctrexes-ok-implies-classes-len
    (implies ok
             (equal (len (nth *fraig-ctrex-resim-classes* fraig-ctrexes))
                    (fraig-ctrex-data-rows fraig-ctrexes)))
    :hints(("Goal" :in-theory (enable fraig-ctrex-data-rows))))

  (defretd fraig-ctrexes-ok-implies-vals-rows
    (implies ok
             (equal (len (stobjs::2darr->rows (nth *fraig-ctrex-in/reg-vals* fraig-ctrexes)))
                    (fraig-ctrex-in/reg-rows fraig-ctrexes)))
    :hints(("Goal" :in-theory (enable fraig-ctrex-in/reg-rows))))

  (defretd fraig-ctrexes-ok-implies-relevants-rows
    (implies ok
             (equal (len (stobjs::2darr->rows (nth *fraig-ctrex-in/reg-relevants* fraig-ctrexes)))
                    (fraig-ctrex-in/reg-rows fraig-ctrexes)))
    :hints(("Goal" :in-theory (enable fraig-ctrex-in/reg-rows))))

  (defretd fraig-ctrexes-ok-implies-vals-columns
    (implies ok
             (equal (stobjs::2darr->ncols (nth *fraig-ctrex-in/reg-vals* fraig-ctrexes))
                    (fraig-ctrex-ncols fraig-ctrexes)))
    :hints(("Goal" :in-theory (enable fraig-ctrex-ncols))))

  (defretd fraig-ctrexes-ok-implies-relevants-columns
    (implies ok
             (equal (stobjs::2darr->ncols (nth *fraig-ctrex-in/reg-relevants* fraig-ctrexes))
                    (fraig-ctrex-ncols fraig-ctrexes)))
    :hints(("Goal" :in-theory (enable fraig-ctrex-ncols))))

  (defretd fraig-ctrexes-ok-implies-ncols-posp
    (implies ok
             (posp (fraig-ctrex-ncols fraig-ctrexes)))
    :hints(("Goal" :in-theory (enable fraig-ctrex-ncols)))
    :rule-classes :forward-chaining)

  (defretd fraig-ctrexes-ok-implies-nctrexes-bound
    (implies ok
             (<= (nfix (nth *fraig-ctrex-nbits* fraig-ctrexes))
                 (* 32 (fraig-ctrex-ncols fraig-ctrexes))))
    :hints(("Goal" :in-theory (enable fraig-ctrex-ncols)))
    :rule-classes :linear)

  (defretd fraig-ctrexes-ok-implies-nctrexes-bound-natp
    (implies (and ok (natp (nth *fraig-ctrex-nbits* fraig-ctrexes)))
             (<= (nth *fraig-ctrex-nbits* fraig-ctrexes)
                 (* 32 (fraig-ctrex-ncols fraig-ctrexes))))
    :hints(("Goal" :in-theory (enable fraig-ctrex-ncols)))
    :rule-classes :linear)

  (def-ruleset! fraig-ctrexes-ok-rules
    '(fraig-ctrexes-ok-implies-data-rows
      fraig-ctrexes-ok-implies-data-columns
      fraig-ctrexes-ok-implies-classes-len
      fraig-ctrexes-ok-implies-vals-rows
      fraig-ctrexes-ok-implies-relevants-rows
      fraig-ctrexes-ok-implies-vals-columns
      fraig-ctrexes-ok-implies-relevants-columns
      fraig-ctrexes-ok-implies-ncols-posp
      fraig-ctrexes-ok-implies-nctrexes-bound
      fraig-ctrexes-ok-implies-nctrexes-bound-natp)))

(local (in-theory (enable* fraig-ctrexes-ok-rules)))

(define s32v-zero-rows ((row natp) s32v)
  :guard (<= row (s32v-nrows s32v))
  :measure (nfix (- (s32v-nrows s32v) (nfix row)))
  :returns new-s32v
  (b* (((When (mbe :logic (zp (- (s32v-nrows s32v) (nfix row)))
                   :exec (eql row (s32v-nrows s32v))))
        s32v)
       (s32v (s32v-zero (lnfix row) s32v)))
    (s32v-zero-rows (+ 1 (lnfix row)) s32v))
  ///
  (defret s32v-nrows-of-s32v-zero-rows
    (equal (len (stobjs::2darr->rows new-s32v))
           (len (stobjs::2darr->rows s32v))))

  (defret s32v-ncols-of-s32v-zero-rows
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v))))

(local (defthm w-state-of-s32v-randomize-iter
         (equal (w (mv-nth 1 (s32v-randomize-iter n out-id s32v state)))
                (w state))
         :hints(("Goal" :in-theory (enable s32v-randomize-iter)))))

(define s32v-randomize-rows ((row natp) s32v state)
  :guard (<= row (s32v-nrows s32v))
  :measure (nfix (- (s32v-nrows s32v) (nfix row)))
  :returns (mv new-s32v new-state)
  (b* (((When (mbe :logic (zp (- (s32v-nrows s32v) (nfix row)))
                   :exec (eql row (s32v-nrows s32v))))
        (mv s32v state))
       ((mv s32v state) (s32v-randomize (lnfix row) s32v state)))
    (s32v-randomize-rows (+ 1 (lnfix row)) s32v state))
  ///
  (defret s32v-nrows-of-s32v-randomize-rows
    (equal (len (stobjs::2darr->rows new-s32v))
           (len (stobjs::2darr->rows s32v))))

  (defret s32v-ncols-of-s32v-randomize-rows
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(local (defthm w-state-of-s32v-randomize-regs
         (equal (w (mv-nth 1 (s32v-randomize-regs n s32v aignet state)))
                (w state))
         :hints(("Goal" :in-theory (enable s32v-randomize-regs)))))

(local (defthm w-state-of-s32v-randomize-inputs
         (equal (w (mv-nth 1 (s32v-randomize-inputs n s32v aignet state)))
                (w state))
         :hints(("Goal" :in-theory (enable s32v-randomize-inputs)))))


(define fraig-ctrexes-init ((ncols posp)
                            fraig-ctrexes
                            aignet)
  :returns new-fraig-ctrexes
  (b* ((ncols (acl2::lposfix ncols))
       (fraig-ctrexes (update-fraig-ctrex-nbits 0 fraig-ctrexes))
       (fraig-ctrexes (update-fraig-ctrex-count 0 fraig-ctrexes))
       (size (num-fanins aignet))
       ((acl2::stobj-get s32v bitarr)
        ((s32v (fraig-ctrex-data fraig-ctrexes))
         (bitarr (fraig-ctrex-resim-classes fraig-ctrexes)))
        (b* ((bitarr (resize-bits 0 bitarr))
             (bitarr (resize-bits size bitarr)) ;; clear to 0
             (s32v (s32v-resize-rows 0 s32v))
             (s32v (s32v-resize-cols ncols s32v))
             (s32v (s32v-resize-rows size s32v)))
          (mv s32v bitarr)))
       (in/reg-size (+ (num-ins aignet) (num-regs aignet)))
       ((acl2::stobj-get packed-vals packed-relevants)
        ((packed-vals (fraig-ctrex-in/reg-vals fraig-ctrexes))
         (packed-relevants (fraig-ctrex-in/reg-relevants fraig-ctrexes)))
        (b* ((packed-vals (s32v-resize-rows 0 packed-vals))
             (packed-vals (s32v-resize-cols ncols packed-vals))
             (packed-vals (s32v-resize-rows in/reg-size packed-vals))
             (packed-relevants (s32v-resize-rows 0 packed-relevants))
             (packed-relevants (s32v-resize-cols ncols packed-relevants))
             (packed-relevants (s32v-resize-rows in/reg-size packed-relevants)))
          (mv packed-vals packed-relevants))))
    fraig-ctrexes)
  ///
  (defret fraig-ctrexes-ok-of-fraig-ctrexes-init
    (fraig-ctrexes-ok new-fraig-ctrexes)
    :hints(("Goal" :in-theory (enable fraig-ctrexes-ok))))
  
  (defret fraig-ctrex-data-rows-of-fraig-ctrexes-init
    (equal (fraig-ctrex-data-rows new-fraig-ctrexes)
           (num-fanins aignet))
    :hints(("Goal" :in-theory (enable fraig-ctrex-data-rows))))

  (defret fraig-ctrex-in/reg-rows-of-fraig-ctrexes-init
    (equal (fraig-ctrex-in/reg-rows new-fraig-ctrexes)
           (+ (num-ins aignet) (num-regs aignet)))
    :hints(("Goal" :in-theory (enable fraig-ctrex-in/reg-rows))))

  (defret fraig-ctrex-ncols-of-fraig-ctrexes-init
    (equal (fraig-ctrex-ncols new-fraig-ctrexes)
           (acl2::pos-fix ncols))
    :hints(("Goal" :in-theory (enable fraig-ctrex-ncols)))))


(define fraig-ctrexes-reinit (fraig-ctrexes)
  :guard (fraig-ctrexes-ok fraig-ctrexes)
  :returns new-fraig-ctrexes
  (b* ((fraig-ctrexes (update-fraig-ctrex-nbits 0 fraig-ctrexes))
       (fraig-ctrexes (update-fraig-ctrex-count 0 fraig-ctrexes))
       (data-rows (fraig-ctrex-data-rows fraig-ctrexes))
       ((acl2::stobj-get bitarr)
        ((bitarr (fraig-ctrex-resim-classes fraig-ctrexes)))
        (b* ((bitarr (resize-bits 0 bitarr))
             (bitarr (resize-bits data-rows bitarr)))
          bitarr))
       ((acl2::stobj-get packed-relevants)
        ((packed-relevants (fraig-ctrex-in/reg-relevants fraig-ctrexes)))
        (s32v-zero-rows 0 packed-relevants)))
    fraig-ctrexes)
  ///
  (defret fraig-ctrexes-ok-of-fraig-ctrexes-reinit
    (implies (fraig-ctrexes-ok fraig-ctrexes)
             (fraig-ctrexes-ok new-fraig-ctrexes))
    :hints(("Goal" :in-theory (e/d* (fraig-ctrexes-ok
                                     fraig-ctrex-data-rows)
                                    (fraig-ctrexes-ok-rules)))))
  
  (defret fraig-ctrex-data-rows-of-fraig-ctrexes-reinit
    (equal (fraig-ctrex-data-rows new-fraig-ctrexes)
           (fraig-ctrex-data-rows fraig-ctrexes))
    :hints(("Goal" :in-theory (enable fraig-ctrex-data-rows))))

  (defret fraig-ctrex-in/reg-rows-of-fraig-ctrexes-reinit
    (equal (fraig-ctrex-in/reg-rows new-fraig-ctrexes)
           (fraig-ctrex-in/reg-rows fraig-ctrexes))
    :hints(("Goal" :in-theory (enable fraig-ctrex-in/reg-rows))))

  (defret fraig-ctrex-ncols-of-fraig-ctrexes-reinit
    (equal (fraig-ctrex-ncols new-fraig-ctrexes)
           (fraig-ctrex-ncols fraig-ctrexes))
    :hints(("Goal" :in-theory (enable fraig-ctrex-ncols))))

  (defret fraig-ctrex-nbits-of-fraig-ctrexes-reinit
    (equal (nth *fraig-ctrex-nbits* new-fraig-ctrexes) 0)))




;; (define fraig-ctrexes-reinit (fraig-ctrexes
;;                               aignet
;;                               state)
;;   :returns (mv new-fraig-ctrexes new-state)
;;   :guard (and (fraig-ctrexes-ok fraig-ctrexes)
;;               (<= (num-fanins aignet) (fraig-ctrexes-size fraig-ctrexes)))
;;   (b* ((fraig-ctrexes (update-fraig-ctrex-bits 0 fraig-ctrexes))
;;        ((acl2::stobj-get s32v bitarr state)
;;         ((s32v (fraig-ctrex-data fraig-ctrexes))
;;          (bitarr (fraig-ctrex-resim-classes fraig-ctrexes)))
;;         (b* ((size (bits-length bitarr))
;;              (bitarr (resize-bits 0 bitarr))
;;              (bitarr (resize-bits size bitarr)) ;; clear to 0
;;              ((mv s32v state) (s32v-randomize-regs 0 s32v aignet state))
;;              ((mv s32v state) (s32v-randomize-inputs 0 s32v aignet state)))
;;           (mv s32v bitarr state))))
;;     (mv fraig-ctrexes state))
;;   ///
;;   (defret nqueued-ctrexes-of-fraig-ctrexes-reinit
;;     (equal (nth *fraig-nqueued-ctrexes* new-fraig-ctrexes) 0))

;;   (defret fraig-ctrexes-ok-of-fraig-ctrexes-reinit
;;     (implies (and (<= (num-fanins aignet)
;;                       (fraig-ctrexes-size fraig-ctrexes))
;;                   (fraig-ctrexes-ok fraig-ctrexes))
;;              (fraig-ctrexes-ok new-fraig-ctrexes))
;;     :hints(("Goal" :in-theory (enable fraig-ctrexes-ok))))

;;   (defret fraig-ctrexes-size-of-fraig-ctrexes-reinit
;;     (implies (and (<= (num-fanins aignet)
;;                       (fraig-ctrexes-size fraig-ctrexes))
;;                   (fraig-ctrexes-ok fraig-ctrexes))
;;              (and (equal (len (stobjs::2darr->rows (nth *fraig-ctrex-data* new-fraig-ctrexes)))
;;                          (fraig-ctrexes-size fraig-ctrexes))
;;                   (equal (len (nth *fraig-ctrex-resim-classes* new-fraig-ctrexes))
;;                          (fraig-ctrexes-size fraig-ctrexes)))))

;;   (defret fraig-ctrexes-ncols-of-fraig-ctrexes-reinit
;;     (equal (stobjs::2darr->ncols (nth *fraig-ctrex-data* new-fraig-ctrexes))
;;            (stobjs::2darr->ncols (nth *fraig-ctrex-data* fraig-ctrexes)))))


(define fraig-store-ctrex ((lit1 litp)
                           (lit2 litp)
                           (class-head natp)
                           (aignet2)
                           (sat-lits)
                           (ipasir)
                           (fraig-ctrexes)
                           state)
  :guard (and (fanin-litp lit1 aignet2)
              (fanin-litp lit2 aignet2)
              (non-exec (eq (ipasir::ipasir$a->status ipasir) :sat))
              (sat-lits-wfp sat-lits aignet2)
              (equal (+ (num-ins aignet2) (num-regs aignet2)) (fraig-ctrex-in/reg-rows fraig-ctrexes))
              (fraig-ctrexes-ok fraig-ctrexes)
              (< (nfix (fraig-ctrex-nbits fraig-ctrexes))
                 (* 32 (fraig-ctrex-ncols fraig-ctrexes)))
              (< class-head (fraig-ctrex-data-rows fraig-ctrexes)))
  :returns (mv new-fraig-ctrexes new-state)
  (b* ((count (fraig-ctrex-nbits fraig-ctrexes))
       ((acl2::stobj-get new-count packed-vals packed-relevants bitarr state)
        ((packed-vals (fraig-ctrex-in/reg-vals fraig-ctrexes))
         (packed-relevants (fraig-ctrex-in/reg-relevants fraig-ctrexes))
         (bitarr (fraig-ctrex-resim-classes fraig-ctrexes)))
        (b* (((mv new-count packed-vals packed-relevants state)
              (fraig-store-ctrex-aux lit1 lit2 aignet2 sat-lits ipasir count packed-vals packed-relevants state))
             (bitarr (set-bit class-head 1 bitarr)))
          (mv new-count packed-vals packed-relevants bitarr state)))
       (fraig-ctrexes (update-fraig-ctrex-nbits new-count fraig-ctrexes))
       (fraig-ctrexes (update-fraig-ctrex-count (+ 1 (fraig-ctrex-count fraig-ctrexes)) fraig-ctrexes)))
    (mv fraig-ctrexes state))
  ///
  (defret fraig-ctrexes-ok-of-fraig-store-ctrex
    (implies (and (fraig-ctrexes-ok fraig-ctrexes)
                  (< (nfix (fraig-ctrex-nbits fraig-ctrexes))
                     (* 32 (fraig-ctrex-ncols fraig-ctrexes)))
                  (equal (fraig-ctrex-in/reg-rows fraig-ctrexes)
                         (+ (num-ins aignet2) (num-regs aignet2)))
                  (< (nfix class-head) (fraig-ctrex-data-rows fraig-ctrexes)))
             (fraig-ctrexes-ok new-fraig-ctrexes))
    :hints(("Goal" :in-theory (enable fraig-ctrexes-ok))))

  (defret fraig-ctrex-data-rows-of-fraig-store-ctrex
    (equal (fraig-ctrex-data-rows new-fraig-ctrexes)
           (fraig-ctrex-data-rows fraig-ctrexes))
    :hints(("Goal" :in-theory (enable fraig-ctrex-data-rows))))

  (defret fraig-ctrex-ncols-of-fraig-store-ctrex
    (equal (fraig-ctrex-ncols new-fraig-ctrexes)
           (fraig-ctrex-ncols fraig-ctrexes))
    :hints(("Goal" :in-theory (enable fraig-ctrex-ncols))))

  (defret fraig-ctrex-in/reg-rows-of-fraig-store-ctrex
    (implies (equal (fraig-ctrex-in/reg-rows fraig-ctrexes)
                    (+ (num-ins aignet2) (num-regs aignet2)))
             (equal (fraig-ctrex-in/reg-rows new-fraig-ctrexes)
                    (+ (num-ins aignet2) (num-regs aignet2))))
    :hints(("Goal" :in-theory (enable fraig-ctrex-in/reg-rows))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(define s32v-bitcol-count-set ((n natp)
                               (acc natp)
                               (bitcol natp)
                               (s32v))
  :guard (and (<= n (s32v-nrows s32v))
              (< bitcol (* 32 (s32v-ncols s32v))))
  :measure (nfix (- (s32v-nrows s32v) (nfix n)))
  (b* (((when (mbe :logic (zp (- (s32v-nrows s32v) (nfix n)))
                   :exec (eql n (s32v-nrows s32v))))
        (lnfix acc)))
    (s32v-bitcol-count-set
     (1+ (lnfix n))
     (+ (lnfix acc) (s32v-get-bit n bitcol s32v))
     bitcol s32v))
  ///
  (local (defun-sk s32v-bitcol-elim-invar (n bitcol s32v)
           (forall acc
                   (implies (syntaxp (not (equal acc ''0)))
                            (equal (s32v-bitcol-count-set n acc bitcol s32v)
                                   (+ (nfix acc) (s32v-bitcol-count-set n 0 bitcol s32v)))))
           :rewrite :direct))
  (local (in-theory (disable s32v-bitcol-elim-invar)))
  (local (defthm s32v-bitcol-elim-invar-is-true
           (s32v-bitcol-elim-invar n bitcol s32v)
           :hints (("goal" :induct (s32v-bitcol-count-set n acc bitcol s32v))
                   (and stable-under-simplificationp
                        `(:expand (,(car (last clause))
                                   (:free (acc) (s32v-bitcol-count-set n acc bitcol s32v))))))))

  (defthm s32v-bitcol-acc-elim
    (implies (syntaxp (not (equal acc ''0)))
                            (equal (s32v-bitcol-count-set n acc bitcol s32v)
                                   (+ (nfix acc) (s32v-bitcol-count-set n 0 bitcol s32v))))))

(define s32v-bitcol-nth-set ((row natp)
                             (nleft natp)
                             (bitcol natp)
                             (s32v))
  :guard (and (<= row (s32v-nrows s32v))
              (< bitcol (* 32 (s32v-ncols s32v)))
              (< nleft (s32v-bitcol-count-set row 0 bitcol s32v)))
  :guard-hints (("goal" :in-theory (enable s32v-bitcol-count-set)))
  :measure (nfix (- (s32v-nrows s32v) (nfix row)))
  :hints(("Goal" :in-theory (enable s32v-bitcol-count-set)
          :expand ((s32v-bitcol-count-set (+ 1 (nfix row)) 0 bitcol s32v))))
  :returns (nth-row natp :rule-classes :type-prescription)
  (b* ((bit (s32v-get-bit row bitcol s32v))
       ((when (and (eql (lnfix nleft) 0) (eql bit 1))) (lnfix row))
       ((unless (mbt (posp (s32v-bitcol-count-set (+ 1 (lnfix row)) 0 bitcol s32v))))
        (lnfix row)))
    (s32v-bitcol-nth-set
     (1+ (lnfix row)) (- (lnfix nleft) bit) bitcol s32v))
  ///
  (defret s32v-bitcol-nth-set-bound
    (implies (< (nfix row) (len (stobjs::2darr->rows s32v)))
             (< nth-row (len (stobjs::2darr->rows s32v))))
    :hints(("Goal" :in-theory (enable s32v-bitcol-count-set)))
    :rule-classes :linear))


(local (defthm natp-of-random$
         (natp (mv-nth 0 (random$ n state)))
         :hints(("Goal" :in-theory (enable random$)))
         :rule-classes :type-prescription))

(local (defthm bound-of-random$
         (implies (posp n)
                  (< (mv-nth 0 (random$ n state)) n))
         :hints(("Goal" :in-theory (enable random$)))
         :rule-classes :linear))

(define s32v-add-salt ((col natp)
                       (packed-vals)
                       (packed-relevants)
                       state)
  :measure (nfix (- (* 32 (s32v-ncols packed-relevants)) (nfix col)))
  :guard (and (<= (s32v-ncols packed-relevants) (s32v-ncols packed-vals))
              (<= (s32v-nrows packed-relevants) (s32v-nrows packed-vals))
              (<= col (* 32 (s32v-ncols packed-relevants)))
              (< 0 (s32v-nrows packed-relevants)))
  :returns (mv new-packed-vals new-state)
  (b* (((when (mbe :logic (zp (- (* 32 (s32v-ncols packed-relevants)) (nfix col)))
                   :exec (eql col (* 32 (s32v-ncols packed-relevants)))))
        (mv packed-vals state))
       (nrelevant (s32v-bitcol-count-set 0 0 col packed-relevants))
       ((when (eql 0 nrelevant))
        (s32v-add-salt (+ 1 (lnfix col)) packed-vals packed-relevants state))
       ((mv which-relevant state) (random$ nrelevant state))
       (idx (s32v-bitcol-nth-set 0 which-relevant col packed-relevants))
       (prev-val (s32v-get-bit idx col packed-vals))
       (packed-vals (s32v-install-bit idx col (b-not prev-val) packed-vals)))
    (s32v-add-salt (+ 1 (lnfix col)) packed-vals packed-relevants state))
  ///
  (defret nrows-of-s32v-add-salt
    (implies (and (<= (s32v-nrows packed-relevants) (s32v-nrows packed-vals))
                  (< 0 (s32v-nrows packed-relevants)))
             (equal (len (stobjs::2darr->rows new-packed-vals))
                    (len (stobjs::2darr->rows packed-vals)))))

  (defret ncols-of-s32v-add-salt
    (equal (stobjs::2darr->ncols new-packed-vals)
           (stobjs::2darr->ncols packed-vals)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(define s32v-row-repeat-bitcols ((output-bit natp)
                              (input-bit natp)
                              (input-bits posp)
                              (row natp)
                              (s32v))
  ;; this is a very inefficient way to do it but we'll see if it's bad enough to fix
  :guard (and (<= input-bits (* 32 (s32v-ncols s32v)))
              (<= output-bit (* 32 (s32v-ncols s32v)))
              (< input-bit input-bits)
              (< row (s32v-nrows s32v)))
  :guard-hints (("goal" :in-theory (enable bitops::ash-is-expt-*-x)))
  :returns (new-s32v)
  :measure (nfix (- (* 32 (s32v-ncols s32v)) (nfix output-bit)))
  (b* (((when (mbe :logic (zp (- (* 32 (s32v-ncols s32v)) (nfix output-bit)))
                   :exec (eql output-bit (ash (s32v-ncols s32v) 5))))
        s32v)
       (bit (s32v-get-bit row input-bit s32v))
       (s32v (s32v-install-bit row output-bit bit s32v))
       (new-input-bit (+ 1 (lnfix input-bit)))
       (new-input-bit (if (eql new-input-bit (acl2::lposfix input-bits)) 0 new-input-bit)))
    (s32v-row-repeat-bitcols (+ 1 (lnfix output-bit)) new-input-bit input-bits row s32v))
  ///
  (defret s32v-nrows-of-s32v-row-repeat-bitcols
    (implies (< (nfix row) (s32v-nrows s32v))
             (equal (len (stobjs::2darr->rows new-s32v))
                    (len (stobjs::2darr->rows s32v)))))

  (defret s32v-ncols-of-s32v-row-repeat-bitcols
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v))))

(define s32v-repeat-bitcols ((num-valid-input-bits posp)
                          (row natp)
                          (s32v))
  :guard (and (<= num-valid-input-bits (* 32 (s32v-ncols s32v)))
              (<= row (s32v-nrows s32v)))
  :measure (nfix (- (s32v-nrows s32v) (nfix row)))
  :returns (new-s32v)
  (b* (((when (mbe :logic (zp (- (s32v-nrows s32v) (nfix row)))
                   :exec (eql row (s32v-nrows s32v))))
        s32v)
       (s32v (s32v-row-repeat-bitcols 0 0 num-valid-input-bits row s32v)))
    (s32v-repeat-bitcols num-valid-input-bits (+ 1 (lnfix row)) s32v))
  ///
  (defret s32v-nrows-of-s32v-repeat-bitcols
    (equal (len (stobjs::2darr->rows new-s32v))
           (len (stobjs::2darr->rows s32v))))

  (defret s32v-ncols-of-s32v-repeat-bitcols
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v))))




(define s32v-copy-cares ((col natp)
                         (in-row natp)
                         (out-row natp)
                         (packed-vals) ;; input data
                         (packed-relevants) ;; input cares
                         (s32v)) ;; output
  ;; For each word in the given in-row of packed-vals/packed-relevants, copy
  ;; the portion of packed-vals given by the mask of packed-relevants into the
  ;; corresponding word in out-row of s32v.
  :guard (and (<= (s32v-ncols s32v) (s32v-ncols packed-vals))
              (<= (s32v-ncols s32v) (s32v-ncols packed-relevants))
              (<= col (s32v-ncols s32v))
              (< in-row (s32v-nrows packed-vals))
              (< in-row (s32v-nrows packed-relevants))
              (< out-row (s32v-nrows s32v)))
  :measure (nfix (- (s32v-ncols s32v) (nfix col)))
  :returns (new-s32v)
  (b* (((when (mbe :logic (zp (- (s32v-ncols s32v) (nfix col)))
                   :exec (eql col (s32v-ncols s32v))))
        s32v)
       (in-data (s32v-get2 in-row col packed-vals))
       (in-mask (s32v-get2 in-row col packed-relevants))
       (out-data (s32v-get2 out-row col s32v))
       (new-data (logior (logand in-mask in-data)
                         (logand (lognot in-mask) out-data)))
       (s32v (s32v-set2 out-row col new-data s32v)))
    (s32v-copy-cares (1+ (lnfix col)) in-row out-row packed-vals packed-relevants s32v))
  ///
  (local (defthm not-equal-nfix-plus-1 ;; dumb thing for fixtype
           (not (equal x (+ 1 (nfix x))))
           :hints(("Goal" :in-theory (enable nfix)))))

  (defret nrows-of-s32v-copy-cares
    (implies (< (nfix out-row) (len (stobjs::2darr->rows s32v)))
             (equal (len (stobjs::2darr->rows new-s32v))
                    (len (stobjs::2darr->rows s32v)))))

  (defret ncols-of-s32v-copy-cares
    (implies (<= (nfix col) (stobjs::2darr->ncols s32v))
             (equal (stobjs::2darr->ncols new-s32v)
                    (stobjs::2darr->ncols s32v)))))

(define fraig-ctrex-invals->vecsim ((n natp)
                                    (packed-vals)
                                    (packed-relevants)
                                    (s32v)
                                    (aignet))
  :returns (new-s32v)
  :guard (and (<= n (num-ins aignet))
              (<= (s32v-ncols s32v) (s32v-ncols packed-vals))
              (<= (s32v-ncols s32v) (s32v-ncols packed-relevants))
              (<= (num-ins aignet) (s32v-nrows packed-vals))
              (<= (num-ins aignet) (s32v-nrows packed-relevants))
              (<= (num-fanins aignet) (s32v-nrows s32v)))
  :measure (nfix (- (num-ins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (eql n (num-ins aignet))))
        s32v)
       (id (innum->id n aignet))
       (s32v (s32v-copy-cares 0 n id packed-vals packed-relevants s32v)))
    (fraig-ctrex-invals->vecsim (1+ (lnfix n)) packed-vals packed-relevants s32v aignet))
  ///
  (defret nrows-of-fraig-ctrex-invals->vecsim
    (implies (<= (num-fanins aignet) (s32v-nrows s32v))
             (equal (len (stobjs::2darr->rows new-s32v))
                    (len (stobjs::2darr->rows s32v)))))

  (defret ncols-of-fraig-ctrex-invals->vecsim
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v))))

(define fraig-ctrex-regvals->vecsim ((n natp)
                                    (packed-vals)
                                    (packed-relevants)
                                    (s32v)
                                    (aignet))
  :returns (new-s32v)
  :guard (and (<= n (num-regs aignet))
              (<= (s32v-ncols s32v) (s32v-ncols packed-vals))
              (<= (s32v-ncols s32v) (s32v-ncols packed-relevants))
              (<= (+ (num-ins aignet) (num-regs aignet)) (s32v-nrows packed-vals))
              (<= (+ (num-ins aignet) (num-regs aignet)) (s32v-nrows packed-relevants))
              (<= (num-fanins aignet) (s32v-nrows s32v)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql n (num-regs aignet))))
        s32v)
       (id (regnum->id n aignet))
       (s32v (s32v-copy-cares 0 (+ (lnfix n) (num-ins aignet)) id packed-vals packed-relevants s32v)))
    (fraig-ctrex-regvals->vecsim (1+ (lnfix n)) packed-vals packed-relevants s32v aignet))
  ///
  (defret nrows-of-fraig-ctrex-regvals->vecsim
    (implies (<= (num-fanins aignet) (s32v-nrows s32v))
             (equal (len (stobjs::2darr->rows new-s32v))
                    (len (stobjs::2darr->rows s32v)))))

  (defret ncols-of-fraig-ctrex-regvals->vecsim
    (equal (stobjs::2darr->ncols new-s32v)
           (stobjs::2darr->ncols s32v))))




(define fraig-ctrexes-resim-aux ((aignet)
                                 fraig-ctrexes
                                 classes
                                 fraig-stats
                                 state)
  :guard-debug t
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp))))
  :guard (and (classes-wellformed classes)
              (fraig-ctrexes-ok fraig-ctrexes)
              (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
              (equal (classes-size classes) (num-fanins aignet))
              (equal (fraig-ctrex-in/reg-rows fraig-ctrexes)
                     (+ (num-ins aignet) (num-regs aignet))))
  :returns (mv new-classes new-fraig-ctrexes new-fraig-stats new-state)
  (b* ((nbits (fraig-ctrex-nbits fraig-ctrexes))
       ((acl2::stobj-get packed-vals packed-relevants s32v classes fraig-stats state)
        ((packed-vals (fraig-ctrex-in/reg-vals fraig-ctrexes))
         (packed-relevants (fraig-ctrex-in/reg-relevants fraig-ctrexes))
         (s32v (fraig-ctrex-data fraig-ctrexes)))
        (b* ((packed-relevants        (if (eql nbits 0)
                                          packed-relevants
                                        (s32v-repeat-bitcols nbits 0 packed-relevants)))
             (packed-vals             (if (eql nbits 0)
                                          packed-vals
                                        (s32v-repeat-bitcols nbits 0 packed-vals)))
             ((mv packed-vals state)  (if (eql 0 (s32v-nrows packed-vals))
                                          (mv packed-vals state)
                                        (s32v-add-salt nbits packed-vals packed-relevants state)))
             ((mv s32v state)         (s32v-randomize-inputs 0 s32v aignet state))
             ((mv s32v state)         (s32v-randomize-regs 0 s32v aignet state))
             (s32v                    (fraig-ctrex-invals->vecsim 0 packed-vals packed-relevants s32v aignet))
             (s32v                    (fraig-ctrex-regvals->vecsim 0 packed-vals packed-relevants s32v aignet))
             (s32v                    (aignet-vecsim-top s32v aignet))
             ((mv classes nclass-lits-refined nconst-lits-refined nclasses-refined)
              (classes-refine s32v classes aignet))
             (fraig-stats (update-fraig-class-lits-refined (+ nclass-lits-refined
                                                              (fraig-class-lits-refined fraig-stats))
                                                           fraig-stats))
             (fraig-stats (update-fraig-const-lits-refined (+ nconst-lits-refined
                                                              (fraig-const-lits-refined fraig-stats))
                                                           fraig-stats))
             (fraig-stats (update-fraig-classes-refined (+ nclasses-refined
                                                           (fraig-classes-refined fraig-stats))
                                                        fraig-stats))
             (fraig-stats (update-fraig-resims (+ 1 (fraig-resims fraig-stats)) fraig-stats)))
          (mv packed-vals packed-relevants s32v classes fraig-stats state))))
    (mv classes fraig-ctrexes fraig-stats state))
  ///
  (defret classes-wellformed-of-fraig-ctrexes-resim-aux
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes)))

  (defret classes-size-of-fraig-ctrexes-resim-aux
    (equal (classes-size new-classes) (classes-size classes)))

  (defret fraig-ctrexes-ok-of-fraig-ctrexes-resim-aux
    (implies (and (fraig-ctrexes-ok fraig-ctrexes)
                  (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet)))
             (fraig-ctrexes-ok new-fraig-ctrexes))
    :hints((and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defret fraig-ctrex-data-rows-of-fraig-ctrexes-resim-aux
    (implies (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
             (equal (fraig-ctrex-data-rows new-fraig-ctrexes)
                    (num-fanins aignet)))
    :hints(("Goal" :in-theory (enable fraig-ctrex-data-rows))))

  (defret fraig-ctrex-in/reg-rows-of-fraig-ctrexes-resim-aux
    (equal (fraig-ctrex-in/reg-rows new-fraig-ctrexes)
           (fraig-ctrex-in/reg-rows fraig-ctrexes))
    :hints(("Goal" :in-theory (enable fraig-ctrex-in/reg-rows))))

  (defret fraig-ctrex-ncols-of-fraig-ctrexes-resim-aux
    (equal (fraig-ctrex-ncols new-fraig-ctrexes)
           (fraig-ctrex-ncols fraig-ctrexes))
    :hints(("Goal" :in-theory (enable fraig-ctrex-ncols))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(define fraig-ctrexes-resim ((aignet)
                             fraig-ctrexes
                             classes
                             fraig-stats
                             state)
  :guard-debug t
  :guard-hints (("goal" :do-not-induct t))
  :guard (and (classes-wellformed classes)
              (fraig-ctrexes-ok fraig-ctrexes)
              (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
              (equal (classes-size classes) (num-fanins aignet))
              (equal (fraig-ctrex-in/reg-rows fraig-ctrexes)
                     (+ (num-ins aignet) (num-regs aignet))))
  :returns (mv new-classes new-fraig-ctrexes new-fraig-stats new-state)
  (b* (((mv classes fraig-ctrexes fraig-stats state)
        (fraig-ctrexes-resim-aux aignet fraig-ctrexes classes fraig-stats state))
       (fraig-ctrexes (fraig-ctrexes-reinit fraig-ctrexes)))
    (mv classes fraig-ctrexes fraig-stats state))
  ///
  (defret classes-wellformed-of-fraig-ctrexes-resim
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes)))

  (defret classes-size-of-fraig-ctrexes-resim
    (equal (classes-size new-classes) (classes-size classes)))

  (defret fraig-ctrexes-ok-of-fraig-ctrexes-resim
    (implies (and (fraig-ctrexes-ok fraig-ctrexes)
                  (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet)))
             (fraig-ctrexes-ok new-fraig-ctrexes))
    :hints((and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defret fraig-ctrex-data-rows-of-fraig-ctrexes-resim
    (implies (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
             (equal (fraig-ctrex-data-rows new-fraig-ctrexes)
                    (num-fanins aignet))))

  (defret fraig-ctrex-in/reg-rows-of-fraig-ctrexes-resim
    (equal (fraig-ctrex-in/reg-rows new-fraig-ctrexes)
           (fraig-ctrex-in/reg-rows fraig-ctrexes)))

  (defret fraig-ctrex-ncols-of-fraig-ctrexes-resim
    (equal (fraig-ctrex-ncols new-fraig-ctrexes)
           (fraig-ctrex-ncols fraig-ctrexes)))

  (defret fraig-ctrex-nbits-of-fraig-ctrexes-resim
    (equal (nth *fraig-ctrex-nbits* new-fraig-ctrexes) 0))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(define fraig-stats-update-last-chance (forcedp fraig-stats)
  (b* ((fraig-stats (update-fraig-last-chance-refines
                     (+ 1 (fraig-last-chance-refines fraig-stats)) fraig-stats))
       ((unless forcedp) fraig-stats)
       (fraig-stats (update-fraig-last-chance-refines-forced
                     (+ 1 (fraig-last-chance-refines-forced fraig-stats)) fraig-stats)))
    fraig-stats))

(define fraig-ctrexes-maybe-resim ((node natp)
                                   (config fraig-config-p)
                                   (aignet "input aignet")
                                   (fraig-ctrexes)
                                   (classes "equiv classes data structure")
                                   (fraig-stats "statistics record")
                                   (state))
  :guard (and (id-existsp node aignet)
              (classes-wellformed classes)
              (fraig-ctrexes-ok fraig-ctrexes)
              (equal (fraig-ctrex-data-rows fraig-ctrexes) (classes-size classes))
              (equal (classes-size classes) (num-fanins aignet))
              (equal (fraig-ctrex-in/reg-rows fraig-ctrexes) (+ (num-ins aignet) (num-regs aignet))))
  :returns (mv forced-last-chancep new-classes new-fraig-ctrexes new-fraig-stats new-state)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp))))
  (b* (((fraig-config config))
       (head (node-head node classes))
       (force-resim (and config.ctrex-force-resim
                         (b* (((acl2::stobj-get force-resim)
                               ((bitarr (fraig-ctrex-resim-classes fraig-ctrexes)))
                               (eql 1 (get-bit head bitarr))))
                           force-resim)))
       ((unless (or (>= (lnfix (fraig-ctrex-nbits fraig-ctrexes))
                        (* 32 (fraig-ctrex-ncols fraig-ctrexes)))
                    (and config.ctrex-queue-limit
                         (>= (lnfix (fraig-ctrex-count fraig-ctrexes))
                             config.ctrex-queue-limit))
                    force-resim))
        (mv nil classes fraig-ctrexes fraig-stats state))
       ((mv classes fraig-ctrexes fraig-stats state)
        (fraig-ctrexes-resim aignet fraig-ctrexes classes fraig-stats state))
       (fraig-stats (if (eql head (node-head node classes))
                        fraig-stats
                      (fraig-stats-update-last-chance force-resim fraig-stats))))
    (mv (and force-resim (not (eql head (node-head node classes))))
        classes fraig-ctrexes fraig-stats state))
                      
  ///
  (defret classes-wellformed-of-fraig-ctrexes-maybe-resim
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes)))

  (defret classes-size-of-fraig-ctrexes-maybe-resim
    (equal (classes-size new-classes) (classes-size classes)))

  (defret fraig-ctrexes-ok-of-fraig-ctrexes-maybe-resim
    (implies (and (fraig-ctrexes-ok fraig-ctrexes)
                  (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet)))
             (fraig-ctrexes-ok new-fraig-ctrexes))
    :hints((and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defret fraig-ctrex-data-rows-of-fraig-ctrexes-maybe-resim
    (implies (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
             (equal (fraig-ctrex-data-rows new-fraig-ctrexes)
                    (num-fanins aignet))))

  (defret fraig-ctrex-in/reg-rows-of-fraig-ctrexes-maybe-resim
    (equal (fraig-ctrex-in/reg-rows new-fraig-ctrexes)
           (fraig-ctrex-in/reg-rows fraig-ctrexes)))

  (defret fraig-ctrex-ncols-of-fraig-ctrexes-maybe-resim
    (equal (fraig-ctrex-ncols new-fraig-ctrexes)
           (fraig-ctrex-ncols fraig-ctrexes)))

  (defret fraig-ctrex-nbits-of-fraig-ctrexes-maybe-resim
    (implies (and (<= (nfix (nth *fraig-ctrex-nbits* fraig-ctrexes))
                      (* 32 (fraig-ctrex-ncols fraig-ctrexes)))
                  (posp (fraig-ctrex-ncols fraig-ctrexes)))
             (< (nfix (nth *fraig-ctrex-nbits* new-fraig-ctrexes))
                (* 32 (fraig-ctrex-ncols fraig-ctrexes))))
    :rule-classes :linear)

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))




(define fraig-stats-increment-coincident-nodes (fraig-stats)
  (update-fraig-coincident-nodes (+ 1 (fraig-coincident-nodes fraig-stats)) fraig-stats))

(define fraig-stats-increment-forced-proved (forcedp fraig-stats)
  (if forcedp
      (update-fraig-last-chance-refines-forced-proved
       (+ 1 (fraig-last-chance-refines-forced-proved fraig-stats)) fraig-stats)
    fraig-stats))
               
(define fraig-sweep-node ((node natp "Current node ID")
                          (aignet  "Input aignet")
                          (aignet2 "New aignet")
                          (copy "Mapping from old to new aignet")
                          (strash "strash for aignet2")
                          (fraig-ctrexes "memory in which to simulate ctrexes")
                          (classes "equiv classes data structure")
                          (aignet-refcounts "refcounts for aignet2 for sat generation")
                          (sat-lits "sat lit mapping for aignet2")
                          (ipasir "sat solver on aignet2")
                          (fraig-stats "statistics collection")
                          (config fraig-config-p "options")
                          (state))
  :guard (and (<= (num-fanins aignet) (lits-length copy))
              (aignet-copies-in-bounds copy aignet2)
              (classes-wellformed classes)
              (equal (classes-size classes) (num-fanins aignet))
              (fraig-ctrexes-ok fraig-ctrexes)
              (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
              (equal (fraig-ctrex-in/reg-rows fraig-ctrexes)
                     (+ (num-ins aignet) (num-regs aignet)))
              (id-existsp node aignet)
              (equal (num-ins aignet) (num-ins aignet2))
              (equal (num-regs aignet) (num-regs aignet2))
              (non-exec (and (not (eq (ipasir::ipasir$a->status ipasir) :undef))
                             (not (ipasir::ipasir$a->new-clause ipasir))
                             (not (ipasir::ipasir$a->assumption ipasir))))
              (sat-lits-wfp sat-lits aignet2))
  :verify-guards nil
  :returns (mv new-aignet2
               new-copy
               new-strash
               new-fraig-ctrexes
               new-classes
               new-refcounts
               new-sat-lits
               new-ipasir
               new-fraig-stats
               new-state)
  (b* ((n (lnfix node))
       (slot0 (id->slot n 0 aignet))
       (type (snode->type slot0))
       (ipasir (ipasir::ipasir-cancel-new-clause ipasir))
       (ipasir (ipasir::ipasir-cancel-assumption ipasir))
       (ipasir (ipasir::ipasir-input ipasir)))
    (aignet-case
      type
      ;; assume inputs already set up and outputs come later
      :in (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state)
      :out (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state)
      :const (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state)
      :gate
      (b* ((fraig-stats (update-fraig-gates-processed (+ 1 (fraig-gates-processed fraig-stats)) fraig-stats))
           ;; Check if there is a pending ctrex that needs resimulating.
           ((mv forced-refinedp classes fraig-ctrexes fraig-stats state)
            (fraig-ctrexes-maybe-resim n config aignet fraig-ctrexes classes fraig-stats state))
           (lit0 (snode->fanin slot0))
           (slot1 (id->slot n 1 aignet))
           (lit1 (snode->fanin slot1))
           (lit0-copy (lit-copy lit0 copy))
           (lit1-copy (lit-copy lit1 copy))
           (prev-count (num-fanins aignet2))
           ((fraig-config config))
           ;; make AND/XOR of the two corresponding lits; this is the new node if
           ;; the candidate equivalent isn't equivalent
           ((mv and-lit strash aignet2)
            (if (eql 1 (snode->regp slot1))
                (aignet-hash-xor lit0-copy lit1-copy config.gatesimp strash aignet2)
              (aignet-hash-and lit0-copy lit1-copy config.gatesimp strash aignet2)))
           ;; update refcounts and copy for new node.
           ;; maybe-update-refs is sensitive to whether a new node was actually added or not.
           ;; copy needs to be updated again if we prove an equivalence.
           (aignet-refcounts (aignet-maybe-update-refs prev-count aignet-refcounts aignet2))
           (copy (set-lit n and-lit copy))
           (equiv-node (node-head n classes))
           ((when (>= equiv-node n))
            ;; no equivalent, done
            (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state))
           (equiv-lit (make-lit equiv-node
                                (b-xor (id->phase equiv-node aignet)
                                       (snode->phase slot1))))
           (equiv-copy (lit-copy equiv-lit copy))
           ((when (eql equiv-copy and-lit))
            ;; already hashed/simplified to equivalent, done
            (b* ((fraig-stats (fraig-stats-increment-coincident-nodes fraig-stats)))
              (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state)))
           (- (and (eql 0 (logand #xff (fraig-total-checks fraig-stats)))
                   (print-fraig-stats-noninitial classes ipasir fraig-stats :start-node n)))
           (- (and (eql (lit-id equiv-copy)
                        (lit-id and-lit))
                   (raise "Programming error -- node and equivalence candidate were the same ID but negated")))
           ;; Check equivalence of the two literals
           ((mv status sat-lits ipasir fraig-stats)
            (ipasir-check-aignet-equivalence and-lit equiv-copy config aignet2 aignet-refcounts sat-lits ipasir fraig-stats))
           ((when (eq status :failed))
            ;; nothing to do really, maybe mark equivalence as failed?
            (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state))
           ((when (eq status :unsat))
            ;; nodes are equivalent! change copy so that it uses the equivalent rather than the new node.
            (b* ((fraig-stats (fraig-stats-increment-forced-proved forced-refinedp fraig-stats))
                 (copy (set-lit n equiv-copy copy)))
              (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state)))
           ;; Generate the counterexample.
           ((mv fraig-ctrexes state) (fraig-store-ctrex and-lit equiv-copy equiv-node aignet2 sat-lits ipasir fraig-ctrexes state)))
        (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state))))
  ///

  (local (in-theory (disable fraig-stats-implies-natp-of-nth
                             lookup-id-out-of-bounds
                             aignet-copy-is-comb-equivalent-for-non-gates-implies-lit-eval
                             satlink::equal-of-lit-negate-component-rewrites
                             satlink::equal-of-lit-negate-cond-component-rewrites)))

  (verify-guards fraig-sweep-node
    ;; :guard-debug t
    :hints (("goal" :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp
                                      fraig-stats-implies-natp-of-nth))))
    :otf-flg t)


  (def-aignet-preservation-thms fraig-sweep-node :stobjname aignet2)

  (defret ipasir-guard-of-fraig-sweep-node
    (and (not (equal (ipasir::ipasir$a->status new-ipasir) :undef))
         (not (ipasir::ipasir$a->new-clause new-ipasir))
         (not (ipasir::ipasir$a->assumption new-ipasir))))

  (defret classes-wellformed-of-fraig-sweep-node
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes)))

  (defret classes-size-of-fraig-sweep-node
    (equal (classes-size new-classes)
           (classes-size classes)))

  (defret fraig-ctrex-data-rows-of-fraig-sweep-node
    (implies (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
             (equal (fraig-ctrex-data-rows new-fraig-ctrexes)
                    (num-fanins aignet))))

  (defret fraig-ctrex-in/reg-rows-of-fraig-sweep-node
    (implies (equal (fraig-ctrex-in/reg-rows fraig-ctrexes) (+ (num-ins aignet2) (num-regs aignet2)))
             (equal (fraig-ctrex-in/reg-rows new-fraig-ctrexes)
                    (+ (num-ins aignet2) (num-regs aignet2)))))

  (defret fraig-ctrex-ncols-of-fraig-sweep-node
    (equal (fraig-ctrex-ncols new-fraig-ctrexes)
           (fraig-ctrex-ncols fraig-ctrexes)))

  (defret fraig-ctrexes-ok-of-fraig-sweep-node
    (implies (and (fraig-ctrexes-ok fraig-ctrexes)
                  (classes-wellformed classes)
                  (equal (classes-size classes) (num-fanins aignet))
                  (<= (nfix node) (fanin-count aignet))
                  (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
                  (<= (nfix (fraig-ctrex-nbits fraig-ctrexes))
                      (* 32 (fraig-ctrex-ncols fraig-ctrexes)))
                  (equal (fraig-ctrex-in/reg-rows fraig-ctrexes)
                         (+ (num-ins aignet2) (num-regs aignet2))))
             (fraig-ctrexes-ok new-fraig-ctrexes)))


  (defret stype-count-preserved-of-fraig-sweep-node
    (implies (and (not (eq (stype-fix stype) (and-stype)))
                  (not (eq (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (local (defthm len-update-nth-lit-preserved
           (implies (< (nfix n) (len lits))
                    (equal (len (update-nth-lit n val lits))
                           (len lits)))
           :hints(("Goal" :in-theory (enable update-nth-lit)))))

  (defret copy-len-of-fraig-sweep-node
    (implies (and (< (fanin-count aignet) (len copy))
                  (<= (nfix node) (fanin-count aignet)))
             (equal (len new-copy) (len copy))))

  (defret sat-lits-wfp-of-fraig-sweep-node
    (implies (sat-lits-wfp sat-lits aignet2)
             (sat-lits-wfp new-sat-lits new-aignet2)))

  (local (defthm lit-copy-of-make-lit
           (equal (lit-copy (make-lit id neg) copy)
                  (lit-negate-cond (nth-lit id copy) neg))
           :hints(("Goal" :in-theory (enable lit-copy)))))

  (defret ipasir-formula-wfp-of-fraig-sweep-node
    (implies (and (sat-lits-wfp sat-lits aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
                  (<= (nfix node) (fanin-count aignet)))
             (sat-lit-list-listp (ipasir::ipasir$a->formula new-ipasir) new-sat-lits)))

  (defret aignet-copies-ok-of-fraig-sweep-node
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (equal n (+ 1 (fanin-count aignet)))
                  (<= (nfix node) (fanin-count aignet)))
             (aignet-copies-in-bounds new-copy new-aignet2)))

  ;; (local (defthm gate-stype-implies-less-than-max-fanin
  ;;          (implies (and (equal (ctype (stype (car (lookup-id node aignet)))) :gate)
  ;;                        (natp node))
  ;;                   (<= node (fanin-count aignet)))
  ;;          :hints(("Goal" :in-theory (enable find-max-fanin lookup-id)))
  ;;          :rule-classes :forward-chaining))
             
  (defret cnf-for-aignet-of-fraig-sweep-node
    (implies (and (cnf-for-aignet aignet2 (ipasir::ipasir$a->formula ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits))
             (cnf-for-aignet new-aignet2 (ipasir::ipasir$a->formula new-ipasir) new-sat-lits)))

  (defret aignet-copy-is-comb-equivalent-for-non-gates-of-fraig-sweep-node
    (implies (and (aignet-copy-is-comb-equivalent-for-non-gates (num-fanins aignet) aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (aignet-copy-is-comb-equivalent-for-non-gates (+ 1 (fanin-count aignet)) aignet new-copy new-aignet2)))

  (local (defthm lit-eval-of-equal-to-hash-and-preexisting
           (implies (and (aignet-litp lit aignet)
                         (equal lit (mv-nth 0 (aignet-hash-and lit1 lit2 gatesimp strash aignet))))
                    (equal (lit-eval lit invals regvals aignet)
                           (b-and (lit-eval lit1 invals regvals aignet)
                                  (lit-eval lit2 invals regvals aignet))))
           :hints (("goal" :use ((:instance lit-eval-of-aignet-hash-and))
                    :in-theory (disable lit-eval-of-aignet-hash-and)))))

  (local (defthm lit-eval-of-lit-negate-cond-equal-to-hash-and-preexisting
           (implies (and (aignet-litp lit aignet)
                         (equal (lit-negate-cond lit neg)
                                (mv-nth 0 (aignet-hash-and lit1 lit2 gatesimp strash aignet))))
                    (equal (lit-eval lit invals regvals aignet)
                           (b-xor neg
                                  (b-and (lit-eval lit1 invals regvals aignet)
                                         (lit-eval lit2 invals regvals aignet)))))
           :hints (("goal" :use ((:instance lit-eval-of-lit-negate-cond))
                    :in-theory (disable lit-eval-of-lit-negate-cond)))))

  
  (local (defthm lit-eval-of-equal-to-hash-xor-preexisting
           (implies (and (aignet-litp lit aignet)
                         (equal lit (mv-nth 0 (aignet-hash-xor lit1 lit2 gatesimp strash aignet))))
                    (equal (lit-eval lit invals regvals aignet)
                           (b-xor (lit-eval lit1 invals regvals aignet)
                                  (lit-eval lit2 invals regvals aignet))))
           :hints (("goal" :use ((:instance lit-eval-of-aignet-hash-xor))
                    :in-theory (disable lit-eval-of-aignet-hash-xor)))))

  (local (defthm lit-eval-of-lit-negate-cond-equal-to-hash-xor-preexisting
           (implies (and (aignet-litp lit aignet)
                         (equal (lit-negate-cond lit neg)
                                (mv-nth 0 (aignet-hash-xor lit1 lit2 gatesimp strash aignet))))
                    (equal (lit-eval lit invals regvals aignet)
                           (b-xor neg
                                  (b-xor (lit-eval lit1 invals regvals aignet)
                                         (lit-eval lit2 invals regvals aignet)))))
           :hints (("goal" :use ((:instance lit-eval-of-lit-negate-cond))
                    :in-theory (disable lit-eval-of-lit-negate-cond)))))



  
  
  (defret aignet-copy-is-comb-equivalent-of-fraig-sweep-node
    (implies (and (nat-equiv node1 node)
                  (aignet-copy-is-comb-equivalent node aignet copy aignet2)
                  (aignet-copy-is-comb-equivalent-for-non-gates (num-fanins aignet) aignet copy aignet2)
                  (cnf-for-aignet aignet2 (ipasir::ipasir$a->formula ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
                  (< (nfix node) (num-fanins aignet)))
             (aignet-copy-is-comb-equivalent
              (+ 1 node1) aignet new-copy new-aignet2))
    :hints (("goal" :expand ((:free (n copy aignet2)
                              (aignet-copy-is-comb-equivalent
                               (+ 1 n) aignet copy aignet2)))
             ;; :in-theory (enable aignet-idp)
             )
            (and stable-under-simplificationp
                 (b* ((lit (car (last clause))))
                   (and (consp lit) (eq (car lit) 'aignet-lits-comb-equivalent)
                        `(:expand (,lit)))))
            (and stable-under-simplificationp
                 (let ((witness (acl2::find-call-lst
                                 'aignet-lits-comb-equivalent-witness
                                 clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((mv-nth '0 ,witness) . invals)
                              ((mv-nth '1 ,witness) . regvals)))
                    :expand ((:free (invals regvals)
                              (id-eval node invals regvals aignet))
                             (:free (lit invals regvals)
                              (lit-eval lit invals regvals aignet))
                             (:free (lit1 lit2 invals regvals)
                              (eval-and-of-lits lit1 lit2 invals regvals aignet))
                             (:free (lit1 lit2 invals regvals)
                              (eval-xor-of-lits lit1 lit2 invals regvals aignet))))))
            ;; (and stable-under-simplificationp
            ;;      '(:cases ((equal 1 (B-XOR (AIGNET$A::ID->PHASE NODE AIGNET)
            ;;                                (AIGNET$A::ID->PHASE (NODE-HEAD NODE CLASSES)
            ;;                                                     AIGNET))))))
            ))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(define fraig-sweep-aux ((node natp "Current node ID")
                         (aignet  "Input aignet")
                         (aignet2 "New aignet")
                         (copy "Mapping from old to new aignet")
                         (strash "strash for aignet2")
                         (fraig-ctrexes "memory in which to simulate ctrexes")
                         (classes "equiv classes data structure")
                         (aignet-refcounts "refcounts for aignet2 for sat generation")
                         (sat-lits "sat lit mapping for aignet2")
                         (ipasir "sat solver on aignet2")
                         (fraig-stats "statistics collection")
                         (config fraig-config-p)
                         (state))
  :returns (mv new-aignet2
               new-copy
               new-strash
               new-fraig-ctrexes
               new-classes
               new-refcounts
               new-sat-lits
               new-ipasir
               new-fraig-stats
               new-state)
  :guard (and (<= (num-fanins aignet) (lits-length copy))
              (aignet-copies-in-bounds copy aignet2)
              (classes-wellformed classes)
              (equal (classes-size classes) (num-fanins aignet))
              (fraig-ctrexes-ok fraig-ctrexes)
              (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
              (equal (fraig-ctrex-in/reg-rows fraig-ctrexes)
                     (+ (num-ins aignet) (num-regs aignet)))
              (<= node (num-fanins aignet))
              (equal (num-ins aignet) (num-ins aignet2))
              (equal (num-regs aignet) (num-regs aignet2))
              (non-exec (and (not (eq (ipasir::ipasir$a->status ipasir) :undef))
                             (not (ipasir::ipasir$a->new-clause ipasir))
                             (not (ipasir::ipasir$a->assumption ipasir))))
              (sat-lits-wfp sat-lits aignet2))
  :guard-hints (("goal" :do-not-induct t)
                (and stable-under-simplificationp
                     '(:in-theory (enable aignet-idp))))
  :measure (nfix (+ (num-fanins aignet) (- (nfix node))))
  (b* (((when (mbe :logic (zp (+ (num-fanins aignet) (- (nfix node))))
                   :exec (eql (num-fanins aignet) node)))
        (b* ((ipasir (ipasir::ipasir-cancel-new-clause ipasir))
             (ipasir (ipasir::ipasir-cancel-assumption ipasir))
             (ipasir (ipasir::ipasir-input ipasir)))
          (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state)))
       ((mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state)
        (fraig-sweep-node node aignet aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats config state)))
    (fraig-sweep-aux
     (+ 1 (lnfix node)) aignet aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats config state))
  ///

  (def-aignet-preservation-thms fraig-sweep-aux :stobjname aignet2)

  (defret ipasir-guard-of-fraig-sweep-aux
    (and (not (equal (ipasir::ipasir$a->status new-ipasir) :undef))
         (not (ipasir::ipasir$a->new-clause new-ipasir))
         (not (ipasir::ipasir$a->assumption new-ipasir))))

  (defret classes-wellformed-of-fraig-sweep-aux
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes)))

  (defret classes-size-of-fraig-sweep-aux
    (equal (classes-size new-classes)
           (classes-size classes)))

  (defret fraig-ctrex-data-rows-of-fraig-sweep-aux
    (implies (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
             (equal (fraig-ctrex-data-rows new-fraig-ctrexes)
                    (num-fanins aignet))))

  (defret fraig-ctrex-in/reg-rows-of-fraig-sweep-aux
    (implies (equal (fraig-ctrex-in/reg-rows fraig-ctrexes) (+ (num-ins aignet2) (num-regs aignet2)))
             (equal (fraig-ctrex-in/reg-rows new-fraig-ctrexes)
                    (+ (num-ins aignet2) (num-regs aignet2)))))

  (defret fraig-ctrex-ncols-of-fraig-sweep-aux
    (equal (fraig-ctrex-ncols new-fraig-ctrexes)
           (fraig-ctrex-ncols fraig-ctrexes)))

  (defret fraig-ctrexes-ok-of-fraig-sweep-aux
    (implies (and (fraig-ctrexes-ok fraig-ctrexes)
                  (classes-wellformed classes)
                  (equal (classes-size classes) (num-fanins aignet))
                  (equal (fraig-ctrex-data-rows fraig-ctrexes) (num-fanins aignet))
                  (<= (nfix (fraig-ctrex-nbits fraig-ctrexes))
                      (* 32 (fraig-ctrex-ncols fraig-ctrexes)))
                  (equal (fraig-ctrex-in/reg-rows fraig-ctrexes)
                         (+ (num-ins aignet2) (num-regs aignet2))))
             (fraig-ctrexes-ok new-fraig-ctrexes)))

  (defret stype-count-preserved-of-fraig-sweep-aux
    (implies (and (not (eq (stype-fix stype) (and-stype)))
                  (not (eq (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (local (defthm len-update-nth-lit-preserved
           (implies (< (nfix n) (len lits))
                    (equal (len (update-nth-lit n val lits))
                           (len lits)))
           :hints(("Goal" :in-theory (enable update-nth-lit)))))

  (defret copy-len-of-fraig-sweep-aux
    (implies (and (< (fanin-count aignet) (len copy))
                  (<= (nfix node) (fanin-count aignet)))
             (equal (len new-copy) (len copy))))

  (defret sat-lits-wfp-of-fraig-sweep-aux
    (implies (sat-lits-wfp sat-lits aignet2)
             (sat-lits-wfp new-sat-lits new-aignet2)))

  (defret ipasir-formula-wfp-of-fraig-sweep-aux
    (implies (and (sat-lits-wfp sat-lits aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits)
                  (<= (nfix node) (fanin-count aignet)))
             (sat-lit-list-listp (ipasir::ipasir$a->formula new-ipasir) new-sat-lits)))

  (defret aignet-copies-ok-of-fraig-sweep-aux
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (equal n (+ 1 (fanin-count aignet))))
             (aignet-copies-in-bounds new-copy new-aignet2))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-copies-ok-of-fraig-sweep-node))
                   :in-theory (disable aignet-copies-ok-of-fraig-sweep-node)))))
             
  (defret cnf-for-aignet-of-fraig-sweep-aux
    (implies (and (cnf-for-aignet aignet2 (ipasir::ipasir$a->formula ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits))
             (cnf-for-aignet new-aignet2 (ipasir::ipasir$a->formula new-ipasir) new-sat-lits)))

  (defret aignet-copy-is-comb-equivalent-for-non-gates-of-fraig-sweep-aux
    (implies (and (aignet-copy-is-comb-equivalent-for-non-gates (num-fanins aignet) aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (aignet-copy-is-comb-equivalent-for-non-gates (+ 1 (fanin-count aignet)) aignet new-copy new-aignet2)))

  (local (defthm aignet-copy-is-comb-equivalent-when-less
           (implies (and (aignet-copy-is-comb-equivalent n aignet copy aignet2)
                         (<= (nfix m) (nfix n)))
                    (aignet-copy-is-comb-equivalent m aignet copy aignet2))
           :hints(("Goal" :in-theory (enable aignet-copy-is-comb-equivalent)
                   :induct (aignet-copy-is-comb-equivalent n aignet copy aignet2)))))


  (defret aignet-copy-is-comb-equivalent-of-fraig-sweep-aux
    (implies (and (aignet-copy-is-comb-equivalent node aignet copy aignet2)
                  (aignet-copy-is-comb-equivalent-for-non-gates (num-fanins aignet) aignet copy aignet2)
                  (cnf-for-aignet aignet2 (ipasir::ipasir$a->formula ipasir) sat-lits)
                  (sat-lits-wfp sat-lits aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (sat-lit-list-listp (ipasir::ipasir$a->formula ipasir) sat-lits))
             (aignet-copy-is-comb-equivalent
              (+ 1 (fanin-count aignet)) aignet new-copy new-aignet2)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))



(define fraig-sweep ((aignet  "Input aignet")
                     (aignet2 "New aignet")
                     (copy "Mapping from old to new aignet")
                     (strash "strash for aignet2")
                     (classes "equiv classes data structure")
                     (config fraig-config-p)
                     (state))
  :returns (mv new-aignet2
               new-copy
               new-strash
               new-classes
               new-state)
  :guard (and (<= (num-fanins aignet) (lits-length copy))
              (aignet-copies-in-bounds copy aignet2)
              (classes-wellformed classes)
              (equal (classes-size classes) (num-fanins aignet))
              (equal (num-ins aignet) (num-ins aignet2))
              (equal (num-regs aignet) (num-regs aignet2)))
  :guard-debug t
  ;; need to ensure:
  ;; (and (equal (classes-size classes) (s32v-nrows s32v))
  ;;             (<= 1 (s32v-ncols s32v))
  ;;             (<= (num-fanins aignet) (s32v-nrows s32v))
  ;;             (non-exec (and (not (eq (ipasir::ipasir$a->status ipasir) :undef))
  ;;                            (not (ipasir::ipasir$a->new-clause ipasir))
  ;;                            (not (ipasir::ipasir$a->assumption ipasir))))
  ;;             (sat-lits-wfp sat-lits aignet2))

  (b* (((acl2::local-stobjs fraig-ctrexes sat-lits aignet-refcounts fraig-stats)
        (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits fraig-stats state))
       ((ipasir::local-ipasir ipasir)
        (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state))
       ((fraig-config config))
       (ipasir (ipasir-set-limit ipasir config.ipasir-limit))
       (fraig-ctrexes
        (fraig-ctrexes-init config.sim-words fraig-ctrexes aignet))
       (sat-lits (resize-aignet->sat (ash (num-fanins aignet) -1) sat-lits))
       ((mv nclasses nconst-lits nclass-lits) (classes-counts classes))
       (fraig-stats (update-fraig-initial-nclasses nclasses fraig-stats))
       (fraig-stats (update-fraig-initial-nconst-lits nconst-lits fraig-stats))
       (fraig-stats (update-fraig-initial-nclass-lits nclass-lits fraig-stats))
       (- (print-fraig-stats-initial fraig-stats))
       ((mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state)
        (fraig-sweep-aux 0 aignet aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats config state))
       (- (print-aignet-stats "Tmp" aignet2))
       (- (print-fraig-stats-noninitial classes ipasir fraig-stats)))
    (mv aignet2 copy strash fraig-ctrexes classes aignet-refcounts sat-lits ipasir fraig-stats state))
  ///
  (def-aignet-preservation-thms fraig-sweep :stobjname aignet2)

  (defret classes-wellformed-of-fraig-sweep
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes)))

  (defret classes-size-of-fraig-sweep
    (equal (classes-size new-classes)
           (classes-size classes)))

  (defret stype-count-preserved-of-fraig-sweep
    (implies (and (not (eq (stype-fix stype) (and-stype)))
                  (not (eq (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret copy-len-of-fraig-sweep
    (implies (< (fanin-count aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (defret aignet-copies-ok-of-fraig-sweep
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret aignet-copy-is-comb-equivalent-for-non-gates-of-fraig-sweep
    (implies (and (aignet-copy-is-comb-equivalent-for-non-gates (num-fanins aignet) aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (aignet-copy-is-comb-equivalent-for-non-gates (+ 1 (fanin-count aignet)) aignet new-copy new-aignet2)))



  (defret aignet-copy-is-comb-equivalent-of-fraig-sweep
    (implies (and (aignet-copy-is-comb-equivalent-for-non-gates (num-fanins aignet) aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (aignet-copy-is-comb-equivalent
              (+ 1 (fanin-count aignet)) aignet new-copy new-aignet2)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(define fraig-initial-sim ((count natp)
                           (s32v)
                           (classes)
                           (aignet)
                           (state))
  :returns (mv new-classes new-s32v new-state)
  :guard (and (classes-wellformed classes)
              (<= (classes-size classes) (num-fanins aignet))
              (<= (num-fanins aignet) (classes-size classes))
              (equal (classes-size classes) (s32v-nrows s32v)))
  (b* (((when (zp count)) (mv classes s32v state))
       ((mv s32v state) (s32v-randomize-inputs 0 s32v aignet state))
       ((mv s32v state) (s32v-randomize-regs 0 s32v aignet state))
       (s32v (aignet-vecsim-top s32v aignet))
       ((mv classes & & &) (classes-refine s32v classes aignet)))
    (fraig-initial-sim (1- count) s32v classes aignet state))
  ///
  (defret classes-wellformed-of-fraig-initial-sim
    (implies (classes-wellformed classes)
             (classes-wellformed new-classes)))
  
  (defret classes-size-of-fraig-initial-sim
    (equal (classes-size new-classes)
           (classes-size classes)))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))
    
  




(define fraig-core-aux ((aignet  "Input aignet")
                        (aignet2 "New aignet -- will be emptied")
                        (config fraig-config-p)
                        copy strash classes s32v 
                        (state))
  :guard (non-exec (and (equal strash (create-strash))
                        (equal s32v (create-s32v))
                        (equal classes (create-classes))))
  :guard-debug t
  :returns (mv new-aignet2 new-copy new-strash new-classes new-s32v new-state)
  (b* (((fraig-config config))
       (- (and config.random-seed-name (acl2::seed-random$ config.random-seed-name)))
       (classes (mbe :logic (non-exec (create-classes))
                     :exec classes))
       (classes (if config.outs-only
                    (classes-init-outs classes aignet)
                  (classes-init (num-fanins aignet) classes)))
       (s32v (mbe :logic (non-exec (create-s32v))
                  :exec s32v))
       (s32v (s32v-resize-cols config.initial-sim-words s32v))
       (s32v (s32v-resize-rows (classes-size classes) s32v))
       ((mv classes s32v state) (fraig-initial-sim config.initial-sim-rounds s32v classes aignet state))
       (strash (mbe :logic (non-exec '(nil))
                    :exec (strashtab-init (num-gates aignet) nil nil strash)))
       ((mv copy aignet2) (init-copy-comb aignet copy aignet2))
       ((mv aignet2 copy strash classes state)
        (fraig-sweep aignet aignet2 copy strash classes config state))
       (aignet2 (finish-copy-comb aignet copy aignet2)))
    (mv aignet2 copy strash classes s32v state))
  ///
  (defret num-ins-of-fraig-core-aux
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-fraig-core-aux
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-fraig-core-aux
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret fraig-core-aux-comb-equivalent
    (comb-equiv new-aignet2 aignet))

  (defret classes-wellformed-of-fraig-core-aux
    (classes-wellformed new-classes))

  (defret classes-size-of-fraig-core-aux
    (equal (classes-size new-classes)
           (num-fanins aignet)))

  (defthm normalize-input-of-fraig-core-aux
    (implies (syntaxp (not (and (equal aignet2 ''nil)
                                (equal copy ''nil)
                                (equal strash ''nil)
                                (equal classes ''nil)
                                (equal s32v ''nil))))
             (equal (fraig-core-aux aignet aignet2 config copy strash classes s32v state)
                    (fraig-core-aux aignet nil config nil nil nil nil state))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))

(define fraig-core ((aignet  "Input aignet")
                    (aignet2 "New aignet -- will be emptied")
                    (config fraig-config-p)
                    (state))

  :guard-debug t
  :returns (mv new-aignet2 new-state)
  (b* (((acl2::local-stobjs copy strash classes s32v)
        (mv aignet2 copy strash classes s32v state)))
    (fraig-core-aux aignet aignet2 config copy strash classes s32v state))
  ///
  (defret num-ins-of-fraig-core
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-fraig-core
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-fraig-core
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret fraig-core-comb-equivalent
    (comb-equiv new-aignet2 aignet))

  (defthm normalize-input-of-fraig-core
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (fraig-core aignet aignet2 config state)
                    (fraig-core aignet nil config state))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(define fraig ((aignet  "Input aignet")
               (aignet2 "New aignet -- will be emptied")
               (config fraig-config-p
                       "Settings for the transform")
               (state))
  :parents (aignet-comb-transforms)
  :short "Apply combinational SAT sweeping (fraiging) to remove redundancies in the input network."
  :long "<p>Note: This fraiging implementation is heavily based on the one in
ABC, developed and maintained at Berkeley by Alan Mishchenko.</p>

<p>Settings for the transform can be tweaked using the @('config') input, which
is a @(see fraig-config) object.</p>"
  :guard-debug t
  :returns (mv new-aignet2 new-state)
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet2 aignet-tmp state))
       ((mv aignet-tmp state) (fraig-core aignet aignet-tmp config state))
       (aignet2 (aignet-prune-comb aignet-tmp aignet2 (fraig-config->gatesimp config))))
    (mv aignet2 aignet-tmp state))
  ///
  (defret num-ins-of-fraig
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-fraig
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-fraig
    (equal (stype-count :po new-aignet2)
           (stype-count :po aignet)))

  (defret fraig-comb-equivalent
    (comb-equiv new-aignet2 aignet))

  (defthm normalize-input-of-fraig
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal (fraig aignet aignet2 config state)
                    (fraig aignet nil config state))))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


(define fraig! ((aignet  "Input aignet -- will be replaced with transformation result")
               (config fraig-config-p)
               (state))
  :guard-debug t
  :returns (mv new-aignet new-state)
  :parents (fraig)
  :short "Like @(see fraig), but overwrites the original network instead of returning a new one."
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet aignet-tmp state))
       ((mv aignet-tmp state) (fraig-core aignet aignet-tmp config state))
       (aignet (aignet-prune-comb aignet-tmp aignet (fraig-config->gatesimp config))))
    (mv aignet aignet-tmp state))
  ///
  (defret num-ins-of-fraig!
    (equal (stype-count :pi new-aignet)
           (stype-count :pi aignet)))

  (defret num-regs-of-fraig!
    (equal (stype-count :reg new-aignet)
           (stype-count :reg aignet)))

  (defret num-outs-of-fraig!
    (equal (stype-count :po new-aignet)
           (stype-count :po aignet)))

  (defret fraig!-comb-equivalent
    (comb-equiv new-aignet aignet))

  (defret w-state-of-<fn>
    (equal (w new-state) (w state))))


