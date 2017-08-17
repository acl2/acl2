

(in-package "AIGNET")

(include-book "centaur/aignet/prune" :dir :system)
(include-book "centaur/aignet/ipasir" :dir :system)
(include-book "transform-utils")

(local (include-book "centaur/satlink/cnf-basics" :dir :system))
(local (include-book "centaur/aignet/cnf" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system ))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

(local (in-theory (disable nth update-nth nfix ifix (tau-system)
                           resize-list
                           acl2::resize-list-when-atom
                           ;; acl2::resize-list-when-empty
                           )))
(local (std::add-default-post-define-hook :fix))


(define input-copy-values ((n natp) invals regvals aignet copy aignet2)
  :verify-guards nil
  :non-executable t
  :returns (input-vals)
  :measure (nfix (- (num-ins aignet) (nfix n)))
  (if (zp (- (num-ins aignet) (nfix n)))
      nil
    (cons (lit-eval (nth-lit (innum->id n aignet) copy) invals regvals aignet2)
          (input-copy-values (1+ (lnfix n)) invals regvals aignet copy aignet2)))
  ///
  (local (defret nth-of-input-copy-values-lemma
           (implies (and (<= (nfix n) (nfix m))
                         (< (nfix m) (num-ins aignet)))
                    (equal (nth (- (nfix m) (nfix n)) input-vals)
                           (lit-eval (nth-lit (innum->id m aignet) copy)
                                     invals regvals aignet2)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)
                   :induct <call>
                   :expand ((:free (cons m a b) (nth m (cons a b))))))))

  (defret nth-of-input-copy-values
    (implies (< (+ (nfix m) (nfix n)) (num-ins aignet))
             (equal (nth m input-vals)
                    (lit-eval (nth-lit (innum->id (+ (nfix m) (nfix n)) aignet) copy)
                              invals regvals aignet2)))
    :hints(("Goal" :use ((:instance nth-of-input-copy-values-lemma
                          (m (+ (nfix m) (nfix n)))))
            :in-theory (disable nth-of-input-copy-values-lemma
                                input-copy-values))))

  (defthm input-copy-values-of-update-non-input
    (implies (not (equal (stype (Car (lookup-id id aignet))) :pi))
             (equal (input-copy-values n invals regvals aignet
                                       (update-nth-lit id lit copy)
                                       aignet2)
                    (input-copy-values n invals regvals aignet copy aignet2))))

  (defthm input-copy-values-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-copies-in-bounds copy orig))
             (equal (input-copy-values n invals regvals aignet copy new)
                    (input-copy-values n invals regvals aignet copy orig))))

  (local (in-theory (enable (:i aignet-copy-dfs-rec))))

  (defthm input-copy-values-of-aignet-copy-dfs-rec
    (implies (aignet-copies-in-bounds copy aignet2)
             (b* (((mv ?new-mark ?new-copy ?new-strash ?new-aignet2)
                   (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))
               (equal (input-copy-values n invals regvals aignet new-copy new-aignet2)
                      (input-copy-values n invals regvals aignet copy aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2)))))

(define reg-copy-values ((n natp) invals regvals aignet copy aignet2)
  :verify-guards nil
  :non-executable t
  :returns (reg-vals)
  :measure (nfix (- (num-regs aignet) (nfix n)))
  (if (zp (- (num-regs aignet) (nfix n)))
      nil
    (cons (lit-eval (nth-lit (regnum->id n aignet) copy) invals regvals aignet2)
          (reg-copy-values (1+ (lnfix n)) invals regvals aignet copy aignet2)))
  ///
  (local (defret nth-of-reg-copy-values-lemma
           (implies (and (<= (nfix n) (nfix m))
                         (< (nfix m) (num-regs aignet)))
                    (equal (nth (- (nfix m) (nfix n)) reg-vals)
                           (lit-eval (nth-lit (regnum->id m aignet) copy)
                                     invals regvals aignet2)))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)
                   :induct <call>
                   :expand ((:free (cons m a b) (nth m (cons a b))))))))

  (defret nth-of-reg-copy-values
    (implies (< (+ (nfix m) (nfix n)) (num-regs aignet))
             (equal (nth m reg-vals)
                    (lit-eval (nth-lit (regnum->id (+ (nfix m) (nfix n)) aignet) copy)
                              invals regvals aignet2)))
    :hints(("Goal" :use ((:instance nth-of-reg-copy-values-lemma
                          (m (+ (nfix m) (nfix n)))))
            :in-theory (disable nth-of-reg-copy-values-lemma
                                reg-copy-values))))

  (defthm reg-copy-values-of-update-non-reg
    (implies (not (equal (stype (Car (lookup-id id aignet))) :reg))
             (equal (reg-copy-values n invals regvals aignet
                                       (update-nth-lit id lit copy)
                                       aignet2)
                    (reg-copy-values n invals regvals aignet copy aignet2))))

  (defthm reg-copy-values-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-copies-in-bounds copy orig))
             (equal (reg-copy-values n invals regvals aignet copy new)
                    (reg-copy-values n invals regvals aignet copy orig))))

  (local (in-theory (enable (:i aignet-copy-dfs-rec))))

  (defthm reg-copy-values-of-aignet-copy-dfs-rec
    (implies (aignet-copies-in-bounds copy aignet2)
             (b* (((mv ?new-mark ?new-copy ?new-strash ?new-aignet2)
                   (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))
               (equal (reg-copy-values n invals regvals aignet new-copy new-aignet2)
                      (reg-copy-values n invals regvals aignet copy aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2)))))

(defsection aignet-copy-dfs-rec
  (defthm copy-length-of-aignet-copy-dfs
    (b* (((mv ?new-mark ?new-copy ?new-strash ?new-aignet2)
          (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))
      (implies (< (nfix id) (len copy))
               (equal (len new-copy) (len copy))))
    :hints(("Goal" :in-theory (enable (:i aignet-copy-dfs-rec) update-nth-lit)
            :induct (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)
            :expand ((aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))))

  (defthm mark-length-of-aignet-copy-dfs
    (b* (((mv ?new-mark ?new-copy ?new-strash ?new-aignet2)
          (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))
      (implies (< (nfix id) (len mark))
               (equal (len new-mark) (len mark))))
    :hints(("Goal" :in-theory (enable (:i aignet-copy-dfs-rec))
            :induct (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)
            :expand ((aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))))

  (defun-sk dfs-copy-onto-invar (aignet mark copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal 1 (get-bit id mark)))
                     (equal (lit-eval (nth-lit id copy) invals regvals aignet2)
                            (id-eval id
                                     (input-copy-values 0 invals regvals aignet copy aignet2)
                                     (reg-copy-values 0 invals regvals aignet copy aignet2)
                                     aignet))))
    :rewrite :direct)

  (in-theory (disable dfs-copy-onto-invar))

  (local (in-theory (enable (:i aignet-copy-dfs-rec))))

  (local (defthm make-lit-equal-0
           (equal (equal (make-lit var neg) 0)
                  (and (nat-equiv var 0)
                       (not (equal neg 1))))
           :hints(("Goal" :in-theory (enable satlink::equal-of-make-lit)))))

  (defthm dfs-copy-onto-invar-holds-of-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy
                    strash gatesimp aignet2)))
               (dfs-copy-onto-invar aignet mark copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2))
            (and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:computed-hint-replacement
                     ((let ((witness (acl2::find-call-lst
                                 'dfs-copy-onto-invar-witness
                                 clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((mv-nth '0 ,witness) . id2)
                              ((mv-nth '1 ,witness) . invals)
                              ((mv-nth '2 ,witness) . regvals))))))
                     :expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t)))
            ;; (and stable-under-simplificationp
            ;;      (let ((witness (acl2::find-call-lst
            ;;                      'dfs-copy-onto-invar-witness
            ;;                      clause)))
            ;;       `(:clause-processor
            ;;         (acl2::simple-generalize-cp
            ;;          clause '(((mv-nth '0 ,witness) . id2)
            ;;                   ((mv-nth '1 ,witness) . invals)
            ;;                   ((mv-nth '2 ,witness) . regvals))))))
            (and stable-under-simplificationp
                 '(:in-theory (enable eval-and-of-lits
                                      lit-negate-cond)
                   :expand ((:free (in-vals reg-vals)
                             (id-eval id in-vals reg-vals aignet)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable lit-eval)))
            (and stable-under-simplificationp
                 (member-equal '(NOT (EQUAL (stype$inline (car (lookup-id id aignet))) ':gate))
                               clause)
                 (let ((term '(b* ((fanin (gate-id->fanin0 id aignet)))
                                (aignet-copy-dfs-rec
                                 (lit-id fanin) aignet mark copy
                                 strash gatesimp aignet2))))
                   `(:use ((:instance dfs-copy-onto-invar-necc
                            (id (lit-id (gate-id->fanin0 id aignet)))
                            (mark (mv-nth 0 ,term))
                            (copy (mv-nth 1 ,term))
                            (aignet2 (mv-nth 3 ,term))))
                     :in-theory (e/d* (lit-negate-cond lit-eval acl2::arith-equiv-forwarding)
                                     (dfs-copy-onto-invar-necc)))))
            (and stable-under-simplificationp
                 (member-equal '(not (EQUAL (ID-EVAL ID2
                                                     (INPUT-COPY-VALUES '0
                                                                        INVALS REGVALS AIGNET COPY AIGNET2)
                                                     (REG-COPY-VALUES '0
                                                                      INVALS REGVALS AIGNET COPY AIGNET2)
                                                     AIGNET)
                                            '1))
                               clause)
                 '(:expand ((:free (invals regvals) (id-eval id2 invals regvals aignet)))))))
    

  (defthm lit-eval-of-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (b* (((mv ?mark copy ?strash aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy
                    strash gatesimp aignet2)))
               (equal (lit-eval (nth-lit id copy) invals regvals aignet2)
                      (id-eval id (input-copy-values 0 invals regvals aignet copy aignet2)
                               (reg-copy-values 0 invals regvals aignet copy aignet2)
                               aignet))))
    :hints (("goal" :use dfs-copy-onto-invar-holds-of-aignet-copy-dfs-rec
             :in-theory (disable dfs-copy-onto-invar-holds-of-aignet-copy-dfs-rec)))))


(define count-gates-mark-rec ((id natp)
                              (mark)
                              (aignet))
  :guard (and (<= id (max-fanin aignet))
              (< (max-fanin aignet) (bits-length mark)))
  :returns (mv (num-subnodes natp :rule-classes :type-prescription)
               new-mark)
  :measure (nfix id)
  :verify-guards nil
  (b* (((when (eql 1 (get-bit id mark)))
        (mv 0 mark))
       (mark (set-bit id 1 mark))
       (slot0 (id->slot id 0 aignet))
       (type (snode->type slot0)))
    (aignet-case type
      :in (mv 0 mark)
      :gate (b* (((mv subs0 mark) (count-gates-mark-rec (lit-id (snode->fanin slot0)) mark aignet))
                 ((mv subs1 mark) (count-gates-mark-rec (lit-id (gate-id->fanin1 id aignet)) mark aignet)))
              (mv (+ 1 subs0 subs1) mark))
      :const (mv 0 mark)
      :out (count-gates-mark-rec (lit-id (snode->fanin slot0)) mark aignet)))
  ///
  (local (in-theory (disable (:d count-gates-mark-rec) nth update-nth)))

  (local (defthm len-update-nth-when-less
           (implies (< (nfix n) (len x))
                    (equal (len (update-nth n val x)) (len x)))))

  (defret len-mark-of-count-gates-mark-rec
    (implies (and (<= (nfix id) (max-fanin aignet))
                  (< (max-fanin aignet) (len mark)))
             (equal (len new-mark) (len mark)))
    :hints (("goal" :induct <call>
             :expand ((:free () <call>)))))

  (Verify-guards count-gates-mark-rec :hints(("goal" :in-theory(enable aignet-idp)))))

(define count-gates-mark ((id natp) aignet)
  :guard (<= id (max-fanin aignet))
  :returns (num-subnodes natp :rule-classes :type-prescription)
  (b* (((acl2::local-stobjs mark)
        (mv ans mark))
       (mark (resize-bits (+ 1 (max-fanin aignet)) mark)))
    (count-gates-mark-rec id mark aignet)))
       
(define aignet-get-ipasir-ctrex-invals ((n natp)
                                        (invals)
                                        (sat-lits)
                                        (aignet)
                                        (ipasir))
  :guard (and (sat-lits-wfp sat-lits aignet)
              (<= n (num-ins aignet))
              (<= (num-ins aignet) (bits-length invals))
              (non-exec (equal (ipasir::ipasir$a->status ipasir) :sat)))
  :returns (new-invals)
  :measure (nfix (- (num-ins aignet) (nfix n)))
  :verify-guards nil
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (eql (num-ins aignet) n)))
        invals)
       (id (innum->id n aignet))
       (sat-lit (aignet-id->sat-lit id sat-lits))
       ((when (eql 0 sat-lit))
        (aignet-get-ipasir-ctrex-invals (1+ (lnfix n)) invals sat-lits aignet ipasir))
       (val (ipasir::ipasir-val ipasir sat-lit))
       ((unless val)
        (aignet-get-ipasir-ctrex-invals (1+ (lnfix n)) invals sat-lits aignet ipasir))
       (invals (set-bit n val invals)))
    (aignet-get-ipasir-ctrex-invals (1+ (lnfix n)) invals sat-lits aignet ipasir))
  ///
  (defret invals-length-of-aignet-get-ipasir-ctrex-invals
    (implies (<= (num-ins aignet) (len invals))
             (equal (len new-invals) (len invals))))
  (verify-guards aignet-get-ipasir-ctrex-invals))


(define aignet-get-ipasir-ctrex-regvals ((n natp)
                                         (regvals)
                                         (sat-lits)
                                         (aignet)
                                         (ipasir))
  :guard (and (sat-lits-wfp sat-lits aignet)
              (<= n (num-regs aignet))
              (<= (num-regs aignet) (bits-length regvals))
              (non-exec (equal (ipasir::ipasir$a->status ipasir) :sat)))
  :returns (new-regvals)
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :verify-guards nil
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql (num-regs aignet) n)))
        regvals)
       (id (regnum->id n aignet))
       (sat-lit (aignet-id->sat-lit id sat-lits))
       ((when (eql 0 sat-lit))
        (aignet-get-ipasir-ctrex-regvals (1+ (lnfix n)) regvals sat-lits aignet ipasir))
       (val (ipasir::ipasir-val ipasir sat-lit))
       ((unless val)
        (aignet-get-ipasir-ctrex-regvals (1+ (lnfix n)) regvals sat-lits aignet ipasir))
       (regvals (set-bit n val regvals)))
    (aignet-get-ipasir-ctrex-regvals (1+ (lnfix n)) regvals sat-lits aignet ipasir))
  ///
  (defret regvals-length-of-aignet-get-ipasir-ctrex-regvals
    (implies (<= (num-regs aignet) (len regvals))
             (equal (len new-regvals) (len regvals))))
  (verify-guards aignet-get-ipasir-ctrex-regvals))


(define aignet-lit-ipasir-sat-check-aux ((x litp)
                                         sat-lits ipasir
                                         aignet state)
  ;; Returns ipasir ready to solve
  :guard (and (fanin-litp x aignet)
              (non-exec (and (equal sat-lits (create-sat-lits))
                             (equal ipasir (create-ipasir)))))
  :returns (mv new-ipasir
               new-sat-lits
               new-state)
  (b* (((acl2::local-stobjs aignet-refcounts)
        (mv aignet-refcounts ipasir sat-lits state))
       (sat-lits (mbe :logic (non-exec (create-sat-lits)) :exec sat-lits))
       (ipasir (mbe :logic (non-exec (create-ipasir)) :exec ipasir))
       ((mv ipasir state) (ipasir::ipasir-init ipasir state))
       (sat-lits (resize-aignet->sat (ash (+ 1 (max-fanin aignet)) -1) sat-lits)) 
       (aignet-refcounts (resize-u32 (+ 1 (max-fanin aignet)) aignet-refcounts))
       (aignet-refcounts (aignet-count-refs aignet-refcounts aignet))
       ((mv sat-lits ipasir) (aignet-lit->ipasir (lit-fix x) t aignet-refcounts sat-lits aignet ipasir))
       (sat-lit (aignet-lit->sat-lit x sat-lits))
       (ipasir (ipasir::ipasir-assume ipasir sat-lit)))
    (mv aignet-refcounts ipasir sat-lits state))
  ///
  (defret ipasir-status-of-aignet-lit-ipasir-sat-check-aux
    (equal (ipasir::ipasir$a->status new-ipasir) :input))

  (defret ipasir-new-clause-of-aignet-lit-ipasir-sat-check-aux
    (equal (ipasir::ipasir$a->new-clause new-ipasir) nil))

  ;; (defret cnf-for-aignet-of-aignet-lit-ipasir-sat-check-aux
  ;;   (implies (aignet-litp x aignet)
  ;;            (cnf-for-aignet aignet (ipasir::ipasir$a->formula new-ipasir) new-sat-lits)))

  (defret sat-lits-wfp-of-aignet-lit-ipasir-sat-check-aux
    (implies (aignet-litp x aignet)
             (sat-lits-wfp new-sat-lits aignet)))

  (defthm normalize-inputs-of-aignet-lit-ipasir-sat-check-aux
    (implies (syntaxp (not (and (equal sat-lits ''nil)
                                (equal ipasir ''nil))))
             (equal (aignet-lit-ipasir-sat-check-aux x sat-lits ipasir aignet state)
                    (aignet-lit-ipasir-sat-check-aux x nil nil aignet state))))

  (local (defthm sat-lits-wfp-implies-sat-varp-of-lookup-aignet-id-bind
           (implies (and (bind-free '((aignet . aignet)))
                         (sat-lits-wfp sat-lits aignet)
                         (aignet-id-has-sat-var n sat-lits))
                    (sat-varp (satlink::lit->var (aignet-id->sat-lit n sat-lits))
                              sat-lits))))

  (local (defthm sat-lits-wfp-implies-lookup-aignet-id-bind
           (implies (and (bind-free '((aignet . aignet)) (aignet))
                         (sat-lits-wfp sat-lits aignet)
                         (bind-free
                          (match-equiv-or-refinement
                           'satlink::var-equiv 'id '(satlink::lit->var (aignet-id->sat-lit n sat-lits))
                           mfc state)
                          (n))
                         (satlink::var-equiv id (satlink::lit->var (aignet-id->sat-lit n sat-lits)))
                         (aignet-id-has-sat-var n sat-lits))
                    (equal (sat-var->aignet-lit id sat-lits)
                           (mk-lit
                            n (satlink::lit->neg (aignet-id->sat-lit n sat-lits)))))
           :hints (("goal" :by sat-lits-wfp-implies-lookup-aignet-id))))

  (defret aignet-lit-ipasir-sat-check-aux-not-unsat-when-sat
    (implies (and (equal (lit-eval x some-invals some-regvals aignet) 1)
                  (aignet-litp x aignet))
             (b* (((mv status &) (ipasir::ipasir-solve$a new-ipasir)))
               (not (equal status :unsat))))
    :hints (("goal" :use ((:instance ipasir::ipasir-solve$a-unsat-implies-unsat
                           (env$ (aignet->cnf-vals some-invals some-regvals nil new-sat-lits aignet))
                           (formula (ipasir::ipasir$a->formula new-ipasir))
                           (solver new-ipasir)))
             :expand ((aignet-eval-conjunction nil some-invals some-regvals aignet))
             :in-theory (disable ipasir::ipasir-solve$a-unsat-implies-unsat)))))
               

(acl2::defstobj-clone inmasks bitarr :prefix "INMASKS-")
(acl2::defstobj-clone regmasks bitarr :prefix "REGMASKS-")

(define aignet-vals-sat-care-masks-rec ((id natp)
                                        inmasks regmasks
                                        invals regvals
                                        (vals)
                                        (mark)
                                        aignet
                                        state)
  :guard (and (id-existsp id aignet)
              (non-exec (equal vals (aignet-record-vals nil invals regvals aignet)))
              (not (Equal (id->type id aignet) (out-type)))
              (<= (num-ins aignet) (bits-length inmasks))
              (<= (num-regs aignet) (bits-length regmasks))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (< id (bits-length vals))
              (< id (bits-length mark)))
  :verify-guards nil
  :returns (mv new-inmasks new-regmasks new-mark new-state)
  (b* (((when (eql 1 (get-bit id mark)))
        (mv inmasks regmasks mark state))
       (mark (set-bit id 1 mark)))
    (aignet-case (id->type id aignet)
      :in (if (eql 1 (io-id->regp id aignet))
              (b* ((regmasks (set-bit (io-id->ionum id aignet) 1 regmasks)))
                (mv inmasks regmasks mark state))
            (b* ((inmasks (set-bit (io-id->ionum id aignet) 1 inmasks)))
              (mv inmasks regmasks mark state)))
      :out (mv inmasks regmasks mark state)
      :const (mv inmasks regmasks mark state)
      :gate (b* ((val (mbe :logic (id-eval id invals regvals aignet)
                                 :exec (get-bit id vals)))
                       (f0 (gate-id->fanin0 id aignet))
                       (f1 (gate-id->fanin1 id aignet))
                       ((when (eql val 1))
                        ;; both needed
                        (b* (((mv inmasks regmasks mark state)
                              (aignet-vals-sat-care-masks-rec
                               (lit-id f0) inmasks regmasks invals regvals vals mark aignet state)))
                          (aignet-vals-sat-care-masks-rec
                           (lit-id f1) inmasks regmasks invals regvals vals mark aignet state)))
                       ((when (eql (mbe :logic (lit-eval f0 invals regvals aignet)
                                        :exec (aignet-eval-lit f0 vals)) 1))
                        ;; f1 only needed
                        (aignet-vals-sat-care-masks-rec
                         (lit-id f1) inmasks regmasks invals regvals vals mark aignet state))
                       ((when (eql (mbe :logic (lit-eval f1 invals regvals aignet)
                                        :exec (aignet-eval-lit f1 vals))
                                   1))
                        ;; f0 only needed
                        (aignet-vals-sat-care-masks-rec
                         (lit-id f0) inmasks regmasks invals regvals vals mark aignet state))
                       ;; either one will do, check if one is already marked
                       ((when (or (eql 1 (get-bit (lit-id f0) mark))
                                  (eql 1 (get-bit (lit-id f1) mark))))
                        (mv inmasks regmasks mark state))
                       ((mv coinflip state) (random$ 2 state)))
                    (if (eql 1 coinflip)
                        (aignet-vals-sat-care-masks-rec
                         (lit-id f1) inmasks regmasks invals regvals vals mark aignet state)
                      (aignet-vals-sat-care-masks-rec
                       (lit-id f0) inmasks regmasks invals regvals vals mark aignet state)))))
  ///
  (local (in-theory (disable (:d aignet-vals-sat-care-masks-rec))))

  (defthm aignet-vals-sat-care-masks-normalize-input
    (implies (syntaxp (not (equal vals ''nil)))
             (equal (aignet-vals-sat-care-masks-rec
                     id inmasks regmasks invals regvals vals mark aignet state)
                    (aignet-vals-sat-care-masks-rec
                     id inmasks regmasks invals regvals nil mark aignet state)))
    :hints ((acl2::just-induct-and-expand
             (aignet-vals-sat-care-masks-rec
                     id inmasks regmasks invals regvals vals mark aignet state)
             :expand-others ((:free (vals)
                              (aignet-vals-sat-care-masks-rec
                     id inmasks regmasks invals regvals vals mark aignet state))))
            (and stable-under-simplificationp
                 '(:do-not-induct t))))

  (defret aignet-vals-sat-care-masks-preserve-marks
    (implies (equal (nth n mark) 1)
             (equal (nth n new-mark) 1))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-vals-sat-care-masks-preserve-inmasks
    (implies (equal (nth n inmasks) 1)
             (equal (nth n new-inmasks) 1))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-vals-sat-care-masks-preserve-regmasks
    (implies (equal (nth n regmasks) 1)
             (equal (nth n new-regmasks) 1))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret inmasks-length-of-aignet-vals-sat-care-masks
    (implies (<= (num-ins aignet) (len inmasks))
             (equal (len new-inmasks) (len inmasks)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret regmasks-length-of-aignet-vals-sat-care-masks
    (implies (<= (num-regs aignet) (len regmasks))
             (equal (len new-regmasks) (len regmasks)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret mark-length-of-aignet-vals-sat-care-masks
    (implies (< (nfix id) (len mark))
             (equal (len new-mark) (len mark)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (local (defthm lit-id-of-fanin-mark-lemma
           (implies (< (nfix id) (len mark))
                    (< (lit-id (fanin ftype (lookup-id id aignet))) (len mark)))
           :hints (("goal" :cases ((<= (nfix id) (node-count aignet)))))))

  (verify-guards aignet-vals-sat-care-masks-rec
    :hints(("Goal" :in-theory (enable lit-eval))))

  (defun-nx aignet-vals-sat-care-masks-mark-ok (node mark invals regvals aignet)
    (implies (and (equal (nth node mark) 1)
                  (equal (stype (car (lookup-id node aignet))) :gate))
             (and (implies (equal (id-eval node invals regvals aignet) 1)
                           (and (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)
                                (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))
                  (implies (and (equal (id-eval node invals regvals aignet) 0)
                                (not (and (equal (lit-eval (fanin :gate0 (lookup-id node aignet))
                                                           invals regvals aignet)
                                                 0)
                                          (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1))))
                           (and (equal (lit-eval (fanin :gate1 (lookup-id node aignet))
                                                 invals regvals aignet)
                                       0)
                                (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1))))))

  (defun-sk aignet-vals-sat-care-masks-mark-invar (id mark invals regvals aignet)
    (forall node
            (implies (<= (nfix node) (nfix id))
                     (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet)))
    :rewrite :direct)

  (in-theory (disable aignet-vals-sat-care-masks-mark-invar))

  (defthmd aignet-vals-sat-care-masks-mark-invar-rw
    (implies (and (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
                  (<= (nfix node) (nfix id))
                  (equal (nth node mark) 1)
                  (equal (stype (car (lookup-id node aignet))) :gate))
             (and (implies (equal (id-eval node invals regvals aignet) 1)
                           (and (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)
                                (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))
                  (implies (and (equal (id-eval node invals regvals aignet) 0)
                                (equal (lit-eval (fanin :gate0 (lookup-id node aignet))
                                                 invals regvals aignet)
                                       1))
                           (and (equal (lit-eval (fanin :gate1 (lookup-id node aignet))
                                                 invals regvals aignet)
                                       0)
                                (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))
                  
                  (implies (and (equal (id-eval node invals regvals aignet) 0)
                                (not (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)))
                           (and (equal (lit-eval (fanin :gate1 (lookup-id node aignet))
                                                 invals regvals aignet)
                                       0)
                                (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))

                  (implies (and (equal (id-eval node invals regvals aignet) 0)
                                (equal (lit-eval (fanin :gate1 (lookup-id node aignet))
                                                 invals regvals aignet)
                                       1))
                           (and (equal (lit-eval (fanin :gate0 (lookup-id node aignet))
                                                 invals regvals aignet)
                                       0)
                                (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)))
                  
                  (implies (and (equal (id-eval node invals regvals aignet) 0)
                                (not (equal (nth (lit-id (fanin :gate1 (lookup-id node aignet))) mark) 1)))
                           (and (equal (lit-eval (fanin :gate0 (lookup-id node aignet))
                                                 invals regvals aignet)
                                       0)
                                (equal (nth (lit-id (fanin :gate0 (lookup-id node aignet))) mark) 1)))))
    :hints (("goal" :use aignet-vals-sat-care-masks-mark-invar-necc
             :in-theory (disable aignet-vals-sat-care-masks-mark-invar-necc))))
             


  (defthm aignet-vals-sat-care-masks-mark-invar-when-lesser-id
    (implies (and (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
                  (<= (nfix id2) (nfix id)))
             (aignet-vals-sat-care-masks-mark-invar id2 mark invals regvals aignet))
    :hints (("goal" :expand ((aignet-vals-sat-care-masks-mark-invar id2 mark invals regvals aignet))
             :in-theory (enable aignet-vals-sat-care-masks-mark-ok
                                aignet-vals-sat-care-masks-mark-invar-rw))))

  (defthm aignet-vals-sat-care-masks-mark-invar-of-mark-greater-id
    (implies (and (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
                  (< (nfix id) (nfix id2)))
             (aignet-vals-sat-care-masks-mark-invar id (update-nth id2 1 mark) invals regvals aignet))
    :hints (("goal" :expand ((aignet-vals-sat-care-masks-mark-invar id (update-nth id2 1 mark) invals regvals aignet))
             :in-theory (enable aignet-vals-sat-care-masks-mark-ok
                                aignet-vals-sat-care-masks-mark-invar-rw))))

  (defret aignet-vals-sat-care-masks-preserves-marks-above-id
    (implies (< (nfix id) (nfix node))
             (equal (nth node new-mark)
                    (nth node mark)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-vals-sat-care-masks-marks-id
    (equal (nth id new-mark) 1)
    :hints (("goal" :expand ((:free (vals) <call>)))))

  ;; (local (defretd aignet-vals-sat-care-masks-preserves-marks-above-id-split
  ;;          (implies (case-split (< (nfix id) (nfix node)))
  ;;                   (equal (nth node new-mark)
  ;;                          (if (equal (nth node mark) 1) 1 (nth node mark) )))
  ;;          :hints ((acl2::just-induct-and-expand <call>))))

  ;; (local (defretd aignet-vals-sat-care-masks-preserve-marks-split
  ;;          (implies (case-split (equal (nth n mark) 1))
  ;;                   (equal (nth n new-mark) 1))
  ;;          :hints ((acl2::just-induct-and-expand <call>))))

  (local (defthm id-eval-of-gate-fanins-when-false
           (implies (And (equal (id-eval id invals regvals aignet) 0)
                         (equal (stype (car (lookup-id id aignet))) :gate))
                    (and (implies (equal (lit-eval (fanin :gate0 (lookup-id id aignet))
                                                   invals regvals aignet)
                                         1)
                                  (equal (lit-eval (fanin :gate1 (lookup-id id aignet))
                                                   invals regvals aignet)
                                         0))
                         (implies (equal (lit-eval (fanin :gate1 (lookup-id id aignet))
                                                   invals regvals aignet)
                                         1)
                                  (equal (lit-eval (fanin :gate0 (lookup-id id aignet))
                                                   invals regvals aignet)
                                         0))))
           :hints (("goal" :expand ((id-eval id invals regvals aignet))
                    :in-theory (enable eval-and-of-lits)))))

  (local (defthm id-eval-of-gate-fanins-when-true
           (implies (and (equal (id-eval id invals regvals aignet) 1)
                         (equal (stype (car (lookup-id id aignet))) :gate))
                    (and (equal (lit-eval (fanin :gate0 (lookup-id id aignet))
                                          invals regvals aignet)
                                1)
                         (equal (lit-eval (fanin :gate1 (lookup-id id aignet))
                                          invals regvals aignet)
                                1)))
           :hints (("goal" :expand ((id-eval id invals regvals aignet))
                    :in-theory (enable eval-and-of-lits)))))

  (local (in-theory (disable aignet-vals-sat-care-masks-mark-ok
                             lookup-id-out-of-bounds)))

  (defthm aignet-vals-sat-care-masks-mark-ok-of-update-mark
    (implies (and (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet)
                  (not (equal (nfix id) (nfix node))))
             (aignet-vals-sat-care-masks-mark-ok node (update-nth id 1 mark) invals regvals aignet))
    :hints(("Goal" :in-theory (enable aignet-vals-sat-care-masks-mark-ok))))
  
  ;; (defthm aignet-vals-sat-care-masks-mark-ok-of-update-non-gate
  ;;   (implies (and (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet)
  ;;                 (not (equal (stype (car (lookup-id id aignet))) :gate)))
  ;;            (aignet-vals-sat-care-masks-mark-ok node (update-nth id 1 mark) invals regvals aignet))
  ;;   :hints(("Goal" :in-theory (enable aignet-vals-sat-care-masks-mark-ok))))

  ;; (defthm aignet-vals-sat-care-masks-mark-ok-of-non-marked
  ;;   (implies (not (equal (nth node mark) 1))
  ;;            (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet))
  ;;   :hints(("Goal" :in-theory (enable aignet-vals-sat-care-masks-mark-ok))))

  ;; To prove this we need to show that the invariant still holds afterward of
  ;; an arbitrary witness node NODE.

  ;; - If node is <= than the ID of the recursive call(s), then it is fully
  ;; covered by the inductive invariant.
  ;; - If the node's mark was already set, then the original hyp implies
  ;; sufficient conditions about its fanins.
  ;; - Otherwise, node is ID and we ensure that its fanins are set correctly.

  ;; (defret aignet-vals-sat-care-masks-mark-invar-of-marked-node-preserved
  ;;   (implies (and (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet)
  ;;                 (equal (nth node mark) 1))
  ;;            (aignet-vals-sat-care-masks-mark-ok node new-mark invals regvals aignet))
  ;;   :hints ((acl2::just-induct-and-expand <call>)
  ;;           (and stable-under-simplificationp
  ;;                '(:cases ((equal (nfix node) (nfix id)))
  ;;                  :in-theory (enable* acl2::arith-equiv-forwarding)))))

  ;; (local (defthm not-gate-by-ctype
  ;;          (implies (not (equal (ctype (stype x)) :gate))
  ;;                   (not (equal (stype x) :gate)))
  ;;          :hints(("Goal" :in-theory (enable ctype)))))

  (defret aignet-vals-sat-care-masks-mark-ok-preserved
    (implies (aignet-vals-sat-care-masks-mark-ok node mark invals regvals aignet)
             (aignet-vals-sat-care-masks-mark-ok node new-mark invals regvals aignet))
    :hints ((acl2::just-induct-and-expand <call>)
            (and stable-under-simplificationp
                 '(:cases ((equal (nfix node) (nfix id)))
                   :in-theory (enable* acl2::arith-equiv-forwarding)))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))
  
  (defret aignet-vals-sat-care-masks-mark-invar-preserved
    (implies (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
             (aignet-vals-sat-care-masks-mark-invar id new-mark invals regvals aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(Car (last clause)))))))

  ;; When the invariant holds, marked nodes depend only on marked inputs
  (defun-sk aignet-marked-inputs-are-masked (mark inmasks aignet)
    (forall n
            (implies (and (< (nfix n) (num-ins aignet))
                          (equal 1 (nth (node-count (lookup-stype n :pi aignet)) mark)))
                     (equal (nth n inmasks) 1)))
    :rewrite :direct)
  
  (in-theory (disable aignet-marked-inputs-are-masked
                      aignet-marked-inputs-are-masked-necc))
  (local (in-theory (enable aignet-marked-inputs-are-masked-necc)))

  (defthm aignet-marked-inputs-are-masked-of-update-non-input
    (implies (and (aignet-marked-inputs-are-masked mark inmasks aignet)
                  (not (equal (stype (car (lookup-id id aignet))) :pi)))
             (aignet-marked-inputs-are-masked (update-nth id 1 mark) inmasks aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret aignet-vals-sat-care-masks-preserves-marked-inputs-masked
    (implies (aignet-marked-inputs-are-masked mark inmasks aignet)
             (aignet-marked-inputs-are-masked new-mark new-inmasks aignet))
    :hints ((acl2::just-induct-and-expand <call>)
            (and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:computed-hint-replacement
                     ((let ((witness (acl2::find-call-lst
                                 'aignet-marked-inputs-are-masked-witness
                                 clause)))
                        `(:clause-processor
                          (acl2::simple-generalize-cp
                           clause '((,witness . n))))))
                     :expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t)))))

  (defun-sk aignet-marked-regs-are-masked (mark regmasks aignet)
    (forall n
            (implies (and (< (nfix n) (num-regs aignet))
                          (equal 1 (nth (node-count (lookup-stype n :reg aignet)) mark)))
                     (equal (nth n regmasks) 1)))
    :rewrite :direct)
  
  (in-theory (disable aignet-marked-regs-are-masked
                      aignet-marked-regs-are-masked-necc))
  (local (in-theory (enable aignet-marked-regs-are-masked-necc)))

  (defthm aignet-marked-regs-are-masked-of-update-non-input
    (implies (and (aignet-marked-regs-are-masked mark regmasks aignet)
                  (not (equal (stype (car (lookup-id id aignet))) :reg)))
             (aignet-marked-regs-are-masked (update-nth id 1 mark) regmasks aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret aignet-vals-sat-care-masks-preserves-marked-regs-masked
    (implies (aignet-marked-regs-are-masked mark regmasks aignet)
             (aignet-marked-regs-are-masked new-mark new-regmasks aignet))
    :hints ((acl2::just-induct-and-expand <call>)
            (and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:computed-hint-replacement
                     ((let ((witness (acl2::find-call-lst
                                 'aignet-marked-regs-are-masked-witness
                                 clause)))
                        `(:clause-processor
                          (acl2::simple-generalize-cp
                           clause '((,witness . n))))))
                     :expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t)))))


  (defun-sk vals-equiv-under-masks (masks invals1 invals2)
    (forall n
            (implies (equal (nth n masks) 1)
                     (equal (nth n invals1) (nth n invals2))))
    :rewrite :direct)

  (in-theory (disable vals-equiv-under-masks))

  (defthmd aignet-vals-sat-care-masks-rec-invariants-imply-counterexample-holds-under-masks
    (implies (and (aignet-vals-sat-care-masks-mark-invar max-id mark invals regvals aignet)
                  (aignet-marked-inputs-are-masked mark inmasks aignet)
                  (aignet-marked-regs-are-masked mark regmasks aignet)
                  (vals-equiv-under-masks inmasks invals invals1)
                  (vals-equiv-under-masks regmasks regvals regvals1)
                  (equal (nth id mark) 1)
                  (not (equal (id->type id aignet) (out-type)))
                  (<= (nfix id) (nfix max-id)))
             (equal (id-eval id invals regvals aignet)
                    (id-eval id invals1 regvals1 aignet)))
    :hints (("goal" :induct (id-eval-ind id aignet))
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-vals-sat-care-masks-mark-invar-rw
                          (id max-id) (node id)))
                   :in-theory (disable aignet-vals-sat-care-masks-mark-invar-rw)
                   :expand ((:free (invals regvals)
                             (id-eval id invals regvals aignet))
                            (:free (lit0 lit1 invals regvals ) (eval-and-of-lits lit0 lit1 invals regvals aignet))
                            (:free (lit invals regvals) (lit-eval lit invals regvals aignet)))))))

  (defretd aignet-vals-sat-care-masks-rec-counterexample-under-masks
    (implies (and (vals-equiv-under-masks new-inmasks invals invals1)
                  (vals-equiv-under-masks new-regmasks regvals regvals1)
                  (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
                  (aignet-marked-inputs-are-masked mark inmasks aignet)
                  (aignet-marked-regs-are-masked mark regmasks aignet)
                  (not (equal (id->type id aignet) (out-type))))
             (equal (id-eval id invals1 regvals1 aignet)
                    (id-eval id invals regvals aignet)))
    :hints (("goal" :use ((:instance aignet-vals-sat-care-masks-rec-invariants-imply-counterexample-holds-under-masks
                           (id id) (max-id id)
                           (inmasks new-inmasks)
                           (regmasks new-regmasks)
                           (mark new-mark))))))

  (defretd aignet-vals-sat-care-masks-rec-counterexample-under-masks-lit-eval
    (implies (and (vals-equiv-under-masks new-inmasks invals invals1)
                  (vals-equiv-under-masks new-regmasks regvals regvals1)
                  (aignet-vals-sat-care-masks-mark-invar id mark invals regvals aignet)
                  (aignet-marked-inputs-are-masked mark inmasks aignet)
                  (aignet-marked-regs-are-masked mark regmasks aignet)
                  (not (equal (id->type id aignet) (out-type)))
                  (equal (lit-id x) (nfix id)))
             (equal (lit-eval x invals1 regvals1 aignet)
                    (lit-eval x invals regvals aignet)))
    :hints (("goal" :use ((:instance aignet-vals-sat-care-masks-rec-invariants-imply-counterexample-holds-under-masks
                           (id id) (max-id id)
                           (inmasks new-inmasks)
                           (regmasks new-regmasks)
                           (mark new-mark)))
             :expand ((:free (invals regvals)
                       (lit-eval x invals regvals aignet)))))))

       
                                                  


(define aignet-lit-ipasir-sat-check ((x litp)
                                     invals regvals   ;; satisfying assign
                                     vals ;; record evaluation
                                     aignet
                                     state)
  :guard (fanin-litp x aignet)
  :returns (mv (status (or (equal status :failed)
                           (equal status :unsat)
                           (equal status :sat))
                       :rule-classes ((:forward-chaining :trigger-terms (status))))
               (sat-invals (equal (len sat-invals) (num-ins aignet)))
               (sat-regvals (equal (len sat-regvals) (num-regs aignet)))
               (eval-vals (implies (equal status :sat)
                                   (equal eval-vals (aignet-record-vals vals sat-invals sat-regvals aignet))))
               new-state)
  :Guard-debug t
  (b* (((acl2::local-stobjs ipasir sat-lits)
        (mv ipasir sat-lits status invals regvals vals state))
       ((mv ipasir sat-lits state)
        (aignet-lit-ipasir-sat-check-aux x sat-lits ipasir aignet state))
       ((mv status ipasir) (ipasir::ipasir-solve ipasir))
       (invals (resize-bits (num-ins aignet) invals))
       (regvals (resize-bits (num-regs aignet) regvals))
       ((unless (eq status :sat))
        (b* ((ipasir (ipasir-release ipasir)))
          (mv ipasir sat-lits status invals regvals vals state)))
       (invals (aignet-get-ipasir-ctrex-invals 0 invals sat-lits aignet ipasir))
       (regvals (aignet-get-ipasir-ctrex-regvals 0 regvals sat-lits aignet ipasir))
       (ipasir (ipasir-release ipasir))
       (vals (aignet-record-vals vals invals regvals aignet))
       ((unless (eql (aignet-eval-lit x vals) 1))
        (raise "Supposed satisfying assignment didn't work!")
        (mv ipasir sat-lits :failed invals regvals vals state)))
    (mv ipasir sat-lits :sat invals regvals vals state))
  ///
  (defret satisfying-assign-of-aignet-lit-ipasir-sat-check
    (implies (and (equal status :sat)
                  (aignet-litp x aignet))
             (equal (lit-eval x sat-invals sat-regvals aignet) 1))
    :hints (("goal" :expand ((:free (invals regvals) (lit-eval x invals regvals aignet))))))

  (defret aignet-lit-ipasir-sat-check-not-unsat-when-sat
    (implies (and (equal (lit-eval x some-invals some-regvals aignet) 1)
                  (aignet-litp x aignet))
             (not (equal status :unsat)))))


(define aignet-lit-ipasir-sat-minimize ((x litp)
                                        invals regvals   ;; satisfying assign
                                        inmasks regmasks ;; minimized masks
                                        aignet
                                        state)
  :guard (fanin-litp x aignet)
  :returns (mv (status (or (equal status :failed)
                           (equal status :unsat)
                           (equal status :sat))
                       :rule-classes ((:forward-chaining :trigger-terms (status))))
               (sat-invals (equal (len sat-invals) (num-ins aignet)))
               (sat-regvals (equal (len sat-regvals) (num-regs aignet)))
               (sat-inmasks (equal (len sat-inmasks) (num-ins aignet)))
               (sat-regmasks (equal (len sat-regmasks) (num-regs aignet)))
               new-state)
  :Guard-debug t
  (b* (((acl2::local-stobjs vals mark)
        (mv vals mark status invals regvals inmasks regmasks state))
       ((mv status invals regvals vals state)
        (aignet-lit-ipasir-sat-check x invals regvals vals aignet state))
       (inmasks (resize-bits 0 inmasks))
       (inmasks (resize-bits (num-ins aignet) inmasks))
       (regmasks (resize-bits 0 regmasks))
       (regmasks (resize-bits (num-regs aignet) regmasks))
       ((unless (eql status :sat))
        (mv vals mark status invals regvals inmasks regmasks state))
       (mark (resize-bits (+ 1 (lit-id x)) mark))
       ((mv inmasks regmasks mark state)
        (aignet-vals-sat-care-masks-rec (lit-id x) inmasks regmasks invals regvals vals mark aignet state)))
    (mv vals mark :sat invals regvals inmasks regmasks state))
  ///
  (local (defthm aignet-vals-sat-care-masks-mark-invar-of-empty
           (aignet-vals-sat-care-masks-mark-invar id (resize-list nil n 0) invals regvals aignet)
           :hints(("Goal" :in-theory (enable aignet-vals-sat-care-masks-mark-invar
                                             aignet-vals-sat-care-masks-mark-ok)))))

  (local (defthm aignet-marked-inputs-are-masked-of-empty
           (aignet-marked-inputs-are-masked (resize-list nil n 0) invals aignet)
           :hints(("Goal" :in-theory (enable aignet-marked-inputs-are-masked)))))

  (local (defthm aignet-marked-regs-are-masked-of-empty
           (aignet-marked-regs-are-masked (resize-list nil n 0) regvals aignet)
           :hints(("Goal" :in-theory (enable aignet-marked-regs-are-masked)))))

  (defret satisfying-assign-of-aignet-lit-ipasir-sat-minimize
    (implies (and (equal status :sat)
                  (aignet-litp x aignet)
                  (vals-equiv-under-masks sat-inmasks sat-invals invals1)
                  (vals-equiv-under-masks sat-regmasks sat-regvals regvals1))
             (equal (lit-eval x invals1 regvals1 aignet) 1))
    :hints (("goal" 
             :in-theory (enable aignet-vals-sat-care-masks-rec-counterexample-under-masks-lit-eval))))

  (defret satisfying-assign-of-aignet-lit-ipasir-sat-minimize-basic
    (implies (and (equal status :sat)
                  (aignet-litp x aignet))
             (equal (lit-eval x sat-invals sat-regvals aignet) 1)))

  (defret aignet-lit-ipasir-sat-minimize-not-unsat-when-sat
    (implies (and (equal (lit-eval x some-invals some-regvals aignet) 1)
                  (aignet-litp x aignet))
             (not (equal status :unsat)))))



(define observability-fixed-inputs ((n natp)
                                    (invals) (inmasks)
                                    (hyp-lit litp)
                                    (aignet)
                                    (copy)
                                    (gatesimp natp)
                                    (strash)
                                    (aignet2))
  :guard (and (<= (nfix n) (num-ins aignet))
              (fanin-litp hyp-lit aignet2)
              (aignet-copies-in-bounds copy aignet2)
              (<= (num-ins aignet) (num-ins aignet2))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-ins aignet) (bits-length inmasks))
              (< (max-fanin aignet) (lits-length copy)))
  :measure (nfix (- (num-ins aignet) (nfix n)))
  :returns (mv new-copy new-strash new-aignet2)
  :prepwork ((local (defthm aignet-litp-of-bit
                      (implies (bitp b)
                               (aignet-litp b aignet))
                      :hints(("Goal" :in-theory (enable aignet-litp bitp)))))
             (local (defthm aignet-litp-of-input-lit
                      (implies (equal (stype (car (lookup-id id aignet))) :pi)
                               (aignet-litp (make-lit id neg) aignet))
                      :hints(("Goal" :in-theory (enable aignet-litp))))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable aignet-litp))))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (eql (num-ins aignet) n)))
        (mv copy strash aignet2))
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
    (implies (< (max-fanin aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints(("Goal" :in-theory (enable update-nth-lit))))

  (defret aignet-extension-p-of-observability-fixed-inputs
    (aignet-extension-p new-aignet2 aignet2))

  (local (defret input-copy-preserved-of-observability-fixed-inputs
           (implies (< (nfix innum) (nfix n))
                    (equal (nth-lit (node-count (lookup-stype innum :pi aignet)) new-copy)
                           (nth-lit (node-count (lookup-stype innum :pi aignet)) copy)))))


  (defret stypes-preserved-of-observability-fixed-inputs
    (implies (not (equal (stype-fix stype) :gate))
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
             (equal (lit-eval (nth-lit (node-count (lookup-stype innum :pi aignet)) new-copy)
                              some-invals some-regvals new-aignet2)
                    (lit-eval (nth-lit (node-count (lookup-stype innum :pi aignet)) copy)
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
                                            (update-nth-lit (node-count (lookup-stype m :pi aignet)) val copy)
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
                                 (gatesimp natp)
                                 (strash)
                                 (aignet2))
  :guard (and (<= (nfix n) (num-regs aignet))
              (fanin-litp hyp-lit aignet2)
              (<= (num-regs aignet) (num-regs aignet2))
              (<= (num-regs aignet) (bits-length regvals))
              (<= (num-regs aignet) (bits-length regmasks))
                  (aignet-copies-in-bounds copy aignet2)
              (< (max-fanin aignet) (lits-length copy)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :returns (mv new-copy new-strash new-aignet2)
  :prepwork ((local (defthm aignet-litp-of-bit
                      (implies (bitp b)
                               (aignet-litp b aignet))
                      :hints(("Goal" :in-theory (enable aignet-litp bitp)))))
             (local (defthm aignet-litp-of-reg-lit
                      (implies (equal (stype (car (lookup-id id aignet))) :reg)
                               (aignet-litp (make-lit id neg) aignet))
                      :hints(("Goal" :in-theory (enable aignet-litp))))))
  ;; :guard-hints ((and stable-under-simplificationp
  ;;                    '(:in-theory (enable aignet-litp))))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql (num-regs aignet) n)))
        (mv copy strash aignet2))
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
    (implies (< (max-fanin aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints(("Goal" :in-theory (enable update-nth-lit))))

  (defret aignet-extension-p-of-observability-fixed-regs
    (aignet-extension-p new-aignet2 aignet2))

  (local (defret reg-copy-preserved-of-observability-fixed-regs
           (implies (< (nfix regnum) (nfix n))
                    (equal (nth-lit (node-count (lookup-stype regnum :reg aignet)) new-copy)
                           (nth-lit (node-count (lookup-stype regnum :reg aignet)) copy)))))

  (defret stypes-preserved-of-observability-fixed-regs
    (implies (not (equal (stype-fix stype) :gate))
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
             (equal (lit-eval (nth-lit (node-count (lookup-stype regnum :reg aignet)) new-copy)
                              some-invals some-regvals new-aignet2)
                    (lit-eval (nth-lit (node-count (lookup-stype regnum :reg aignet)) copy)
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
                                            (update-nth-lit (node-count (lookup-stype m :reg aignet)) val copy)
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
              (< (max-fanin aignet) (lits-length copy))
              (<= (num-ins aignet) (num-ins aignet2))
              (<= (num-regs aignet) (num-regs aignet2))
              (aignet-copies-in-bounds copy aignet2))
  
  (b* (((acl2::local-stobjs invals regvals inmasks regmasks)
        (mv invals regvals inmasks regmasks status copy strash aignet2 state))
       ((mv status invals regvals inmasks regmasks state)
        (aignet-lit-ipasir-sat-minimize lit invals regvals inmasks regmasks aignet2 state))
       ((unless (eql status :sat))
        ;; BOZO for unsat, map to constants or something?
        (mv invals regvals inmasks regmasks status copy strash aignet2 state))
       ((mv copy strash aignet2)
        (observability-fixed-inputs 0 invals inmasks lit aignet copy 9 strash aignet2))
       ((mv copy strash aignet2)
        (observability-fixed-regs 0 regvals regmasks lit aignet copy 9 strash aignet2)))
    (mv invals regvals inmasks regmasks status copy strash aignet2 state))
  ///
  
  (defret copies-in-bounds-of-observability-fix-input-copies
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-litp lit aignet2)
                  (<= (num-ins aignet) (num-ins aignet2))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret copy-length-of-observability-fix-input-copies
    (implies (< (max-fanin aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints(("Goal" :in-theory (enable update-nth-lit))))

  (defret aignet-extension-p-of-observability-fix-input-copies
    (aignet-extension-p new-aignet2 aignet2))

  (defret stypes-preserved-of-observability-fix-input-copies
    (implies (not (equal (stype-fix stype) :gate))
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
             (equal (lit-eval (nth-lit (node-count (lookup-stype innum :pi aignet)) new-copy)
                              some-invals some-regvals new-aignet2)
                    (lit-eval (nth-lit (node-count (lookup-stype innum :pi aignet)) copy)
                              some-invals some-regvals aignet2))))

  (defret reg-copy-of-observability-fix-input-copies
    (implies (and (< (nfix regnum) (num-regs aignet))
                  (aignet-litp lit aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (<= (num-regs aignet) (num-regs aignet2))
                  (<= (num-ins aignet) (num-ins aignet2))
                  (equal 1 (lit-eval lit some-invals some-regvals aignet2)))
             (equal (lit-eval (nth-lit (node-count (lookup-stype regnum :reg aignet)) new-copy)
                              some-invals some-regvals new-aignet2)
                    (lit-eval (nth-lit (node-count (lookup-stype regnum :reg aignet)) copy)
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
             (not (equal status :unsat)))))
       


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
              :default 10))
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

(define observability-fix-hyp/concl ((hyp litp)
                                     (concl litp)
                                     (aignet)
                                     (copy)
                                     (strash)
                                     (aignet2)
                                     (state))
  
    :guard (and (< (max-fanin aignet) (lits-length copy))
                (aignet-copies-in-bounds copy aignet2)
                (fanin-litp hyp aignet)
                (fanin-litp concl aignet)
                (<= (num-ins aignet) (num-ins aignet2))
                (<= (num-regs aignet) (num-regs aignet2)))
    :returns (mv (conj litp)
                 new-copy new-strash new-aignet2 new-state)
    (b* (((mv copy strash aignet2)
          (b* (((acl2::local-stobjs mark)
                (mv mark copy strash aignet2))
               (mark (resize-bits (+ 1 (lit-id hyp)) mark))
               ;; (litarr (resize-lits (+ 1 (lit-id hyp)) litarr))
               ((mv mark copy strash aignet2)
                (aignet-copy-dfs-rec (lit-id hyp) aignet mark copy strash 9 aignet2)))
            (mv mark copy strash aignet2)))
         (hyp-copy (lit-copy hyp copy))
         ((mv ?status copy strash aignet2 state)
          (observability-fix-input-copies hyp-copy aignet copy strash aignet2 state))
         ((when (eq status :unsat))
          (mv 0 copy strash aignet2 state))
         ((mv copy strash aignet2)
          (b* (((acl2::local-stobjs mark)
                (mv mark copy strash aignet2))
               (mark (resize-bits (+ 1 (lit-id concl)) mark)))
            (aignet-copy-dfs-rec (lit-id concl) aignet mark copy strash 9 aignet2)))
         (concl-copy (lit-copy concl copy))
         ((mv and-lit strash aignet2) (aignet-hash-and hyp-copy concl-copy 9 strash aignet2)))
      (mv and-lit copy strash aignet2 state))
    ///
    
  (local (acl2::use-trivial-ancestors-check))

  (defret aignet-extension-of-observability-fix-hyp/concl
    (aignet-extension-p new-aignet2 aignet2)
    :hints ('(:expand (<call>))))

  (defret stype-counts-of-observability-fix-hyp/concl
      (implies (not (equal (stype-fix stype) :gate))
               (equal (stype-count stype new-aignet2)
                      (stype-count stype aignet2)))
      :hints ('(:expand (<call>))))


  (local (defthm aignet-idp-when-lte-max-fanin
           (implies (<= (nfix n) (max-fanin aignet))
                    (aignet-idp n aignet))
           :hints(("Goal" :in-theory (enable aignet-idp)))))

  (local (in-theory (disable bound-when-aignet-idp)))

  (local (defthm len-of-update-nth-lit
           (implies (< (nfix n) (len x))
                    (equal (len (update-nth-lit n val x))
                           (len x)))
           :hints(("Goal" :in-theory (enable update-nth-lit)))))

  (defret copy-size-of-observability-fix-hyp/concl
      (implies (and (< (max-fanin aignet) (len copy))
                    (<= (lit-id hyp) (max-fanin aignet))
                    (<= (lit-id concl) (max-fanin aignet)))
               (equal (len new-copy) (len copy)))
      :hints ('(:expand (<call>))))

  (defret copies-in-bounds-of-observability-fix-hyp/concl
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (<= (lit-id hyp) (max-fanin aignet))
                  (<= (lit-id concl) (max-fanin aignet))
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

  (local (defthm and-of-lit-evals-is-gate-eval
           (implies (equal (stype (car (lookup-id n aignet))) :gate)
                    (equal (b-and (lit-eval (fanin :gate0 (lookup-id n aignet))
                                            invals regvals aignet)
                                  (lit-eval (fanin :gate1 (lookup-id n aignet))
                                            invals regvals aignet))
                           (id-eval n invals regvals aignet)))
           :hints(("Goal" :expand ((id-eval n invals regvals aignet))
                   :in-theory (enable eval-and-of-lits)))))

  (local (defthm lit-eval-of-gate-fanin-when-1
           (implies (and (member f '(:gate0 :gate1))
                         (equal (id-eval n invals regvals aignet) 1)
                         (equal (stype (car (lookup-id n aignet))) :gate))
                    (equal (lit-eval (fanin f (lookup-id n aignet))
                                     invals regvals aignet)
                           1))
           :hints(("Goal" :expand ((id-eval n invals regvals aignet))
                   :in-theory (enable eval-and-of-lits)))))

  (local (defun search-matching-lit (pat clause alist)
           (b* (((when (atom clause)) nil)
                ((mv ok subst) (acl2::simple-one-way-unify pat (car clause) alist)))
             (if ok
                 subst
               (search-matching-lit pat (cdr clause) alist)))))


  (defret eval-of-observability-fix-hyp/concl
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  ;; (aignet-litp hyp aignet)
                  (aignet-litp concl aignet)
                  (<= (lit-id hyp) (max-fanin aignet))
                  (<= (lit-id concl) (max-fanin aignet))
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
            (and stable-under-simplificationp
                 '(:cases ((EQUAL 1
                                  (LIT-EVAL HYP
                                            (INPUT-COPY-VALUES 0 INVALS REGVALS AIGNET COPY AIGNET2)
                                            (REG-COPY-VALUES 0 INVALS REGVALS AIGNET COPY AIGNET2)
                                            AIGNET))))))))
                                     

(define observability-split-supergate-aux ((lits lit-listp)
                                           (config observability-config-p)
                                           (full-size natp)
                                           (aignet))
  :returns (mv (hyps lit-listp)
               (rest lit-listp))
  :guard (aignet-lit-listp lits aignet)
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
       (lits (lit-collect-supergate (make-lit id 0) t nil nil aignet-refcounts aignet))
       (- (cw "Observability supergate: ~x0 lits~%" (len lits)))
       ((mv hyps rest) (observability-split-supergate-aux lits config full-size aignet))
       (- (cw "Observability hyp lits: ~x0 concl: ~x1~%" (len hyps) (len rest))))
    (mv hyps rest aignet-refcounts))
  ///
  (local (defthm id-less-than-max-fanin-when-not-output
           (implies (and (aignet-idp id aignet)
                         (not (equal (id->type id aignet) (out-type))))
                    (and (<= (nfix id) (node-count (find-max-fanin aignet)))
                         (implies (natp id)
                                  (<= id (node-count (find-max-fanin aignet))))))
           :hints(("Goal" :in-theory (enable find-max-fanin lookup-id aignet-idp)))))

  (verify-guards observability-split-supergate
    :hints(("Goal" :in-theory (enable aignet-litp aignet-idp))))

  (defret aignet-lit-listp-of-observability-split-supergate
    (implies (and (aignet-idp id aignet)
                  (not (equal (ctype (stype (car (lookup-id id aignet)))) :output)))
             (and (aignet-lit-listp hyps aignet)
                  (aignet-lit-listp rest aignet)))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defret eval-of-observability-split-supergate
    (equal (b-and (aignet-eval-conjunction hyps invals regvals aignet)
                  (aignet-eval-conjunction rest invals regvals aignet))
           (id-eval id invals regvals aignet))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction lit-eval)))))


(define aignet-build-wide-and ((lits lit-listp)
                          (strash)
                          (aignet))
  :guard (aignet-lit-listp lits aignet)
  :returns (mv (and-lit litp) new-strash new-aignet)
  :verify-guards nil
  (b* (((when (atom lits)) (mv 1 strash aignet))
       ((mv rest strash aignet) (aignet-build-wide-and (cdr lits) strash aignet)))
    (aignet-hash-and (car lits) rest 9 strash aignet))
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
    (implies (not (equal (stype-fix stype) :gate))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet)))))


;; BOZO move
(define aignet-copy-set-ins ((n natp)
                             (aignet)
                             (copy)
                             (aignet2))
  ;; Sets the copy of each PI ID of aignet to the corresponding PI lit of aignet2, beginning at input number N.
  :guard (and (<= n (num-ins aignet))
              (<= (num-ins aignet) (num-ins aignet2))
              (< (max-fanin aignet) (lits-length copy)))
  :measure (nfix (- (num-ins aignet) (nfix n)))
  :returns (new-copy)
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (eql n (num-ins aignet))))
        copy)
       (copy (set-lit (innum->id n aignet)
                      (make-lit (innum->id n aignet2) 0)
                      copy)))
    (aignet-copy-set-ins (1+ (lnfix n)) aignet copy aignet2))
  ///
  (local (defthm len-of-update-nth-lit
           (implies (< (nfix n) (len x))
                    (equal (len (update-nth-lit n val x))
                           (len x)))
           :hints(("Goal" :in-theory (enable update-nth-lit)))))

  (defret len-of-aignet-copy-set-ins
    (implies (< (max-fanin aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (defret nth-lit-of-aignet-copy-set-ins
    (equal (nth-lit id new-copy)
           (if (and (eq (stype (car (lookup-id id aignet))) :pi)
                    (<= (nfix n) (stype-count :pi (cdr (lookup-id id aignet)))))
               (make-lit (node-count (lookup-stype (stype-count :pi (cdr (lookup-id id aignet))) :pi aignet2))
                         0)
             (nth-lit id copy))))

  (defret input-copy-values-of-aignet-copy-set-ins
    (implies (<= (num-ins aignet) (num-ins aignet2))
             (equal (input-copy-values n invals regvals aignet new-copy aignet2)
                    (bit-list-fix (take (- (num-ins aignet) (nfix n)) (nthcdr n invals)))))
    :hints(("Goal" :in-theory (enable input-copy-values))
           (and stable-under-simplificationp
                '(:expand ((:free (i) (lit-eval (make-lit i 0) invals regvals aignet2))
                           (:free (i) (id-eval i invals regvals aignet2)))))))

  (defret reg-copy-values-of-aignet-copy-set-ins
    (equal (reg-copy-values m invals regvals aignet new-copy aignet2)
           (reg-copy-values m invals regvals aignet copy aignet2)))

  (local (defthm aignet-litp-of-lookup-stype
           (aignet-litp (make-lit (node-count (lookup-stype n :pi aignet)) neg) aignet)
           :hints(("Goal" :in-theory (enable aignet-litp)
                   :cases ((< (nfix n) (num-ins aignet)))))))

  (defret aignet-copies-in-bounds-of-aignet-copy-set-ins
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy aignet2))))



(define aignet-copy-set-regs ((n natp)
                             (aignet)
                             (copy)
                             (aignet2))
  ;; Sets the copy of each PI ID of aignet to the corresponding PI lit of aignet2, beginning at input number N.
  :guard (and (<= n (num-regs aignet))
              (<= (num-regs aignet) (num-regs aignet2))
              (< (max-fanin aignet) (lits-length copy)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :returns (new-copy)
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql n (num-regs aignet))))
        copy)
       (copy (set-lit (regnum->id n aignet)
                      (make-lit (regnum->id n aignet2) 0)
                      copy)))
    (aignet-copy-set-regs (1+ (lnfix n)) aignet copy aignet2))
  ///
  (local (defthm len-of-update-nth-lit
           (implies (< (nfix n) (len x))
                    (equal (len (update-nth-lit n val x))
                           (len x)))
           :hints(("Goal" :in-theory (enable update-nth-lit)))))

  (defret len-of-aignet-copy-set-regs
    (implies (< (max-fanin aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (defret nth-lit-of-aignet-copy-set-regs
    (equal (nth-lit id new-copy)
           (if (and (eq (stype (car (lookup-id id aignet))) :reg)
                    (<= (nfix n) (stype-count :reg (cdr (lookup-id id aignet)))))
               (make-lit (node-count (lookup-stype (stype-count :reg (cdr (lookup-id id aignet))) :reg aignet2))
                         0)
             (nth-lit id copy))))

  (defret reg-copy-values-of-aignet-copy-set-regs
    (implies (<= (num-regs aignet) (num-regs aignet2))
             (equal (reg-copy-values n invals regvals aignet new-copy aignet2)
                    (bit-list-fix (take (- (num-regs aignet) (nfix n)) (nthcdr n regvals)))))
    :hints(("Goal" :in-theory (enable reg-copy-values))
           (and stable-under-simplificationp
                '(:expand ((:free (i) (lit-eval (make-lit i 0) invals regvals aignet2))
                           (:free (i) (id-eval i invals regvals aignet2)))))))

  (defret input-copy-values-of-aignet-copy-set-regs
    (equal (input-copy-values m invals regvals aignet new-copy aignet2)
           (input-copy-values m invals regvals aignet copy aignet2)))

  (local (defthm aignet-litp-of-lookup-stype
           (aignet-litp (make-lit (node-count (lookup-stype n :reg aignet)) neg) aignet)
           :hints(("Goal" :in-theory (enable aignet-litp)
                   :cases ((< (nfix n) (num-regs aignet)))))))

  (defret aignet-copies-in-bounds-of-aignet-copy-set-regs
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy aignet2))))

(local (defthm nth-of-bit-list-fix
         (bit-equiv (nth n (bit-list-fix x))
                    (nth n x))
         :hints(("Goal" :in-theory (enable nth)))))

(local (defthm id-eval-of-bit-list-fix-ins
         (equal (id-eval id (bit-list-fix ins) regs aignet)
                (id-eval id ins regs aignet))
         :hints (("goal" :induct (id-eval-ind id aignet)
                  :expand ((:free (ins) (id-eval id ins regs aignet))
                           (:free (lit ins) (lit-eval lit ins regs aignet))
                           (:free (lit1 lit2 ins) (eval-and-of-lits lit1 lit2 ins regs aignet)))))))

(local (defthm id-eval-of-bit-list-fix-regs
         (equal (id-eval id ins (bit-list-fix regs) aignet)
                (id-eval id ins regs aignet))
         :hints (("goal" :induct (id-eval-ind id aignet)
                  :expand ((:free (regs) (id-eval id ins regs aignet))
                           (:free (lit regs) (lit-eval lit ins regs aignet))
                           (:free (lit1 lit2 regs) (eval-and-of-lits lit1 lit2 ins regs aignet)))))))

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
             (local (defthm max-fanin-less-than-lit->var
                      (implies (aignet-litp lit aignet)
                               (<= (lit-id lit) (node-count (find-max-fanin aignet))))
                      :hints(("Goal" :in-theory (e/d (aignet-litp find-max-fanin node-count)
                                                     (FANIN-IF-CO-ID-LTE-MAX-FANIN))))))
             (local (defthm node-count-<-plus-1
                      (< (node-count x) (+ 1 (node-count x))))))
  (b* (((mv hyps rest) (observability-split-supergate (lit-id lit) config aignet))
       ((mv hyp concl aignet)
        (b* (((acl2::local-stobjs strash)
              (mv strash hyp concl aignet))
             ((mv hyp strash aignet) (aignet-build-wide-and hyps strash aignet))
             ((mv concl strash aignet) (aignet-build-wide-and rest strash aignet)))
          (mv strash hyp concl aignet)))
       (- (cw "Observability input: hyp size ~x0, concl ~x1~%"
              (count-gates-mark (lit-id hyp) aignet)
              (count-gates-mark (lit-id concl) aignet)))
       (copy (resize-lits (+ 1 (max-fanin aignet)) copy))
       (copy (aignet-copy-set-ins 0 aignet copy aignet2))
       (copy (aignet-copy-set-regs 0 aignet copy aignet2))
       ((mv conjunction copy strash aignet2 state)
        (observability-fix-hyp/concl hyp concl aignet copy strash aignet2 state)))
    (mv (lit-negate-cond conjunction (lit-neg lit))
        copy strash aignet2 aignet state))
  ///
  (defret aignet-extension-p-of-observability-fix-lit-1
    (aignet-extension-p new-aignet aignet))

  (defret stype-counts-of-observability-fix-lit-1
    (implies (not (equal (stype-fix stype) :gate))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (defret aignet-extension-p-of-observability-fix-lit-2
    (aignet-extension-p new-aignet2 aignet2))

  (defret stype-counts-of-observability-fix-lit-2
    (implies (not (equal (stype-fix stype) :gate))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

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
                    (lit-eval lit invals regvals aignet)))))
       



;; (defines observability-fix-rec
;;   :ruler-extenders :all
;;   (define observability-fix-rec ((n natp)
;;                                  (config observability-config-p)
;;                                  (aignet)
;;                                  (copy)
;;                                  (strash)
;;                                  (aignet2)
;;                                  (state))
;;     :guard (and (<= n (max-fanin aignet))
;;                 (< (max-fanin aignet) (lits-length copy))
;;                 (aignet-copies-in-bounds copy aignet2)
;;                 (not (equal (id->type n aignet) (out-type)))
;;                 (<= (num-ins aignet) (num-ins aignet2))
;;                 (<= (num-regs aignet) (num-regs aignet2)))
;;     :measure (acl2::two-nats-measure (nfix n) 0)
;;     :returns (mv new-copy new-strash new-aignet2 new-state)
;;     :verify-guards nil
;;     (b* (((acl2::local-stobjs mark)
;;           (mv mark copy strash aignet2 state))
;;          (mark (resize-bits (+ 1 (lnfix n)) mark)))
;;       (aignet-case (id->type n aignet)
;;         :const (b* (((mv mark copy strash aignet2)
;;                      (aignet-copy-dfs-rec n aignet mark copy strash 9 aignet2)))
;;                  (mv mark copy strash aignet2 state))
;;         :in (b* (((mv mark copy strash aignet2)
;;                   (aignet-copy-dfs-rec n aignet mark copy strash 9 aignet2)))
;;               (mv mark copy strash aignet2 state))
;;         :out (b* (((mv mark copy strash aignet2)
;;                    (aignet-copy-dfs-rec (lit-id (co-id->fanin n aignet)) aignet mark copy strash 9 aignet2)))
;;                (mv mark copy strash aignet2 state))
;;         :gate (b* ((f0 (gate-id->fanin0 n aignet))
;;                    (f1 (gate-id->fanin1 n aignet))
;;                    (f0size (count-gates-mark (lit-id f0) aignet))
;;                    (f1size (count-gates-mark (lit-id f1) aignet))
;;                    ((unless (observability-size-check f0size f1size config))
;;                     (cw "Observability: not splitting further (~x0, ~x1)~%" f0size f1size)
;;                     (b* (((mv mark copy strash aignet2)
;;                           (aignet-copy-dfs-rec n aignet mark copy strash 9 aignet2)))
;;                       (mv mark copy strash aignet2 state)))
;;                    (- (cw "Observability: hyp size ~x0, concl size ~x1~%" (min f0size f1size)
;;                           (max f0size f1size)))
;;                    ((mv lit1 lit2 copy strash aignet2 state)
;;                     (if (< f0size f1size)
;;                         (observability-fix-lits-rec f0 f1
;;                                                     config
;;                                                     aignet copy strash aignet2 state)
;;                       (observability-fix-lits-rec f1 f0
;;                                                   config
;;                                                   aignet copy strash aignet2 state)))
;;                    ((mv lit strash aignet2) (aignet-hash-and lit1 lit2 9 strash aignet2))
;;                    (copy (set-lit n lit copy)))
;;                 (mv mark copy strash aignet2 state)))))

;;   (define observability-fix-lits-rec ((assum litp)
;;                                       (large litp)
;;                                       (config observability-config-p)
;;                                       (aignet)
;;                                       (copy)
;;                                       (strash)
;;                                       (aignet2)
;;                                       (state))
;;     :guard (and (< (max-fanin aignet) (lits-length copy))
;;                 (aignet-copies-in-bounds copy aignet2)
;;                 (fanin-litp assum aignet)
;;                 (fanin-litp large aignet)
;;                 (<= (num-ins aignet) (num-ins aignet2))
;;                 (<= (num-regs aignet) (num-regs aignet2)))
;;     :measure (acl2::two-nats-measure (lit-id large) 1)
;;     :returns (mv (assum-copy litp)
;;                  (large-copy litp)
;;                  new-copy new-strash new-aignet2 state)
;;     (b* (((mv assum-copy copy strash aignet2 state)
;;           (b* (((acl2::local-stobjs mark)
;;                 (mv mark assum-copy copy strash aignet2 state))
;;                (mark (resize-bits (+ 1 (lit-id assum)) mark))
;;                ;; (litarr (resize-lits (+ 1 (lit-id assum)) litarr))
;;                ((mv mark copy strash aignet2)
;;                 (aignet-copy-dfs-rec (lit-id assum) aignet mark copy strash 9 aignet2))
;;                (assum-copy (lit-copy assum copy))
;;                ((mv ?status copy strash aignet2 state)
;;                 (observability-fix-input-copies assum-copy aignet copy strash aignet2 state)))
;;             (mv mark assum-copy copy strash aignet2 state)))
;;          ((mv copy strash aignet2 state)
;;           (observability-fix-rec (lit-id large) config aignet copy strash aignet2 state))
;;          (large-copy (lit-copy large copy)))
;;       (mv assum-copy large-copy copy strash aignet2 state)))
;;   ///

;;   (local (in-theory (disable (:d observability-fix-rec)
;;                              (:d observability-fix-lits-rec))))

;;   (local (acl2::use-trivial-ancestors-check))

;;   (std::defret-mutual aignet-extension-of-observability-fix-rec
;;     (defret aignet-extension-of-observability-fix-rec
;;       (aignet-extension-p new-aignet2 aignet2)
;;       :hints ('(:expand (<call>)))
;;       :fn observability-fix-rec)
;;     (defret aignet-extension-of-observability-fix-lits-rec
;;       (aignet-extension-p new-aignet2 aignet2)
;;       :hints ('(:expand (<call>)))
;;       :fn observability-fix-lits-rec))

;;   (std::defret-mutual stype-counts-of-observability-fix-rec
;;     (defret stype-counts-of-observability-fix-rec
;;       (implies (not (equal (stype-fix stype) :gate))
;;                (equal (stype-count stype new-aignet2)
;;                       (stype-count stype aignet2)))
;;       :hints ('(:expand (<call>)))
;;       :fn observability-fix-rec)
;;     (defret stype-counts-of-observability-fix-lits-rec
;;       (implies (not (equal (stype-fix stype) :gate))
;;                (equal (stype-count stype new-aignet2)
;;                       (stype-count stype aignet2)))
;;       :hints ('(:expand (<call>)))
;;       :fn observability-fix-lits-rec))


;;   (local (defthm aignet-idp-when-lte-max-fanin
;;            (implies (<= (nfix n) (max-fanin aignet))
;;                     (aignet-idp n aignet))
;;            :hints(("Goal" :in-theory (enable aignet-idp)))))

;;   (local (in-theory (disable bound-when-aignet-idp)))

;;   (local (defthm len-of-update-nth-lit
;;            (implies (< (nfix n) (len x))
;;                     (equal (len (update-nth-lit n val x))
;;                            (len x)))
;;            :hints(("Goal" :in-theory (enable update-nth-lit)))))

;;   (std::defret-mutual copy-size-of-observability-fix-rec
;;     (defret copy-size-of-observability-fix-rec
;;       (implies (and (< (max-fanin aignet) (len copy))
;;                     (<= (nfix n) (max-fanin aignet)))
;;                (equal (len new-copy) (len copy)))
;;       :hints ('(:expand (<call>)))
;;       :fn observability-fix-rec)
;;     (defret copy-size-of-observability-fix-lits-rec
;;       (implies (and (< (max-fanin aignet) (len copy))
;;                     (<= (lit-id assum) (max-fanin aignet))
;;                     (<= (lit-id large) (max-fanin aignet)))
;;                (equal (len new-copy) (len copy)))
;;       :hints ('(:expand (<call>)))
;;       :fn observability-fix-lits-rec))

;;   (std::defret-mutual copies-in-bounds-of-observability-fix-rec
;;     (defret copies-in-bounds-of-observability-fix-rec
;;       (implies (and (aignet-copies-in-bounds copy aignet2)
;;                     (<= (nfix n) (max-fanin aignet))
;;                     (<= (num-ins aignet) (num-ins aignet2))
;;                     (<= (num-regs aignet) (num-regs aignet2)))
;;                (aignet-copies-in-bounds new-copy new-aignet2))
;;       :hints ('(:expand (<call>)))
;;       :fn observability-fix-rec)
;;     (defret copies-in-bounds-of-observability-fix-lits-rec
;;       (implies (and (aignet-copies-in-bounds copy aignet2)
;;                     (<= (lit-id assum) (max-fanin aignet))
;;                     (<= (lit-id large) (max-fanin aignet))
;;                     (<= (num-ins aignet) (num-ins aignet2))
;;                     (<= (num-regs aignet) (num-regs aignet2)))
;;                (and (aignet-copies-in-bounds new-copy new-aignet2)
;;                     (aignet-litp assum-copy new-aignet2)
;;                     (aignet-litp large-copy new-aignet2)))
;;       :hints ('(:expand (<call>)))
;;       :fn observability-fix-lits-rec))


;;   (verify-guards observability-fix-rec
;;     :hints(("Goal" :in-theory (enable aignet-idp))))
  
;;   (local (defthm id-eval-of-input
;;            (implies (equal (ctype (stype (car (lookup-id n aignet)))) :input)
;;                     (equal (id-eval n invals regvals aignet)
;;                            (if (eql 1 (regp (stype (car (lookup-id n aignet)))))
;;                                (bfix (nth (stype-count :reg (cdr (lookup-id n aignet))) regvals))
;;                              (bfix (nth (stype-count :pi (cdr (lookup-id n aignet))) invals)))))
;;            :hints (("goal" :expand ((id-eval n invals regvals aignet))))))

;;   (defthm dfs-copy-onto-invar-of-empty-mark
;;     (dfs-copy-onto-invar aignet (resize-list nil n 0) copy aignet2)
;;     :hints(("Goal" :in-theory (enable dfs-copy-onto-invar))))

;;   (local (defthm b-xor-id-eval-equals-lit-eval
;;            (equal (b-xor (lit->neg x)
;;                          (id-eval (lit->var x) invals regvals aignet))
;;                   (lit-eval x invals regvals aignet))
;;            :hints(("Goal" :in-theory (enable lit-eval)))))

;;   (local (defthm and-of-lit-evals-is-gate-eval
;;            (implies (equal (stype (car (lookup-id n aignet))) :gate)
;;                     (equal (b-and (lit-eval (fanin :gate0 (lookup-id n aignet))
;;                                             invals regvals aignet)
;;                                   (lit-eval (fanin :gate1 (lookup-id n aignet))
;;                                             invals regvals aignet))
;;                            (id-eval n invals regvals aignet)))
;;            :hints(("Goal" :expand ((id-eval n invals regvals aignet))
;;                    :in-theory (enable eval-and-of-lits)))))

;;   (local (defthm lit-eval-of-gate-fanin-when-1
;;            (implies (and (member f '(:gate0 :gate1))
;;                          (equal (id-eval n invals regvals aignet) 1)
;;                          (equal (stype (car (lookup-id n aignet))) :gate))
;;                     (equal (lit-eval (fanin f (lookup-id n aignet))
;;                                      invals regvals aignet)
;;                            1))
;;            :hints(("Goal" :expand ((id-eval n invals regvals aignet))
;;                    :in-theory (enable eval-and-of-lits)))))

;;   (std::defret-mutual eval-of-observability-fix-rec
;;     (defret eval-of-observability-fix-rec
;;       (implies (and (aignet-copies-in-bounds copy aignet2)
;;                     (<= (nfix n) (max-fanin aignet))
;;                     (<= (num-ins aignet) (num-ins aignet2))
;;                     (<= (num-regs aignet) (num-regs aignet2))
;;                     (not (equal (ctype (stype (car (lookup-id n aignet )))) :output)))
;;                (equal (lit-eval (nth-lit n new-copy) invals regvals new-aignet2)
;;                       (id-eval n 
;;                                (input-copy-values 0 invals regvals aignet copy aignet2)
;;                                (reg-copy-values 0 invals regvals aignet copy aignet2)
;;                                aignet)))
;;       :hints ('(:expand (<call>) :do-not-induct t
;;                 :cases ((equal (stype (car (lookup-id n aignet))) :gate)
;;                         (equal (stype (car (lookup-id n aignet))) :const)
;;                         (equal (ctype (stype (car (lookup-id n aignet)))) :input))))
;;       :fn observability-fix-rec)
;;     (defret eval-of-observability-fix-lits-rec
;;       (implies (and (aignet-copies-in-bounds copy aignet2)
;;                     (aignet-litp large aignet)
;;                     (<= (lit-id assum) (max-fanin aignet))
;;                     (<= (lit-id large) (max-fanin aignet))
;;                     (<= (num-ins aignet) (num-ins aignet2))
;;                     (<= (num-regs aignet) (num-regs aignet2)))
;;                (and (equal (lit-eval assum-copy invals regvals new-aignet2)
;;                            (lit-eval assum
;;                                      (input-copy-values 0 invals regvals aignet copy aignet2)
;;                                      (reg-copy-values 0 invals regvals aignet copy aignet2)
;;                                      aignet))
;;                     (implies (equal 1 (lit-eval assum
;;                                                 (input-copy-values 0 invals regvals aignet copy aignet2)
;;                                                 (reg-copy-values 0 invals regvals aignet copy aignet2)
;;                                                 aignet))
;;                              (equal (lit-eval large-copy invals regvals new-aignet2)
;;                                     (lit-eval large
;;                                               (input-copy-values 0 invals regvals aignet copy aignet2)
;;                                               (reg-copy-values 0 invals regvals aignet copy aignet2)
;;                                               aignet)))))
;;       :hints ('(:expand (<call>) :do-not-induct t))
;;       :fn observability-fix-lits-rec))

;;   (fty::deffixequiv-mutual observability-fix-rec))

  




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
  (b* (((when (mbe :logic (zp (- (num-outs aignet) (nfix n)))
                   :exec (Eql (num-outs aignet) n)))
        (mv copy strash aignet2 aignet state))
       (fanin-lit (co-id->fanin (outnum->id n aignet) aignet))
       ((mv copy-lit copy strash aignet2 aignet state)
        (observability-fix-lit fanin-lit config aignet copy strash aignet2 state))
       (aignet2 (aignet-add-out copy-lit aignet2)))
    (observability-fix-outs (1+ (lnfix n)) config aignet copy strash aignet2 state))
  ///
  (defret aignet-extension-p-of-observability-fix-outs-2
    (aignet-extension-p new-aignet2 aignet2))

  (defret aignet-extension-p-of-observability-fix-outs-1
    (aignet-extension-p new-aignet aignet))

  (defret stype-counts-of-observability-fix-outs-2
    (implies (and (not (equal (stype-fix stype) :gate))
                  (not (equal (stype-fix stype) :po)))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret stype-counts-of-observability-fix-outs-1
    (implies (not (equal (stype-fix stype) :gate))
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
                '(:expand ((:free (a b) (lookup-stype m :po (cons a b)))))))))


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
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (Eql (num-regs aignet) n)))
        (mv copy strash aignet2 aignet state))
       (fanin-lit (reg-id->nxst-lit (regnum->id n aignet) aignet))
       ((mv copy-lit copy strash aignet2 aignet state)
        (observability-fix-lit fanin-lit config aignet copy strash aignet2 state))
       (aignet2 (aignet-set-nxst copy-lit (regnum->id n aignet2) aignet2)))
    (observability-fix-nxsts (1+ (lnfix n)) config aignet copy strash aignet2 state))
  ///
  (defret aignet-extension-p-of-observability-fix-nxsts-2
    (aignet-extension-p new-aignet2 aignet2))

  (defret stype-counts-of-observability-fix-nxsts-2
    (implies (and (not (equal (stype-fix stype) :gate))
                  (not (equal (stype-fix stype) :nxst)))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret aignet-extension-p-of-observability-fix-nxsts-1
    (aignet-extension-p new-aignet aignet))

  (defret stype-counts-of-observability-fix-nxsts-1
    (implies (not (equal (stype-fix stype) :gate))
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
           (implies (and (<= (nfix id) (node-count aignet2))
                         (<= (num-regs aignet) (num-regs aignet2))
                         (< (stype-count :reg (cdr (lookup-id id aignet2))) (nfix n)))
                    (equal (lookup-reg->nxst id new-aignet2)
                           (lookup-reg->nxst id aignet2)))
           :hints (("goal" :induct <call> :expand (<call>)
                    :in-theory (enable aignet-idp
                                       stype-count-of-cdr-lookup-stype-dumb))
                   (and stable-under-simplificationp
                        '(:expand ((:free (a b) (lookup-reg->nxst id (cons a b)))))))))

  (local (defthm reg-id->nxst-lit-of-lookup-stype
           (equal (reg-id->nxst-lit (node-count (lookup-stype n :reg aignet)) aignet)
                  (fanin-if-co (lookup-regnum->nxst n aignet)))
           :hints(("Goal" :in-theory (enable fanin-if-co reg-id->nxst-lit)))))

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
                                       acl2::arith-equiv-forwarding)
            :induct <call>
            :expand (<call>))
           (and stable-under-simplificationp
                '(:expand ((:free (a b) (lookup-regnum->nxst m (cons a b))))))
           (and stable-under-simplificationp
                '(:cases ((< (nfix m) (num-regs aignet2))))))))


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
                             (num-nodes aignet)
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
    :hints(("Goal" :in-theory (enable comb-equiv)))))
             


(define observability-fix ((aignet  "Input aignet")
                           (aignet2 "New aignet -- will be emptied")
                           (config observability-config-p)
                           (state))
  :guard-debug t
  :returns (mv new-aignet2 state)
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet2 aignet-tmp state))
       (aignet2 (aignet-raw-copy aignet aignet2))
       ((mv aignet-tmp aignet2 state) (observability-fix-core aignet2 aignet-tmp config state))
       (aignet2 (aignet-prune-comb aignet-tmp aignet2 9)))
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
                    (observability-fix aignet nil config state)))))


(define observability-fix! ((aignet  "Input aignet -- will be replaced with transformation result")
                            (config observability-config-p)
                            (state))
  :guard-debug t
  :returns (mv new-aignet state)
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet aignet-tmp state))
       ((mv aignet-tmp aignet state) (observability-fix-core aignet aignet-tmp config state))
       (aignet (aignet-prune-comb aignet-tmp aignet 9)))
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
    (comb-equiv new-aignet aignet)))


  
