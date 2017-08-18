

(in-package "AIGNET")


(include-book "centaur/aignet/copying" :dir :system)
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (in-theory (disable acl2::resize-list-when-atom resize-list)))

(defstobj-clone aignet-tmp aignet :suffix "TMP")

(define print-aignet-stats ((name stringp) aignet)
  (cw "~s0 network: Nodes: ~x6  Max fanin ~x7~%       PIs ~x1 regs ~x2 gates ~x3 nxsts ~x4 POs ~x5~%"
      (mbe :logic (acl2::str-fix name) :exec name)
      (num-ins aignet)
      (num-regs aignet)
      (num-gates aignet)
      (num-nxsts aignet)
      (num-outs aignet)
      (num-nodes aignet)
      (max-fanin aignet)))


(define init-copy-comb ((aignet)
                         (copy)
                         (aignet2))
  :returns (mv new-copy new-aignet2)
  :guard-debug t
  :prepwork ((local (defthm floor-natp
                      (implies (and (natp x) (natp y))
                               (natp (floor x y)))
                      :hints(("Goal" :in-theory (enable floor)))
                      :rule-classes :type-prescription)))
  (b* ((aignet2 (aignet-init
                 (num-outs aignet)
                 (num-regs aignet)
                 (num-ins aignet)
                 (+ 1
                    (num-outs aignet)
                    (* 2 (num-regs aignet))
                    (num-ins aignet)
                    (floor (num-gates aignet) 3)) ;; optimistic!
                 aignet2))
       (copy (resize-lits 0 copy))
       (copy (resize-lits (+ 1 (max-fanin aignet)) copy))
       ((mv copy aignet2) (aignet-copy-ins aignet copy aignet2)))
    (aignet-copy-regs aignet copy aignet2))
  ///
  
  (defret copy-length-of-init-copy-comb
    (equal (len new-copy) (+ 1 (max-fanin aignet))))

  ;; (defret aignet-copies-ok-of-init-copy-comb
  ;;   (aignet-copies-ok (+ 1 (node-count (find-max-fanin aignet))) new-copy new-aignet2))

  (local (defthm nth-lit-of-nil
           (equal (nth-lit n nil) 0)
           :hints(("Goal" :in-theory (enable nth-lit)))))

  (defret aignet-copies-in-bounds-of-balance-init-copy
    (aignet-copies-in-bounds new-copy new-aignet2)
    :hints (("goal" :in-theory (enable aignet-copies-in-bounds
                                       aignet-litp))
            (and stable-under-simplificationp
                 (let ((witness (acl2::find-call-lst
                                 'aignet-copies-in-bounds-witness
                                 clause)))
                   (and witness
                        `(:clause-processor
                          (acl2::simple-generalize-cp
                           clause '((,witness . some-node)))))))))

  (defret num-ins-of-init-copy-comb
    (equal (stype-count :pi new-aignet2)
           (stype-count :pi aignet)))

  (defret num-regs-of-init-copy-comb
    (equal (stype-count :reg new-aignet2)
           (stype-count :reg aignet)))

  (defret num-outs-of-init-copy-comb
    (equal (stype-count :po new-aignet2) 0))

  (defret num-nxsts-of-init-copy-comb
    (equal (stype-count :nxst new-aignet2) 0))

  (defthm normalize-inputs-of-init-copy-comb
    (implies (syntaxp (not (and (equal aignet2 ''nil)
                                (equal copy ''nil))))
             (equal (init-copy-comb aignet copy aignet2)
                    (init-copy-comb aignet nil nil)))))

(defsection output-fanins-comb-equiv
  (defun-sk output-fanins-comb-equiv (aignet copy aignet2)
    (forall (n invals regvals)
            (implies (< (nfix n) (num-outs aignet))
                     (equal (lit-eval (nth-lit (lit-id (fanin :co (lookup-stype n :po aignet))) copy)
                                      invals regvals aignet2)
                            (id-eval (lit-id (fanin :co (lookup-stype n :po aignet)))
                                     invals regvals aignet))))
    :rewrite :direct)
  (in-theory (disable output-fanins-comb-equiv)))

(defsection nxst-fanins-comb-equiv
  (defun-sk nxst-fanins-comb-equiv (aignet copy aignet2)
    (forall (n invals regvals)
            (implies (< (nfix n) (num-regs aignet))
                     (equal (lit-eval (nth-lit (lit-id (fanin-if-co (lookup-regnum->nxst n aignet))) copy)
                                      invals regvals aignet2)
                            (id-eval (lit-id (fanin-if-co (lookup-regnum->nxst n aignet)))
                                     invals regvals aignet))))
    :rewrite :direct)
  (in-theory (disable nxst-fanins-comb-equiv)))


(define finish-copy-comb ((aignet)
                           (copy)
                           (aignet2))
  :guard (and (< (max-fanin aignet) (lits-length copy))
              (aignet-copies-in-bounds copy aignet2)
              (<= (num-regs aignet) (num-regs aignet2)))
  :returns (new-aignet2)
  (b* ((aignet2 (aignet-copy-outs-from-fanins aignet copy aignet2)))
    (aignet-copy-nxsts-from-fanins aignet copy aignet2))
  ///
  (local (defthm not-nxst-or-po-by-ctype
           (implies (not (Equal (ctype stype) :output))
                    (and (not (equal (stype-fix stype) :nxst))
                         (not (equal (stype-fix stype) :po))))
           :hints(("Goal" :in-theory (enable ctype)))))

  (defret non-output-stype-count-of-finish-copy-comb
    (implies (not (equal (ctype stype) :output))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret num-outs-of-finish-copy-comb
    (equal (stype-count :po new-aignet2)
           (+ (stype-count :po aignet) (stype-count :po aignet2))))


  (defret outs-comb-equiv-of-finish-copy-comb
    (implies (and (output-fanins-comb-equiv aignet copy aignet2)
                  (equal (stype-count :po aignet2) 0)
                  (aignet-copies-in-bounds copy aignet2))
             (outs-comb-equiv new-aignet2 aignet))
    :hints(("Goal" :in-theory (e/d (outs-comb-equiv output-eval)
                                   (outs-comb-equiv-necc)))
           (and stable-under-simplificationp
                (let ((witness (acl2::find-call-lst
                                'outs-comb-equiv-witness
                                clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((mv-nth '0 ,witness) . n)
                              ((mv-nth '1 ,witness) . invals)
                              ((mv-nth '2 ,witness) . regvals))))))
           (and stable-under-simplificationp
                '(:cases ((< (nfix n) (num-outs aignet)))
                  :expand (;; (:free (suff aignet)
                           ;;  (id-eval (node-count suff) invals regvals aignet))
                           ;; (:free (suff aignet)
                           ;;  (id-eval (+ 1 (nfix n) (node-count suff)) invals regvals aignet))
                           (:free (x)
                            (lit-eval (fanin :co x)
                                      invals regvals aignet)))))))

  (local (acl2::use-trivial-ancestors-check))

  (defret nxsts-comb-equiv-of-finish-copy-comb
    (implies (and (nxst-fanins-comb-equiv aignet copy aignet2)
                  (equal (stype-count :nxst aignet2) 0)
                  (equal (stype-count :reg aignet) (stype-count :reg aignet2))
                  (aignet-copies-in-bounds copy aignet2))
             (nxsts-comb-equiv new-aignet2 aignet))
    :hints(("Goal" :in-theory (e/d (nxsts-comb-equiv nxst-eval)
                                   (nxsts-comb-equiv-necc)))
           (and stable-under-simplificationp
                (let ((witness (acl2::find-call-lst
                                'nxsts-comb-equiv-witness
                                clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((mv-nth '0 ,witness) . n)
                              ((mv-nth '1 ,witness) . invals)
                              ((mv-nth '2 ,witness) . regvals))))))
           (and stable-under-simplificationp
                '(:cases ((< (nfix n) (num-regs aignet)))
                  :expand (;; (:free (suff aignet)
                           ;;  (id-eval (node-count suff) invals regvals aignet))
                           ;; (:free (suff aignet)
                           ;;  (id-eval (+ 1 (nfix n) (node-count suff)) invals regvals aignet))
                           (:free (x)
                            (lit-eval (fanin-if-co x)
                                      invals regvals aignet)))))))

  (defret comb-equiv-of-finish-copy-comb
    (implies (and (output-fanins-comb-equiv aignet copy aignet2)
                  (nxst-fanins-comb-equiv aignet copy aignet2)
                  (equal (stype-count :po aignet2) 0)
                  (equal (stype-count :nxst aignet2) 0)
                  (equal (stype-count :reg aignet) (stype-count :reg aignet2))
                  (aignet-copies-in-bounds copy aignet2))
             (comb-equiv new-aignet2 aignet))
    :hints(("Goal" :in-theory (e/d (comb-equiv) (finish-copy-comb))))))




(define aignet-raw-copy-aux ((n natp) aignet aignet2)
  :guard (and (<= n (num-nodes aignet))
              (non-exec (equal aignet2 (lookup-id (+ -1 n) aignet))))
  ;; :measure (nfix (- (num-nodes aignet) (nfix n)))
  :guard-hints (("goal" :in-theory (e/d (aignet-idp fanin co-node->fanin regp) (aignet-nodes-ok))
                 :expand ((:free (n aignet aignet2) (aignet-raw-copy-aux n aignet aignet2)))
                 :cases ((equal 0 n))
                 :use ((:instance aignet-nodes-ok (aignet (lookup-id n aignet))))))
  :returns new-aignet2
  :enabled t
  :prepwork ((local (defthm lookup-id-of-num-nodes
                      (implies (equal n (node-count aignet))
                               (equal (lookup-id n aignet)
                                      (node-list-fix aignet)))
                      :hints(("Goal" :in-theory (enable lookup-id)))))
             (local (defthm lookup-id-of-n-minus-1
                      (implies (and (natp n)
                                    (<= n (node-count aignet)))
                               (equal (lookup-id (+ -1 n) aignet)
                                      (cdr (lookup-id n aignet))))
                      :hints(("Goal" :in-theory (enable lookup-id)
                              :induct (lookup-id n aignet)))))
             (local (defret aignet-litp-in-extension-of-cdr-of-fanin
                      (implies (aignet-extension-p new (cdr aignet))
                               (aignet-litp lit new))
                      :hints(("Goal" :in-theory (enable fanin)))
                      :fn fanin))
             (local (defthm stype-is-pi-implies-equal-pi
                      (implies (node-p node)
                               (equal (equal (stype node) :pi)
                                      (equal node '(:pi))))
                      :hints(("Goal" :in-theory (enable node-p stype)))))
             (local (defthm stype-is-reg-implies-equal-reg
                      (implies (node-p node)
                               (equal (equal (stype node) :reg)
                                      (equal node '(:reg))))
                      :hints(("Goal" :in-theory (enable node-p stype)))))
             (local (defthm equal-of-cons-by-components
                      (implies (and (consp c)
                                    (equal (car c) a)
                                    (equal (cdr c) b))
                               (equal (equal (cons a b) c) t)))))
  (mbe :logic (non-exec aignet)
       :exec
       (b* (((when (mbe :logic (zp (- (num-nodes aignet) (nfix n)))
                        :exec (eql n (num-nodes aignet))))
             aignet2)
            (slot0 (id->slot n 0 aignet))
            (slot1 (id->slot n 1 aignet))
            (type (snode->type slot0))
            (regp (snode->regp slot1))
            (aignet2 (aignet-seq-case type regp
                       :gate (aignet-add-gate (snode->fanin slot0)
                                              (snode->fanin slot1)
                                              aignet2)
                       :pi (aignet-add-in aignet2)
                       :reg (aignet-add-reg aignet2)
                       :po (aignet-add-out (snode->fanin slot0) aignet2)
                       :nxst (aignet-set-nxst (snode->fanin slot0)
                                              (snode->regid slot1)
                                              aignet2)
                       :const aignet2)))
         (aignet-raw-copy-aux (+ 1 (lnfix n)) aignet aignet2))))

(define aignet-raw-copy (aignet aignet2)
  :enabled t
  (mbe :logic (non-exec aignet)
       :exec (b* ((aignet2 (aignet-init (num-outs aignet)
                                        (num-regs aignet)
                                        (num-ins aignet)
                                        (num-nodes aignet)
                                        aignet2)))
               (aignet-raw-copy-aux 0 aignet aignet2))))


