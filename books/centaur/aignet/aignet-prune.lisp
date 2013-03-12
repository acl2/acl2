
(in-package "AIGNET")

(include-book "aignet-base")
(include-book "../misc/iter")
(local (include-book "bit-lemmas"))

(local (in-theory (disable nth update-nth
                           acl2::nth-with-large-index
                           SETS::SETS-ARE-TRUE-LISTS
                           sets::double-containment
                           len)))

(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (include-book "arithmetic/top-with-meta" :dir :system))


(defsection comb-equiv
  (defun-sk comb-equiv (aignet aignet2)
    (forall (n invals regvals)
            (and (equal (equal (nth *num-outs* aignet)
                               (nth *num-outs* aignet2))
                        t)
                 (equal (equal (nth *num-regs* aignet)
                               (nth *num-regs* aignet2))
                        t)
                 (implies (< (nfix n) (nth *num-outs* aignet))
                          (equal (equal (id-eval (nth-id n (nth *outsi* aignet))
                                                 invals regvals aignet)
                                        (id-eval (nth-id n (nth *outsi* aignet2))
                                                 invals regvals aignet2))
                                 t))
                 (implies (< (nfix n) (nth *num-regs* aignet))
                          (equal (equal (id-eval (nth-id n (nth *regsi* aignet))
                                                 invals regvals aignet)
                                        (id-eval (nth-id n (nth *regsi* aignet2))
                                                 invals regvals aignet2))
                                 t))))
    :rewrite :direct)

  (in-theory (disable comb-equiv comb-equiv-necc))

  (local (defthm refl
           (comb-equiv x x)
           :hints(("Goal" :in-theory (enable comb-equiv)))))

  (local
   (defthm symm
     (implies (comb-equiv aignet aignet2)
              (comb-equiv aignet2 aignet))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))
                    :use ((:instance comb-equiv-necc
                           (n (mv-nth 0 (comb-equiv-witness aignet2 aignet)))
                           (invals (mv-nth 1 (comb-equiv-witness aignet2 aignet)))
                           (regvals (mv-nth 2 (comb-equiv-witness aignet2
                                                                  aignet))))))))))

  (local
   (defthm trans-lemma
     (implies (and (comb-equiv aignet aignet2)
                   (comb-equiv aignet2 aignet3))
              (comb-equiv aignet aignet3))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))
                    :use ((:instance comb-equiv-necc
                           (n (mv-nth 0 (comb-equiv-witness aignet aignet3)))
                           (invals (mv-nth 1 (comb-equiv-witness aignet aignet3)))
                           (regvals (mv-nth 2 (comb-equiv-witness aignet aignet3))))
                          (:instance comb-equiv-necc
                           (aignet aignet2) (aignet2 aignet3)
                           (n (mv-nth 0 (comb-equiv-witness aignet aignet3)))
                           (invals (mv-nth 1 (comb-equiv-witness aignet aignet3)))
                           (regvals (mv-nth 2 (comb-equiv-witness aignet
                                                                  aignet3))))))))))

  (defequiv comb-equiv))


(defsection aignet-copy-dfs-rec

  (acl2::defstobj-clone aignet-mark bitarr :suffix "-MARK")

  (defund aignet-copy-dfs-rec (id aignet aignet-mark aignet-copy strash gatesimp aignet2)
    (declare (type (integer 0 *) id)
             (xargs :stobjs (aignet aignet-mark aignet-copy strash aignet2)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (aignet-idp id aignet)
                                (natp gatesimp)
                                (bitarr-sizedp aignet-mark aignet)
                                (litarr-sizedp aignet-copy aignet)
                                (aignet-copies-ok
                                 (num-nodes aignet) aignet-copy aignet2))
                    :hints(("Goal" :in-theory (enable gate-orderedp
                                                      co-orderedp)))
                    :guard-debug t
                    :verify-guards nil
                    :measure (id-val id)))
    (b* (((when (int= (get-id->bit id aignet-mark) 1))
          (mv aignet-mark aignet-copy strash aignet2))
         (type (id->type id aignet))
         ((when (int= type (out-type)))
          ;; copy the fanin of the output and set the output ID's copy to be
          ;; that of the fanin lit
          (b* (((unless (mbt (co-orderedp id aignet)))
                (b* ((aignet-copy (set-id->lit id 0 aignet-copy))
                     (aignet-mark (set-id->bit id 1 aignet-mark)))
                  (mv aignet-mark aignet-copy strash aignet2)))
               (f (co-id->fanin id aignet))
               ((mv aignet-mark aignet-copy strash aignet2)
                (aignet-copy-dfs-rec
                 (lit-id f) aignet aignet-mark aignet-copy strash gatesimp
                 aignet2))
               (f-copy (lit-copy f aignet-copy))
               (aignet-copy (set-id->lit id f-copy aignet-copy))
               (aignet-mark (set-id->bit id 1 aignet-mark)))
            (mv aignet-mark aignet-copy strash aignet2)))

         ((unless (int= type (gate-type)))
          (mv aignet-mark aignet-copy strash aignet2))
         ((unless (mbt (gate-orderedp id aignet)))
          (b* ((aignet-copy (set-id->lit id 0 aignet-copy))
               (aignet-mark (set-id->bit id 1 aignet-mark)))
            (mv aignet-mark aignet-copy strash aignet2)))

         ;; gate: recur on each fanin, then hash an AND of the two copies
         (f0 (gate-id->fanin0 id aignet))
         (f1 (gate-id->fanin1 id aignet))
         ((mv aignet-mark aignet-copy strash aignet2)
          (aignet-copy-dfs-rec
           (lit-id f0) aignet aignet-mark aignet-copy strash gatesimp aignet2))
         (f0-copy (lit-copy f0 aignet-copy))
         ((when (int= f0-copy (to-lit 0)))
          ;; first branch was 0 so exit early
          (b* ((aignet-copy (set-id->lit id 0 aignet-copy))
               (aignet-mark (set-id->bit id 1 aignet-mark)))
            (mv aignet-mark aignet-copy strash aignet2)))
         ((mv aignet-mark aignet-copy strash aignet2)
          (aignet-copy-dfs-rec
           (lit-id f1) aignet aignet-mark aignet-copy strash gatesimp aignet2))
         (f1-copy (lit-copy f1 aignet-copy))
         ((mv id-copy strash aignet2)
          (aignet-hash-and f0-copy f1-copy strash gatesimp aignet2))
         (aignet-copy (set-id->lit id id-copy aignet-copy))
         (aignet-mark (set-id->bit id 1 aignet-mark)))
      (mv aignet-mark aignet-copy strash aignet2)))

  (defthm litp-of-lit-negate-cond
    (litp (lit-negate-cond lit neg)))

  (local (in-theory (disable lit-negate-cond acl2::b-xor
                             aignet-copies-ok)))
  (local (in-theory (enable (:induction aignet-copy-dfs-rec))))

  (def-aignet-preservation-thms aignet-copy-dfs-rec :stobjname aignet2)

  (def-aignet2-frame aignet-copy-dfs-rec
        :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet aignet-mark aignet-copy strash
              gatesimp aignet2))
            '(:in-theory (enable* aignet-frame-thms)
              :do-not-induct t
              :do-not '(generalize))))

  (defcong id-equiv equal (gate-orderedp id aignet) 1
    :hints(("Goal" :in-theory (enable gate-orderedp))))

  (defcong id-equiv equal (co-orderedp id aignet) 1
    :hints(("Goal" :in-theory (enable co-orderedp))))

  (defcong id-equiv equal
    (aignet-copy-dfs-rec id aignet aignet-mark
                         aignet-copy strash gatesimp aignet2)
    1
    :hints (("goal" :induct
             (aignet-copy-dfs-rec id aignet aignet-mark
                                  aignet-copy strash gatesimp aignet2)
             :expand ((aignet-copy-dfs-rec id aignet aignet-mark
                                           aignet-copy strash gatesimp aignet2)
                      (aignet-copy-dfs-rec id-equiv aignet aignet-mark
                                           aignet-copy strash gatesimp aignet2)))))

  (defthm copies-sized-of-aignet-copy-dfs-rec
    (implies (litarr-sizedp aignet-copy aignet)
             (memo-tablep (mv-nth 1 (aignet-copy-dfs-rec
                                     id aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm mark-sized-of-aignet-copy-dfs-rec
    (implies (bitarr-sizedp aignet-mark aignet)
             (memo-tablep (mv-nth 0 (aignet-copy-dfs-rec
                                     id aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm id-in-bounds-when-memo-tablep-bind-free
    (implies (and (bind-free '((aignet . aignet)) (aignet))
                  (memo-tablep arr aignet)
                  (double-rewrite (aignet-idp n aignet)))
             (id-in-bounds n arr)))

  (defthm aignet-copies-ok-implies-special-bind-free
    (implies (and (bind-free '((aignet1 . aignet)) (aignet1))
                  (aignet-copies-ok (nth *num-nodes* aignet1) aignet-copy aignet)
                  (aignet-idp (to-id k) aignet1))
             (aignet-litp (nth-lit k aignet-copy) aignet)))

  (defthm aignet-copies-ok-of-aignet-copy-dfs-rec
    (implies (and (aignet-well-formedp aignet2)
                  (aignet-well-formedp aignet)
                  (aignet-idp id aignet)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2))
             (b* (((mv & aignet-copy & aignet2)
                   (aignet-copy-dfs-rec
                    id aignet aignet-mark aignet-copy
                    strash gatesimp aignet2)))
               (and (aignet-copies-ok (nth *num-nodes* aignet)
                                      aignet-copy aignet2)
                    (aignet-well-formedp aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (local (in-theory (disable acl2::aignetp)))
  (verify-guards aignet-copy-dfs-rec))

(local (defun trivial-worse-than-or-equal (term1 term2)
         (declare (xargs :guard t)
                  (ignorable term1 term2))
         nil))

(local (defattach acl2::worse-than-or-equal trivial-worse-than-or-equal))

(defsection aignet-copy-dfs-invar

  (defund-nx dfs-copiedp (id aignet aignet-mark)
    (implies (or (int= (id->type id aignet) (gate-type))
                 (int= (id->type id aignet) (out-type)))
             (int= (get-id->bit id aignet-mark) 1)))
  
  (local (in-theory (enable dfs-copiedp)))

  (defthm dfs-copiedp-when-get-id->bit
    (implies (int= (get-id->bit id aignet-mark) 1)
             (dfs-copiedp id aignet aignet-mark)))

  (defthm dfs-copiedp-when-in/const
    (implies (and (not (int= (id->type id aignet) (gate-type)))
                  (not (int= (id->type id aignet) (out-type))))
             (dfs-copiedp id aignet aignet-mark)))

  (defthm not-dfs-copiedp
    (implies (and (or (int= (id->type id aignet) (gate-type))
                      (int= (id->type id aignet) (out-type)))
                  (not (int= (get-id->bit id aignet-mark) 1)))
             (not (dfs-copiedp id aignet aignet-mark))))

  (defthm dfs-copiedp-of-update-diff
    (implies (not (equal (nfix n) (id-val w)))
             (equal (dfs-copiedp
                     w aignet
                     (update-nth n v aignet-marks))
                    (double-rewrite
                     (dfs-copiedp w aignet aignet-marks))))
    :hints(("Goal" :in-theory (enable dfs-copiedp))))

  (defcong id-equiv equal (dfs-copiedp id aignet aignet-marks) 1)
  (defcong nth-equiv equal (dfs-copiedp id aignet aignet-marks) 3)

  (local (in-theory (disable dfs-copiedp)))

  

  (defun-sk aignet-copy-dfs-invar (aignet aignet-mark aignet-copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (dfs-copiedp id aignet aignet-mark))
                     (equal (id-eval id invals regvals aignet)
                            (lit-eval (get-id->lit id aignet-copy)
                                      invals regvals aignet2))))
    :rewrite :direct)

  (in-theory (disable aignet-copy-dfs-invar))

  (local (in-theory (enable (:induction aignet-copy-dfs-rec))))

  (local (in-theory (disable acl2::b-xor lit-negate-cond)))

  (defthm aignet-copy-dfs-id-copiedp
    (dfs-copiedp id aignet
                 (mv-nth 0 (aignet-copy-dfs-rec
                            id aignet aignet-mark aignet-copy
                            strash gatesimp aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-rec-preserves-dfs-copiedp
    (implies (dfs-copiedp n aignet aignet-mark)
             (dfs-copiedp n aignet (mv-nth 0 (aignet-copy-dfs-rec
                                              id aignet aignet-mark aignet-copy
                                              strash gatesimp aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet aignet-mark aignet-copy
              strash gatesimp aignet2))
            (and stable-under-simplificationp
                 '(:in-theory (enable dfs-copiedp)))))

  (defthm aignet-copy-dfs-preserves-copy-when-marked
    (implies (dfs-copiedp id aignet aignet-mark)
             (equal (nth-lit id (mv-nth 1 (aignet-copy-dfs-rec
                                                        id aignet aignet-mark aignet-copy
                                                        strash gatesimp aignet2)))
                    (nth-lit id aignet-copy)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (local (defthm lit-eval-of-lit-negate-cond
           (equal (lit-eval (lit-negate-cond lit neg)
                            in-vals reg-vals aignet)
                  (acl2::b-xor (lit-eval lit in-vals reg-vals aignet) neg))
           :hints(("Goal" :in-theory (enable lit-negate-cond lit-eval)))))

  (defthm aignet-copy-dfs-invar-necc-rewrite
    (b* (((mv aignet-mark aignet-copy & aignet2)
          (aignet-copy-dfs-rec
           id aignet aignet-mark aignet-copy
           strash gatesimp aignet2)))
      (implies (and (aignet-copy-dfs-invar
                     aignet aignet-mark aignet-copy aignet2)
                    (aignet-idp id aignet))
               (equal (id-eval id in-vals reg-vals aignet)
                      (lit-eval
                       (get-id->lit id aignet-copy)
                       in-vals reg-vals aignet2))))
    :hints (("goal" :do-not-induct t)))

  (local (defthm equal-mk-lit-rw
           (equal (equal (mk-lit id neg) val)
                  (and (litp val)
                       (equal (id-fix id) (lit-id val))
                       (equal (bfix neg) (lit-neg val))))
           :hints(("Goal" :in-theory (disable mk-lit-identity)
                   :use ((:instance mk-lit-identity (lit val)))))))

  (defthm aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-rec
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-idp id aignet)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2))
             (b* (((mv aignet-mark aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-rec
                    id aignet aignet-mark aignet-copy
                    strash gatesimp aignet2)))
               (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet aignet-mark aignet-copy
              strash gatesimp aignet2))
            (and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t)))
            (and stable-under-simplificationp
                 '(:in-theory (enable lit-eval
                                      lit-negate-cond)
                   :expand ((:free (in-vals reg-vals)
                             (id-eval id in-vals reg-vals aignet)))))))

  (defthm lit-eval-in-aignet-copy-dfs-rec
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-idp id aignet)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy
                                         aignet2))
             (b* (((mv aignet-mark aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-rec
                    id aignet aignet-mark aignet-copy strash gatesimp aignet2)))
               (implies (and (aignet-idp id2 aignet)
                             (dfs-copiedp id2 aignet aignet-mark))
                        (equal (lit-eval (nth-lit (id-val id2) aignet-copy)
                                         invals regvals aignet2)
                               (id-eval id2 invals regvals aignet)))))
    :hints (("goal" :use aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-rec
             :in-theory (disable aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-rec)))))

(defsection aignet-copy-dfs-outs

  (local (in-theory (disable acl2::aignetp)))

  (defiteration aignet-copy-dfs-outs
    (aignet aignet-mark aignet-copy strash gatesimp aignet2)
    (declare (xargs :stobjs (aignet aignet-mark aignet-copy strash aignet2)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (natp gatesimp)
                                (bitarr-sizedp aignet-mark aignet)
                                (litarr-sizedp aignet-copy aignet)
                                (aignet-copies-ok
                                 (num-nodes aignet) aignet-copy aignet2))))
    (b* ((outid (outnum->id n aignet))
         ((mv aignet-mark aignet-copy strash aignet2)
          (aignet-copy-dfs-rec
           outid aignet aignet-mark aignet-copy strash gatesimp aignet2))
         (fanin (get-id->lit outid aignet-copy))
         (aignet2 (aignet-add-out fanin aignet2)))
      (mv aignet-mark aignet-copy strash aignet2))
    :returns (mv aignet-mark aignet-copy strash aignet2)
    :index n
    :last (num-outs aignet))

  (in-theory (disable aignet-copy-dfs-outs))
  (local (in-theory (enable aignet-copy-dfs-outs)))
  (in-theory (enable (:induction aignet-copy-dfs-outs-iter)))

  (def-aignet-preservation-thms aignet-copy-dfs-outs-iter :stobjname aignet2)
  (def-aignet-preservation-thms aignet-copy-dfs-outs :stobjname aignet2)

  (def-aignet2-frame aignet-copy-dfs-outs-iter
        :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet aignet-mark aignet-copy strash
              gatesimp aignet2))
            '(:in-theory (enable* aignet-frame-thms)
              :do-not-induct t
              :do-not '(generalize))))

  (def-aignet2-frame aignet-copy-dfs-outs)

  (defthm copies-sized-of-aignet-copy-dfs-outs-iter
    (implies (litarr-sizedp aignet-copy aignet)
             (memo-tablep (mv-nth 1 (aignet-copy-dfs-outs-iter
                                     n aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm copies-sized-of-aignet-copy-dfs-outs
    (implies (litarr-sizedp aignet-copy aignet)
             (memo-tablep (mv-nth 1 (aignet-copy-dfs-outs
                                     aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))
                          aignet)))

  (defthm mark-sized-of-aignet-copy-dfs-outs-iter
    (implies (bitarr-sizedp aignet-mark aignet)
             (memo-tablep (mv-nth 0 (aignet-copy-dfs-outs-iter
                                     n aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm mark-sized-of-aignet-copy-dfs-outs
    (implies (bitarr-sizedp aignet-mark aignet)
             (memo-tablep (mv-nth 0 (aignet-copy-dfs-outs
                                     aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))
                          aignet)))

  (defthm aignet-copies-ok-of-aignet-copy-dfs-outs-iter
    (implies (and (aignet-well-formedp aignet2)
                  (aignet-well-formedp aignet)
                  (aignet-copies-ok (nth *num-nodes* aignet) aignet-copy
                                    aignet2)
                  (<= (nfix n) (nth *num-outs* aignet)))
             (b* (((mv & aignet-copy & aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet aignet-mark aignet-copy
                    strash gatesimp aignet2)))
               (and (aignet-copies-ok (nth *num-nodes* aignet) aignet-copy aignet2)
                    (aignet-well-formedp aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm aignet-copies-ok-of-aignet-copy-dfs-outs
    (implies (and (aignet-well-formedp aignet2)
                  (aignet-well-formedp aignet)
                  (aignet-copies-ok (nth *num-nodes* aignet) aignet-copy
                                    aignet2))
             (b* (((mv & aignet-copy & aignet2)
                   (aignet-copy-dfs-outs aignet aignet-mark aignet-copy
                    strash gatesimp aignet2)))
               (and (aignet-copies-ok (nth *num-nodes* aignet) aignet-copy aignet2)
                    (aignet-well-formedp aignet2)))))

  (defthm aignet-copy-dfs-invar-holds-of-aignet-add-out
    (implies ;(and (aignet-well-formedp aignet2)
     (and (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)
          (aignet-copies-ok (nth *num-nodes* aignet)
                            aignet-copy aignet2))
     (aignet-copy-dfs-invar
      aignet aignet-mark aignet-copy
      (aignet-add-out fanin aignet2)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-outs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)
                  (<= (nfix n) (nth *num-outs* aignet)))
             (b* (((mv aignet-mark aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet aignet-mark aignet-copy
                    strash gatesimp aignet2)))
               (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-outs
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2))
             (b* (((mv aignet-mark aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-outs aignet aignet-mark aignet-copy
                                         strash gatesimp aignet2)))
               (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2))))

  (defthm aignet-copy-dfs-outs-iter-preserves-dfs-copiedp
    (implies (dfs-copiedp id aignet aignet-mark)
             (dfs-copiedp id aignet (mv-nth 0 (aignet-copy-dfs-outs-iter
                                              n aignet aignet-mark aignet-copy
                                              strash gatesimp aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-outs-preserves-dfs-copiedp
    (implies (dfs-copiedp id aignet aignet-mark)
             (dfs-copiedp id aignet (mv-nth 0 (aignet-copy-dfs-outs
                                               aignet aignet-mark aignet-copy
                                               strash gatesimp aignet2)))))

  (defthm outs-dfs-copied-of-aignet-copy-dfs-outs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id aignet)
                  (equal (id->type id aignet) (out-type))
                  (equal (io-id->regp id aignet) 0)
                  (< (io-id->ionum id aignet) (nfix n)))
             (dfs-copiedp id aignet
                          (mv-nth 0 (aignet-copy-dfs-outs-iter
                                     n aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-well-formedp-out-linear
                          (n id))
                         (:instance aignet-well-formedp-out-rw
                          (n id)))
                   :in-theory (disable aignet-well-formedp-out-linear
                                       aignet-well-formedp-out-rw)))))

  (defthm outs-dfs-copied-of-aignet-copy-dfs-outs
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id aignet)
                  (equal (id->type id aignet) (out-type))
                  (equal (io-id->regp id aignet) 0)
                  (< (io-id->ionum id aignet) (nth *num-outs* aignet)))
             (dfs-copiedp id aignet
                          (mv-nth 0 (aignet-copy-dfs-outs
                                     aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2)))))

  (defthm num-outs-of-aignet-copy-dfs-outs-iter
    (implies (equal (nth *num-outs* aignet2) 0)
             (equal (nth *num-outs*
                         (mv-nth 3 (aignet-copy-dfs-outs-iter
                                    m aignet aignet-mark aignet-copy
                                    strash gatesimp aignet2)))
                    (nfix m)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
                    m aignet aignet-mark aignet-copy
                    strash gatesimp aignet2))
           '(:in-theory (enable* aignet-frame-thms))))

  (defthm num-outs-of-aignet-copy-dfs-outs
    (implies (equal (nth *num-outs* aignet2) 0)
             (equal (nth *num-outs*
                         (mv-nth 3 (aignet-copy-dfs-outs
                                    aignet aignet-mark aignet-copy
                                    strash gatesimp aignet2)))
                    (nfix (nth *num-outs* aignet)))))

  (defthm new-output-of-aignet-add-out
    (implies (equal (nfix n) (nfix (nth *num-outs* aignet)))
             (equal (nth-id n (nth *outsi* (aignet-add-out fanin aignet)))
                    (to-id (nth *num-nodes* aignet))))
    :hints(("Goal" :in-theory (enable* aignet-add-out
                                       aignet-add-out1
                                       aignet-frame-thms))))

  (defthm eval-new-id-of-aignet-add-out
    (implies (aignet-well-formedp aignet)
             (equal (id-eval (to-id (nth *num-nodes* aignet))
                             in-vals reg-vals
                             (aignet-add-out fanin aignet))
                    (lit-eval (aignet-lit-fix fanin aignet)
                              in-vals reg-vals aignet)))
    :hints(("Goal" :in-theory (enable* aignet-frame-thms
                                       id-eval
                                       co-orderedp
                                       aignet-idp))))


  (defthm eval-output-of-aignet-copy-dfs-outs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (equal (nth *num-outs* aignet2) 0)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)
                  (< (nfix n) (nfix m))
                  (<= (nfix m) (nth *num-outs* aignet)))
             (b* (((mv ?aignet-mark ?aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-outs-iter
                    m aignet aignet-mark aignet-copy
                    strash gatesimp aignet2)))
             (equal (id-eval (nth-id n (nth *outsi* aignet2))
                             in-vals reg-vals aignet2)
                    (id-eval (outnum->id n aignet)
                             in-vals reg-vals aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
                    m aignet aignet-mark aignet-copy
                    strash gatesimp aignet2))
           '(:in-theory (enable* aignet-frame-thms)
             :cases ((equal (nfix n) (1- m))))))

  (defthm eval-output-of-aignet-copy-dfs-outs
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (equal (nth *num-outs* aignet2) 0)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)
                  (< (nfix n) (nth *num-outs* aignet)))
             (b* (((mv ?aignet-mark ?aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-outs
                    aignet aignet-mark aignet-copy strash gatesimp aignet2)))
             (equal (id-eval (nth-id n (nth *outsi* aignet2))
                             in-vals reg-vals aignet2)
                    (id-eval (outnum->id n aignet)
                             in-vals reg-vals aignet)))))

  (defthm lit-eval-in-aignet-copy-dfs-outs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)
                  (<= (nfix n) (nth *num-outs* aignet)))
             (b* (((mv aignet-mark aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet aignet-mark aignet-copy strash gatesimp aignet2)))
               (implies (and (aignet-idp id aignet)
                             (dfs-copiedp id aignet aignet-mark))
                        (equal (lit-eval (nth-lit (id-val id) aignet-copy)
                                         invals regvals aignet2)
                               (id-eval id invals regvals aignet)))))
    :hints (("goal" :use aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-outs-iter
             :in-theory (disable
                         aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-outs-iter))))

  (defthm lit-eval-in-aignet-copy-dfs-outs
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2))
             (b* (((mv aignet-mark aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-outs
                    aignet aignet-mark aignet-copy strash gatesimp aignet2)))
               (implies (and (aignet-idp id aignet)
                             (dfs-copiedp id aignet aignet-mark))
                        (equal (lit-eval (nth-lit (id-val id) aignet-copy)
                                         invals regvals aignet2)
                               (id-eval id invals regvals aignet)))))))

(defsection aignet-copy-dfs-regs

  (local (in-theory (disable acl2::aignetp)))

  (defund aignet-unconnected-regs-p (n aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (aignet-well-formedp aignet)
                                (natp n)
                                (<= n (num-regs aignet)))
                    :measure (nfix (- (nfix (num-regs aignet))
                                      (nfix n)))))
    (if (mbe :logic (zp (- (nfix (num-regs aignet))
                           (nfix n)))
             :exec (int= (num-regs aignet) n))
        t
      (and (aignet-unconnected-reg-p (regnum->ro (lnfix n) aignet) aignet)
           (aignet-unconnected-regs-p (+ 1 (lnfix n)) aignet))))

  (local (in-theory (enable aignet-unconnected-regs-p)))

  (defthm aignet-unconnected-regs-p-implies-unconnected
    (implies (and (aignet-unconnected-regs-p n aignet)
                  (<= (nfix n) (nfix m))
                  (< (nfix m) (nfix (num-regs aignet))))
             (aignet-unconnected-reg-p
              (regnum->ro m aignet) aignet)))

  (defthm aignet-unconnected-regs-p-implies-later
    (implies (and (aignet-unconnected-regs-p n aignet)
                  (<= (nfix n) (nfix m)))
             (aignet-unconnected-regs-p m aignet)))

  (local (defthm aignet-idp-implies-not-equal-num-nodes
           (implies (aignet-idp id aignet)
                    (not (equal (id-val id) (nth *num-nodes* aignet))))
           :hints(("Goal" :in-theory (enable aignet-idp)))))

  (local (defthm regnum->ro-not-zero
           (implies (and (aignet-well-formedp aignet)
                         (< (nfix m) (num-regs aignet)))
                    (not (equal 0 (id-val (regnum->ro m aignet)))))
           :hints(("Goal" :in-theory (e/d (regnum->ro)
                                          (aignet-well-formedp-regnum-id))
                   :use ((:instance aignet-well-formedp-regnum-id
                          (id 0) (n m)))))))

  (defthm regnum->id-of-aignet-add-regin-of-regnum->ro
    (implies (and (aignet-well-formedp aignet)
                  (aignet-unconnected-reg-p (regnum->ro m aignet) aignet)
                  (< (nfix n) (num-regs aignet))
                  (< (nfix m) (num-regs aignet)))
             (equal (nth-id n (nth *regsi* (aignet-add-regin
                                            lit (regnum->ro m aignet) aignet)))
                    (if (equal (nfix n) (nfix m))
                        (to-id (num-nodes aignet))
                      (nth-id n (nth *regsi* aignet)))))
    :hints(("Goal" :in-theory (enable*
                               aignet-add-regin
                               aignet-add-regin1
                               aignet-frame-thms))))

  (defthm aignet-unconnected-reg-p-of-aignet-add-regin-of-regnum->ro
    (implies (and (aignet-well-formedp aignet)
                  (aignet-unconnected-reg-p (regnum->ro m aignet) aignet)
                  (< (nfix n) (num-regs aignet))
                  (< (nfix m) (num-regs aignet)))
             (equal (aignet-unconnected-reg-p
                     (regnum->ro n aignet)
                     (aignet-add-regin
                      lit (regnum->ro m aignet) aignet))
                    (and (aignet-unconnected-reg-p (regnum->ro n aignet) aignet)
                         (not (equal (nfix n) (nfix m))))))
    :hints(("Goal" :in-theory (enable*
                               aignet-frame-thms))
           (and stable-under-simplificationp
                `(:expand ((:free (id)
                            (aignet-unconnected-reg-p
                             id (aignet-add-regin lit (regnum->ro m aignet)
                                                  aignet)))
                           (:free (aignet2)
                            (aignet-unconnected-reg-p
                             (regnum->ro n aignet) aignet2))))))
    :otf-flg t)

  (defthm aignet-unconnected-regs-p-add-regin-before
    (implies (and (aignet-well-formedp aignet)
                  (aignet-unconnected-regs-p n aignet)
                  (aignet-unconnected-reg-p (regnum->ro m aignet) aignet)
                  (< (nfix m) (nfix n))
                  (<= (nfix n) (num-regs aignet)))
             (aignet-unconnected-regs-p
              n (aignet-add-regin
                 lit (regnum->ro m aignet) aignet)))
    :hints (("goal" :induct (aignet-unconnected-regs-p n aignet)
             :in-theory (enable* aignet-frame-thms)
             :expand ((:free (aignet)
                       (aignet-unconnected-regs-p n aignet))))))

  (defthm aignet-unconnected-regs-p-step
    (implies (and (aignet-well-formedp aignet)
                  (natp n)
                  (aignet-unconnected-regs-p n aignet)
                  (< n (num-regs aignet)))
             (aignet-unconnected-regs-p
              (+ 1 n)
              (aignet-add-regin
               lit (regnum->ro n aignet) aignet))))

  (defthm aignet-unconnected-regs-p-step-of-ext
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-extension-p aignet2 aignet)
                  (aignet-unconnected-regs-p n aignet2)
                  (natp n)
                  (< n (num-regs aignet)))
             (aignet-unconnected-regs-p
              (+ 1 n)
              (aignet-add-regin
               lit (regnum->ro n aignet) aignet2)))
    :hints (("goal" :use ((:instance aignet-unconnected-regs-p-step
                           (aignet aignet2)))
             :do-not-induct t))
    :otf-flg t)

  (defthm regnum->id-of-aignet-add-regin-of-regnum->ro-of-ext
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-extension-p aignet2 aignet)
                  (aignet-unconnected-reg-p (regnum->ro m aignet) aignet2)
                  (< (nfix n) (num-regs aignet))
                  (< (nfix m) (num-regs aignet)))
             (equal (nth-id n (nth *regsi* (aignet-add-regin
                                            lit (regnum->ro m aignet) aignet2)))
                    (if (equal (nfix n) (nfix m))
                        (to-id (num-nodes aignet2))
                      (nth-id n (nth *regsi* aignet2)))))
    :hints (("goal" :use ((:instance
                           regnum->id-of-aignet-add-regin-of-regnum->ro
                           (aignet aignet2))))))

  (defthm aignet-unconnected-reg-p-of-aignet-add-regin-of-regnum->ro-of-ext
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-extension-p aignet2 aignet)
                  (aignet-unconnected-reg-p (regnum->ro m aignet) aignet2)
                  (< (nfix n) (num-regs aignet))
                  (< (nfix m) (num-regs aignet)))
             (equal (aignet-unconnected-reg-p
                     (regnum->ro n aignet)
                     (aignet-add-regin
                      lit (regnum->ro m aignet) aignet2))
                    (and (aignet-unconnected-reg-p (regnum->ro n aignet) aignet2)
                         (not (equal (nfix n) (nfix m))))))
    :hints (("goal" :use ((:instance
                           aignet-unconnected-reg-p-of-aignet-add-regin-of-regnum->ro
                           (aignet aignet2))))))


  (defthm aignet-unconnected-reg-p-of-aignet-copy-dfs-rec
    (implies (aignet-idp reg aignet2)
             (equal 
              (aignet-unconnected-reg-p
               reg (mv-nth 3 (aignet-copy-dfs-rec
                              id aignet aignet-mark
                              aignet-copy strash gatesimp aignet2)))
              (aignet-unconnected-reg-p reg aignet2)))
    :hints(("Goal" :in-theory (enable* aignet-unconnected-reg-p
                                       aignet-frame-thms))))

  (defthm aignet-unconnected-regs-p-of-aignet-copy-dfs-rec
    (implies (aignet-well-formedp aignet2)
             (equal (aignet-unconnected-regs-p
                     n (mv-nth 3 (aignet-copy-dfs-rec
                                  id aignet aignet-mark
                                  aignet-copy strash gatesimp aignet2)))
                    (aignet-unconnected-regs-p n aignet2)))
    :hints(("Goal" :in-theory (enable* aignet-frame-thms))))

  (local (in-theory (disable aignet-unconnected-regs-p)))

  (defiteration aignet-copy-dfs-regs
    (aignet aignet-mark aignet-copy strash gatesimp aignet2)
    (declare (xargs :stobjs (aignet aignet-mark aignet-copy strash aignet2)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (equal (num-regs aignet2)
                                       (num-regs aignet))
                                (natp gatesimp)
                                (bitarr-sizedp aignet-mark aignet)
                                (litarr-sizedp aignet-copy aignet)
                                (aignet-copies-ok
                                 (num-nodes aignet) aignet-copy aignet2))
                    :guard-hints (("goal" :in-theory (enable* aignet-frame-thms)))))
    (b* ((regid (regnum->id n aignet))
         ((mv aignet-mark aignet-copy strash aignet2)
          (aignet-copy-dfs-rec
           regid aignet aignet-mark aignet-copy strash gatesimp aignet2))
         (fanin (get-id->lit regid aignet-copy))
         (aignet2 (aignet-add-regin
                   fanin (regnum->ro n aignet2) aignet2)))
      (mv aignet-mark aignet-copy strash aignet2))
    :iter-guard (aignet-unconnected-regs-p n aignet2)
    :top-guard (aignet-unconnected-regs-p 0 aignet2)
    :returns (mv aignet-mark aignet-copy strash aignet2)
    :index n
    :last (num-regs aignet))

  (in-theory (disable aignet-copy-dfs-regs))
  (local (in-theory (enable aignet-copy-dfs-regs)))
  (in-theory (enable (:induction aignet-copy-dfs-regs-iter)))

  (def-aignet-preservation-thms
    aignet-copy-dfs-regs-iter
    :stobjname aignet2
    :omit (aignet-unconnected-reg-p-preserved))
  (def-aignet-preservation-thms aignet-copy-dfs-regs
    :stobjname aignet2
    :omit (aignet-unconnected-reg-p-preserved))

  (def-aignet2-frame aignet-copy-dfs-regs-iter
        :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet aignet-mark aignet-copy strash
              gatesimp aignet2))
            '(:in-theory (enable* aignet-frame-thms)
              :do-not-induct t
              :do-not '(generalize))))

  (def-aignet2-frame aignet-copy-dfs-regs)

  (defthm copies-sized-of-aignet-copy-dfs-regs-iter
    (implies (litarr-sizedp aignet-copy aignet)
             (memo-tablep (mv-nth 1 (aignet-copy-dfs-regs-iter
                                     n aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm copies-sized-of-aignet-copy-dfs-regs
    (implies (litarr-sizedp aignet-copy aignet)
             (memo-tablep (mv-nth 1 (aignet-copy-dfs-regs
                                     aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))
                          aignet)))

  (defthm mark-sized-of-aignet-copy-dfs-regs-iter
    (implies (bitarr-sizedp aignet-mark aignet)
             (memo-tablep (mv-nth 0 (aignet-copy-dfs-regs-iter
                                     n aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))
                          aignet))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm mark-sized-of-aignet-copy-dfs-regs
    (implies (bitarr-sizedp aignet-mark aignet)
             (memo-tablep (mv-nth 0 (aignet-copy-dfs-regs
                                     aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))
                          aignet)))

  (defthm aignet-copies-ok-of-aignet-copy-dfs-regs-iter
    (implies (and (aignet-well-formedp aignet2)
                  (aignet-well-formedp aignet)
                  (aignet-copies-ok (nth *num-nodes* aignet) aignet-copy
                                    aignet2)
                  (<= (nfix n) (nth *num-regs* aignet)))
             (b* (((mv & aignet-copy & aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet aignet-mark aignet-copy
                    strash gatesimp aignet2)))
               (and (aignet-copies-ok (nth *num-nodes* aignet) aignet-copy aignet2)
                    (aignet-well-formedp aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm aignet-copies-ok-of-aignet-copy-dfs-regs
    (implies (and (aignet-well-formedp aignet2)
                  (aignet-well-formedp aignet)
                  (aignet-copies-ok (nth *num-nodes* aignet) aignet-copy
                                    aignet2))
             (b* (((mv & aignet-copy & aignet2)
                   (aignet-copy-dfs-regs aignet aignet-mark aignet-copy
                    strash gatesimp aignet2)))
               (and (aignet-copies-ok (nth *num-nodes* aignet) aignet-copy aignet2)
                    (aignet-well-formedp aignet2)))))

  (defthm aignet-copy-dfs-invar-holds-of-aignet-add-regin
    (implies ;(and (aignet-well-formedp aignet2)
     (and (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)
          (aignet-copies-ok (nth *num-nodes* aignet)
                            aignet-copy aignet2))
     (aignet-copy-dfs-invar
      aignet aignet-mark aignet-copy
      (aignet-add-regin fanin regout aignet2)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-regs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)
                  (<= (nfix n) (nth *num-regs* aignet)))
             (b* (((mv aignet-mark aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet aignet-mark aignet-copy
                    strash gatesimp aignet2)))
               (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-regs
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2))
             (b* (((mv aignet-mark aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-regs aignet aignet-mark aignet-copy
                                         strash gatesimp aignet2)))
               (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2))))

  (defthm aignet-copy-dfs-regs-iter-preserves-dfs-copiedp
    (implies (dfs-copiedp id aignet aignet-mark)
             (dfs-copiedp id aignet (mv-nth 0 (aignet-copy-dfs-regs-iter
                                              n aignet aignet-mark aignet-copy
                                              strash gatesimp aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-regs-preserves-dfs-copiedp
    (implies (dfs-copiedp id aignet aignet-mark)
             (dfs-copiedp id aignet (mv-nth 0 (aignet-copy-dfs-regs
                                               aignet aignet-mark aignet-copy
                                               strash gatesimp aignet2)))))

  (defthm regs-dfs-copied-of-aignet-copy-dfs-regs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id aignet)
                  (equal (id->type id aignet) (out-type))
                  (equal (io-id->regp id aignet) 1)
                  (equal (id->type (regin-id->ro id aignet) aignet)
                         (in-type))
                  (< (io-id->ionum (regin-id->ro id aignet) aignet) (nfix n)))
             (dfs-copiedp id aignet
                          (mv-nth 0 (aignet-copy-dfs-regs-iter
                                     n aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet aignet-mark aignet-copy
              strash gatesimp aignet2))
            (and stable-under-simplificationp
                 '(:use ((:instance aignet-well-formedp-out-linear
                          (n id))
                         (:instance aignet-well-formedp-out-rw
                          (n id)))
                   :in-theory (disable aignet-well-formedp-out-linear
                                       aignet-well-formedp-out-rw)))))

  (defthm regs-dfs-copied-of-aignet-copy-dfs-regs
    (implies (and (aignet-well-formedp aignet)
                  (aignet-idp id aignet)
                  (equal (id->type id aignet) (out-type))
                  (equal (io-id->regp id aignet) 1)
                  (equal (id->type (regin-id->ro id aignet) aignet)
                         (in-type))
                  (< (io-id->ionum id aignet) (nth *num-regs* aignet)))
             (dfs-copiedp id aignet
                          (mv-nth 0 (aignet-copy-dfs-regs
                                     aignet aignet-mark aignet-copy
                                     strash gatesimp aignet2)))))

  (defthm num-regs-of-aignet-copy-dfs-regs-iter
    (equal (nth *num-regs*
                (mv-nth 3 (aignet-copy-dfs-regs-iter
                           m aignet aignet-mark aignet-copy
                           strash gatesimp aignet2)))
           (nth *num-regs* aignet2))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
                    m aignet aignet-mark aignet-copy
                    strash gatesimp aignet2))
           '(:in-theory (enable* aignet-frame-thms))))

  (defthm num-regs-of-aignet-copy-dfs-regs
    (equal (nth *num-regs*
                (mv-nth 3 (aignet-copy-dfs-regs
                           aignet aignet-mark aignet-copy
                           strash gatesimp aignet2)))
           (nth *num-regs* aignet2)))

  ;; (defthm new-reg-id-of-aignet-add-regin
  ;;   (implies (and (aignet-well-formedp aignet)
  ;;                 (< (nfix m) (num-regs aignet))
  ;;                 (< (nfix n) (num-regs aignet)))
  ;;            (equal (nth-id n (nth *regsi* (aignet-add-regin fanin aignet)))
  ;;                   (to-id (nth *num-nodes* aignet))))
  ;;   :hints(("Goal" :in-theory (enable* aignet-add-out
  ;;                                      aignet-add-out1
  ;;                                      aignet-frame-thms))))

  (defthm eval-new-id-of-aignet-add-regin
    (implies (aignet-well-formedp aignet)
             (equal (id-eval (to-id (nth *num-nodes* aignet))
                             in-vals reg-vals
                             (aignet-add-regin fanin ro aignet))
                    (lit-eval (aignet-lit-fix fanin aignet)
                              in-vals reg-vals aignet)))
    :hints(("Goal" :in-theory (enable* aignet-frame-thms
                                       id-eval
                                       co-orderedp
                                       aignet-idp))))

  (local (defthm <-of-decr
           (implies (and (not (zp m))
                         (integerp n)
                         (<= m n))
                    (equal (< (+ -1 m) n) t))))

  (local (defthm equal-of-decr
           (implies (and (not (zp m))
                         (integerp n)
                         (<= m n))
                    (equal (equal (+ -1 m) n) nil))))

  (local (defun aignet-unconnected-reg-p-ind (m n)
           (if (zp m)
               n
             (list (aignet-unconnected-reg-p-ind
                    (1- m) n)
                   (aignet-unconnected-reg-p-ind
                    (1- m) (1- m))))))

  (defthm aignet-unconnected-reg-p-of-aignet-copy-dfs-regs-iter
    (implies (and (aignet-well-formedp aignet2)
                  (<= (nfix m) (nfix n))
                  (< (nfix n) (num-regs aignet2))
                  (aignet-unconnected-regs-p 0 aignet2)
                  (aignet-unconnected-reg-p
                   (regnum->ro n aignet2)
                   aignet2))
             (aignet-unconnected-reg-p
              (regnum->ro n aignet2)
              (mv-nth 3 (aignet-copy-dfs-regs-iter
                         m aignet aignet-mark aignet-copy strash
                         gatesimp aignet2))))
    :hints(("goal" :induct (list (aignet-unconnected-reg-p-ind m n)
                                 (aignet-copy-dfs-regs-iter
                                  m aignet aignet-mark aignet-copy strash
                                  gatesimp aignet2))
            :expand ((aignet-copy-dfs-regs-iter
                      m aignet aignet-mark aignet-copy strash
                      gatesimp aignet2)))))


  (defthm eval-regin-of-aignet-copy-dfs-regs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (equal (nth *num-regs* aignet2)
                         (nth *num-regs* aignet))
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy
                                         aignet2)
                  (aignet-unconnected-regs-p 0 aignet2)
                  (< (nfix n) (nfix m))
                  (<= (nfix m) (nth *num-regs* aignet)))
             (b* (((mv ?aignet-mark ?aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-regs-iter
                    m aignet aignet-mark aignet-copy
                    strash gatesimp aignet2)))
             (equal (id-eval (nth-id n (nth *regsi* aignet2))
                             in-vals reg-vals aignet2)
                    (id-eval (regnum->id n aignet)
                             in-vals reg-vals aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
                    m aignet aignet-mark aignet-copy
                    strash gatesimp aignet2))
           '(:in-theory (enable* aignet-frame-thms)
             :cases ((equal (nfix n) (1- m))))))

  (defthm eval-regin-of-aignet-copy-dfs-regs
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (equal (nth *num-regs* aignet2) (nth *num-regs* aignet))
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy
                                         aignet2)
                  (aignet-unconnected-regs-p 0 aignet2)
                  (< (nfix n) (nth *num-regs* aignet)))
             (b* (((mv ?aignet-mark ?aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-regs
                    aignet aignet-mark aignet-copy strash gatesimp aignet2)))
             (equal (id-eval (nth-id n (nth *regsi* aignet2))
                             in-vals reg-vals aignet2)
                    (id-eval (regnum->id n aignet)
                             in-vals reg-vals aignet)))))

  (defthm lit-eval-in-aignet-copy-dfs-regs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy
                                         aignet2)
                  (<= (nfix n) (nth *num-regs* aignet)))
             (b* (((mv aignet-mark aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet aignet-mark aignet-copy strash gatesimp aignet2)))
               (implies (and (aignet-idp id aignet)
                             (dfs-copiedp id aignet aignet-mark))
                        (equal (lit-eval (nth-lit (id-val id) aignet-copy)
                                         invals regvals aignet2)
                               (id-eval id invals regvals aignet)))))
    :hints (("goal" :use aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-regs-iter
             :in-theory (disable
                         aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-regs-iter))))

  (defthm lit-eval-in-aignet-copy-dfs-regs
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-copies-ok (num-nodes aignet) aignet-copy aignet2)
                  (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2))
             (b* (((mv aignet-mark aignet-copy ?strash aignet2)
                   (aignet-copy-dfs-regs
                    aignet aignet-mark aignet-copy strash gatesimp aignet2)))
               (implies (and (aignet-idp id aignet)
                             (dfs-copiedp id aignet aignet-mark))
                        (equal (lit-eval (nth-lit (id-val id) aignet-copy)
                                         invals regvals aignet2)
                               (id-eval id invals regvals aignet)))))))


(defsection aignet-copy-dfs

  (local (in-theory (disable acl2::resize-list-when-empty)))

  (defthm aignet-copies-ok-of-init
    (implies (aignet-well-formedp aignet2)
             (aignet-copies-ok n (resize-list nil m 0)
                               aignet2))
    :hints (("goal" :induct (aignet-copies-ok n (update-nth 0 (resize-list nil m 0) '(nil))
                                              aignet2)
             :expand ((:free (aignet-copy)
                       (aignet-copies-ok n aignet-copy aignet2)))
             :in-theory (e/d (nth-lit
                              acl2::nth-with-large-index
                              acl2::nth-of-resize-list-split)
                             ((:induction resize-list)
                              (:induction true-listp))))))
  
  (local (in-theory (enable (:induction aignet-copy-regs-iter))))

  (defthm num-regs-of-aignet-copy-regs
    (implies (aignet-well-formedp aignet2)
             (equal (nth *num-regs* (mv-nth 1 (aignet-copy-regs-iter n aignet aignet-copy aignet2)))
                    (+ (num-regs aignet2)
                       (nfix n))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-regs-iter n aignet aignet-copy aignet2))))

  (defund aignet-copy-dfs-setup (aignet aignet-mark aignet-copy aignet2)
    (declare (xargs :stobjs (aignet aignet-mark aignet-copy aignet2)
                    :guard (aignet-well-formedp aignet)))
    (b* ((aignet2 (aignet-init (lnfix (num-outs aignet))
                               (lnfix (num-regs aignet))
                               (lnfix (num-ins aignet))
                               (lnfix (num-nodes aignet))
                               aignet2))
         (aignet-mark (bitarr-clear aignet-mark))
         (aignet-mark (resize-bits (num-nodes aignet) aignet-mark))
         (aignet-copy (litarr-clear aignet-copy))
         (aignet-copy (resize-lits (num-nodes aignet) aignet-copy))
         ((mv aignet-copy aignet2)
          (aignet-copy-ins aignet aignet-copy aignet2))
         ((mv aignet-copy aignet2)
          (aignet-copy-regs aignet aignet-copy aignet2)))
      (mv aignet-mark aignet-copy aignet2)))

  (local (in-theory (enable aignet-copy-dfs-setup)))

  (defthm aignet-copy-dfs-setup-normalize
    (implies (syntaxp (not (and (equal aignet-mark ''nil)
                                (equal aignet-copy ''nil))))
             (equal (aignet-copy-dfs-setup aignet aignet-mark aignet-copy
                                           aignet2)
                    (aignet-copy-dfs-setup aignet nil nil aignet2))))

  (defthm aignet-copy-dfs-setup-well-formed
    (implies (aignet-well-formedp aignet)
             (b* (((mv aignet-mark aignet-copy aignet2)
                   (aignet-copy-dfs-setup aignet aignet-mark aignet-copy
                                          aignet2)))
               (and (memo-tablep aignet-mark aignet)
                    (memo-tablep aignet-copy aignet)
                    (aignet-copies-ok (nth *num-nodes* aignet) aignet-copy aignet2)
                    (aignet-well-formedp aignet2)))))

  (def-aignet2-frame aignet-copy-dfs-setup)

  (defthm num-outs-of-aignet-copy-dfs-setup
    (equal (nth *num-outs* (mv-nth 2 (aignet-copy-dfs-setup
                                      aignet aignet-mark aignet-copy aignet2)))
           0)
    :hints(("Goal" :in-theory (enable* aignet-frame-thms))))

  (defthm num-regs-of-aignet-copy-dfs-setup
    (equal (nth *num-regs* (mv-nth 2 (aignet-copy-dfs-setup
                                      aignet aignet-mark aignet-copy aignet2)))
           (nfix (nth *num-regs* aignet)))
    :hints(("Goal" :in-theory (enable* aignet-frame-thms))))

  (defthm aignet-unconnected-reg-p-of-aignet-copy-ins-iter
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n) (nfix (num-regs aignet)))
                  (aignet-unconnected-reg-p (regnum->ro n aignet) aignet))
             (let ((aignet (mv-nth 1 (aignet-copy-ins-iter m aignet2 aignet-copy aignet))))
               (aignet-unconnected-reg-p (regnum->ro n aignet) aignet)))
    :hints(;; (acl2::just-induct-and-expand
           ;;  (aignet-copy-ins-iter m aignet2 aignet-copy aignet))
           '(:in-theory (enable* aignet-frame-thms
                                 aignet-unconnected-reg-p
                                 regnum->ro))))

  (defthm aignet-unconnected-reg-p-of-aignet-add-reg-prev
    (implies (and (aignet-well-formedp aignet)
                  (aignet-unconnected-reg-p (regnum->ro n aignet) aignet)
                  (< (nfix n) (num-regs aignet)))
             (let ((aignet (mv-nth 1 (aignet-add-reg aignet))))
               (aignet-unconnected-reg-p (regnum->ro n aignet) aignet)))
    :hints(("Goal" :in-theory (enable* aignet-add-reg
                                       aignet-frame-thms
                                       aignet-unconnected-reg-p
                                       regnum->ro
                                       nth-node-of-update-nth-node-split))))

  (defthm aignet-unconnected-reg-p-of-aignet-add-reg
    (implies (and (aignet-well-formedp aignet)
                  (equal (nfix n) (num-regs aignet)))
             (let ((aignet (mv-nth 1 (aignet-add-reg aignet))))
               (aignet-unconnected-reg-p (regnum->ro n aignet) aignet)))
    :hints(("Goal" :in-theory (enable* aignet-add-reg
                                       aignet-frame-thms
                                       aignet-unconnected-reg-p
                                       regnum->ro
                                       nth-node-of-update-nth-node-split))))

  (defthm aignet-unconnected-reg-p-of-aignet-copy-regs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-unconnected-reg-p (regnum->ro n aignet) aignet)
                  (< (nfix n) (num-regs aignet)))
             (let ((aignet (mv-nth 1 (aignet-copy-regs-iter m aignet2
                                                            aignet-copy
                                                            aignet))))
               (aignet-unconnected-reg-p (regnum->ro n aignet) aignet))))

  (defthm aignet-unconnected-reg-p-of-aignet-copy-regs-iter-new
    (implies (and (aignet-well-formedp aignet)
                  (<= (num-regs aignet) (nfix n)))
             (let ((aignet (mv-nth 1 (aignet-copy-regs-iter m aignet2
                                                            aignet-copy
                                                            aignet))))
               (implies (< (nfix n) (num-regs aignet))
                        (aignet-unconnected-reg-p (regnum->ro n aignet)
                                                  aignet))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-regs-iter m aignet2
                                   aignet-copy
                                   aignet))
           (and stable-under-simplificationp
                '(:cases ((equal (nfix n)
                                 (num-regs
                                  (mv-nth 1 (aignet-copy-regs-iter
                                             (1- m) aignet2 aignet-copy aignet)))))))))

  (in-theory (enable (:induction aignet-unconnected-regs-p)))

  (defthm aignet-unconnected-regs-p-of-aignet-copy-regs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-unconnected-regs-p n aignet))
             (aignet-unconnected-regs-p
              n (mv-nth 1 (aignet-copy-regs-iter m aignet2 aignet-copy
                                                 aignet))))
    :hints('(:in-theory (disable (:induction aignet-copy-regs-iter)))
           (acl2::just-induct-and-expand
            (aignet-unconnected-regs-p
             n (mv-nth 1 (aignet-copy-regs-iter m aignet2 aignet-copy
                                                aignet))))
           (and stable-under-simplificationp
                '(:expand ((:free (aignet) (aignet-unconnected-regs-p n aignet)))
                  :cases ((<= (num-regs aignet) (nfix n)))))))

  (defthm aignet-unconnected-regs-p-of-aignet-copy-ins-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-unconnected-regs-p n aignet))
             (let ((aignet (mv-nth 1 (aignet-copy-ins-iter m aignet2 aignet-copy aignet))))
               (aignet-unconnected-regs-p n aignet)))
    :hints((acl2::just-induct-and-expand
            (aignet-unconnected-regs-p
             n (mv-nth 1 (aignet-copy-ins-iter m aignet2 aignet-copy aignet))))
           (and stable-under-simplificationp
                '(:expand
                  ((:free (aignet) (aignet-unconnected-regs-p n aignet)))
                  :in-theory (enable* aignet-frame-thms)))))

  (defthm aignet-unconnected-regs-p-of-aignet-init
    (aignet-unconnected-regs-p 0 (aignet-init outs regs ins nodes aignet))
    :hints(("Goal" :in-theory (enable* aignet-init
                                       aignet-unconnected-regs-p))))

  (local (in-theory (enable* aignet-frame-thms)))

  (defun aignet-copy-dfs (aignet aignet2 gatesimp)
    (declare (xargs :stobjs (aignet aignet2)
                    :guard (and (aignet-well-formedp aignet)
                                (aignet-well-formedp aignet2)
                                (natp gatesimp))))
    (b* (((local-stobjs aignet-mark aignet-copy strash)
          (mv aignet-mark aignet-copy strash aignet2))
         ((mv aignet-mark aignet-copy aignet2)
          (aignet-copy-dfs-setup aignet aignet-mark aignet-copy aignet2))
         ((mv aignet-mark aignet-copy strash aignet2)
          (aignet-copy-dfs-regs aignet aignet-mark aignet-copy strash
                                gatesimp aignet2))
         ((mv aignet-mark aignet-copy strash aignet2)
          (aignet-copy-dfs-outs aignet aignet-mark aignet-copy strash
                                gatesimp aignet2)))
      (mv aignet-mark aignet-copy strash aignet2)))

  (defthm aignet-well-formedp-of-aignet-copy-dfs
    (aignet-well-formedp (aignet-copy-dfs aignet aignet2 gatesimp)))

  (defthm num-nodes-of-aignet-copy-ins-iter
    (implies (natp (num-nodes aignet2))
             (equal (nth *num-nodes* (mv-nth 1 (aignet-copy-ins-iter
                                                n aignet aignet-copy aignet2)))
                    (+ (nfix n) (nth *num-nodes* aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-ins-iter n aignet aignet-copy aignet2))))

  (defthm id-eval-of-aignet-add-in-new
    (implies (and (aignet-well-formedp aignet)
                  (equal (id-val id) (num-nodes aignet)))
             (equal (id-eval id invals regvals (mv-nth 1 (aignet-add-in aignet)))
                    (bfix (nth (num-ins aignet) invals))))
    :hints(("Goal" :in-theory (enable aignet-add-in
                                      aignet-idp)
            :expand ((:free (aignet) (id-eval id invals regvals aignet))))))
    

  (defthm aignet-copy-ins-iter-copy-of-non-input
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (num-ins aignet))
                  (not (and (equal (id->type id aignet) (in-type))
                            (equal (io-id->regp id aignet) 0))))
             (equal (nth-lit (id-val id)
                             (mv-nth 0 (aignet-copy-ins-iter
                                        n aignet aignet-copy aignet2)))
                    (nth-lit (id-val id) aignet-copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-ins-iter n aignet aignet-copy aignet2))
           '(:in-theory (enable* aignet-well-formedp-strong-rules))))

  (defthm eval-id-of-aignet-copy-ins-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-idp (id-fix id) aignet)
                  (equal (num-ins aignet2) 0)
                  (equal (id->type id aignet) (in-type))
                  (equal (io-id->regp id aignet) 0)
                  (< (io-id->ionum id aignet) (nfix n))
                  (<= (nfix n) (num-ins aignet)))
             (mv-let (aignet-copy aignet2)
               (aignet-copy-ins-iter n aignet aignet-copy aignet2)
               (and (equal (lit-eval (nth-lit (id-val id) aignet-copy)
                                     invals regvals aignet2)
                           (id-eval id invals regvals aignet))
                    (aignet-litp (nth-lit (id-val id) aignet-copy)
                                 aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-ins-iter n aignet aignet-copy aignet2))
           (and stable-under-simplificationp
                '(:in-theory (enable* lit-eval
                                      aignet-well-formedp-strong-rules)
                  :expand ((:free (aignet)
                            (id-eval id invals regvals aignet)))))))


  (defthm num-nodes-of-aignet-copy-regs-iter
    (implies (natp (num-nodes aignet2))
             (equal (nth *num-nodes* (mv-nth 1 (aignet-copy-regs-iter
                                                n aignet aignet-copy aignet2)))
                    (+ (nfix n) (nth *num-nodes* aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-regs-iter n aignet aignet-copy aignet2))))

  (defthm id-eval-of-aignet-add-reg-new
    (implies (and (aignet-well-formedp aignet)
                  (equal (id-val id) (num-nodes aignet)))
             (equal (id-eval id invals regvals (mv-nth 1 (aignet-add-reg aignet)))
                    (bfix (nth (num-regs aignet) regvals))))
    :hints(("Goal" :in-theory (enable aignet-add-reg
                                      aignet-idp)
            :expand ((:free (aignet) (id-eval id invals regvals aignet))))))

  (defthm aignet-copy-regs-iter-copy-of-non-reg
    (implies (and (aignet-well-formedp aignet)
                  (<= (nfix n) (num-regs aignet))
                  (not (and (equal (id->type id aignet) (in-type))
                            (equal (io-id->regp id aignet) 1))))
             (equal (nth-lit (id-val id)
                             (mv-nth 0 (aignet-copy-regs-iter
                                        n aignet aignet-copy aignet2)))
                    (nth-lit (id-val id) aignet-copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-regs-iter n aignet aignet-copy aignet2))
           '(:in-theory (enable* aignet-well-formedp-strong-rules))))

  (defthm eval-id-of-aignet-copy-regs-iter
    (implies (and (aignet-well-formedp aignet)
                  (aignet-well-formedp aignet2)
                  (aignet-idp (id-fix id) aignet)
                  (equal (num-regs aignet2) 0)
                  (equal (id->type id aignet) (in-type))
                  (equal (io-id->regp id aignet) 1)
                  (< (io-id->ionum id aignet) (nfix n))
                  (<= (nfix n) (num-regs aignet)))
             (mv-let (aignet-copy aignet2)
               (aignet-copy-regs-iter n aignet aignet-copy aignet2)
               (and (equal (lit-eval (nth-lit (id-val id) aignet-copy)
                                     invals regvals aignet2)
                           (id-eval id invals regvals aignet))
                    (aignet-litp (nth-lit (id-val id) aignet-copy)
                                 aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-regs-iter n aignet aignet-copy aignet2))
           (and stable-under-simplificationp
                '(:in-theory (enable* lit-eval
                                      aignet-well-formedp-strong-rules)
                  :expand ((:free (aignet)
                            (id-eval id invals regvals aignet)))))))

  (defthm aignet-copy-dfs-invar-of-aignet-copy-dfs-setup-lemma
    (mv-let (aignet-mark aignet-copy aignet2)
      (aignet-copy-dfs-setup aignet nil nil aignet2)    
      (implies (and (aignet-well-formedp aignet)
                    (aignet-idp id aignet)
                    (dfs-copiedp id aignet aignet-mark))
               (equal (lit-eval (nth-lit (id-val id) aignet-copy)
                                invals regvals aignet2)
                      (id-eval id invals regvals aignet))))
    :hints(("Goal" :in-theory (e/d (dfs-copiedp)
                                   (LOOKUP-COPY-OF-AIGNET-COPY-INS-ITER))
            :cases ((equal (id->type id aignet) 0)))
           '(:cases ((equal (io-id->regp id aignet) 1)))
            ;; :expand ((:free (aignet-copy aignet2)
            ;;           (lit-eval (nth-lit (id-val id) aignet-copy)
            ;;                     invals regvals aignet2))
            ;;          (id-eval id invals regvals aignet))
            ))
    

  (defthm aignet-copy-dfs-invar-of-aignet-copy-dfs-setup
    (implies (aignet-well-formedp aignet)
             (mv-let (aignet-mark aignet-copy aignet2)
               (aignet-copy-dfs-setup aignet nil nil aignet2)
             (aignet-copy-dfs-invar aignet aignet-mark aignet-copy aignet2)))
    :hints(("Goal" :in-theory (e/d (aignet-copy-dfs-invar)
                                   (aignet-copy-dfs-setup)))))


  (defthm aignet-unconnected-regs-p-of-aignet-copy-dfs-setup
    (implies (aignet-well-formedp aignet)
             (mv-let (aignet-mark aignet-copy aignet2)
               (aignet-copy-dfs-setup aignet nil nil aignet2)
               (declare (ignore aignet-mark aignet-copy))
               (aignet-unconnected-regs-p 0 aignet2))))

  (defthm eval-out-of-aignet-copy-dfs
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n) (num-outs aignet)))
             (let ((aignet2 (aignet-copy-dfs aignet aignet2 gatesimp)))
               (equal (id-eval (nth-id n (nth *outsi* aignet2)) in-vals reg-vals
                               aignet2)
                      (id-eval (nth-id n (nth *outsi* aignet)) in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (e/d* (aignet-frame-thms)
                                    (aignet-copy-dfs-setup)))))

  (defthm eval-regin-of-aignet-copy-dfs
    (implies (and (aignet-well-formedp aignet)
                  (< (nfix n) (num-regs aignet)))
             (let ((aignet2 (aignet-copy-dfs aignet aignet2 gatesimp)))
               (equal (id-eval (nth-id n (nth *regsi* aignet2)) in-vals reg-vals
                               aignet2)
                      (id-eval (nth-id n (nth *regsi* aignet)) in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (e/d* (aignet-frame-thms)
                                    (aignet-copy-dfs-setup)))))

  (defthm num-outs-of-aignet-copy-dfs
    (equal (nth *num-outs* (aignet-copy-dfs aignet aignet2 gatesimp))
           (nfix (nth *num-outs* aignet)))
    :hints(("Goal" :in-theory (enable* aignet-frame-thms))))

  (defthm num-regs-of-aignet-copy-dfs
    (equal (nth *num-regs* (aignet-copy-dfs aignet aignet2 gatesimp))
           (nfix (nth *num-regs* aignet)))
    :hints(("Goal" :in-theory (enable* aignet-frame-thms))))

  (defthm aignet-copy-dfs-comb-equiv
    (implies (aignet-well-formedp aignet)
             (comb-equiv (aignet-copy-dfs aignet aignet2 gatesimp)
                         aignet))
    :hints(("Goal" :in-theory (e/d (comb-equiv)
                                   (aignet-copy-dfs))))))

