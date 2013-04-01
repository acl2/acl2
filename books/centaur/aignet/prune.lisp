(in-package "AIGNET")

(include-book "copying")

(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable sets::double-containment)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           sets::double-containment
                           sets::sets-are-true-lists
                           make-list-ac)))

(local (acl2::use-trivial-ancestors-check))

(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (in-theory (disable id-eval
                           true-listp
                           sets::double-containment
                           acl2::nfix-when-not-natp
                           acl2::natp-when-integerp)))


(include-book "types")


;(defsection aignet-copy-dfs

(defsection aignet-copy-dfs-rec

  (acl2::defstobj-clone mark bitarr :suffix "-MARK")

  (defund aignet-copy-dfs-rec (id aignet mark copy strash gatesimp aignet2)
    (declare (type (integer 0 *) id)
             (xargs :stobjs (aignet mark copy strash aignet2)
                    :guard (and (id-existsp id aignet)
                                (natp gatesimp)
                                (<= (num-nodes aignet) (bits-length mark))
                                (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-ok
                                 (num-nodes aignet) copy aignet2))
                    :guard-debug t
                    :verify-guards nil
                    :measure (nfix id)))
    (b* (((when (int= (get-bit id mark) 1))
          (mv mark copy strash aignet2))
         (slot0 (id->slot id 0 aignet))
         (type (snode->type slot0))
         ((when (int= type (out-type)))
          ;; copy the fanin of the output and set the output ID's copy to be
          ;; that of the fanin lit
          (b* ((f (co-id->fanin id aignet))
               ((mv mark copy strash aignet2)
                (aignet-copy-dfs-rec
                 (lit-id f) aignet mark copy strash gatesimp
                 aignet2))
               (f-copy (lit-copy f copy))
               (copy (set-lit id f-copy copy))
               (mark (set-bit id 1 mark)))
            (mv mark copy strash aignet2)))

         ((when (int= type (const-type)))
          (b* ((mark (set-bit id 1 mark))
               (copy (set-lit id 0 copy)))
            (mv mark copy strash aignet2)))

         ((unless (int= type (gate-type)))
          (b* ((mark (set-bit id 1 mark)))
            (mv mark copy strash aignet2)))

         ;; gate: recur on each fanin, then hash an AND of the two copies
         (f0 (gate-id->fanin0 id aignet))
         (f1 (gate-id->fanin1 id aignet))
         ((mv mark copy strash aignet2)
          (aignet-copy-dfs-rec
           (lit-id f0) aignet mark copy strash gatesimp aignet2))
         (f0-copy (lit-copy f0 copy))
         ((when (int= f0-copy (to-lit 0)))
          ;; first branch was 0 so exit early
          (b* ((copy (set-lit id 0 copy))
               (mark (set-bit id 1 mark)))
            (mv mark copy strash aignet2)))
         ((mv mark copy strash aignet2)
          (aignet-copy-dfs-rec
           (lit-id f1) aignet mark copy strash gatesimp aignet2))
         (f1-copy (lit-copy f1 copy))
         ((mv id-copy strash aignet2)
          (aignet-hash-and f0-copy f1-copy gatesimp strash aignet2))
         (copy (set-lit id id-copy copy))
         (mark (set-bit id 1 mark)))
      (mv mark copy strash aignet2)))

  (defthm litp-of-lit-negate-cond
    (litp (lit-negate-cond lit neg)))

  (local (in-theory (disable lit-negate-cond acl2::b-xor
                             aignet-copies-ok)))
  (local (in-theory (enable (:induction aignet-copy-dfs-rec))))

  (def-aignet-preservation-thms aignet-copy-dfs-rec :stobjname aignet2)

  (defcong nat-equiv equal
    (aignet-copy-dfs-rec id aignet mark
                         copy strash gatesimp aignet2)
    1
    :hints (("goal" :induct
             (aignet-copy-dfs-rec id aignet mark
                                  copy strash gatesimp aignet2)
             :expand ((aignet-copy-dfs-rec id aignet mark
                                           copy strash gatesimp aignet2)
                      (aignet-copy-dfs-rec acl2::id-equiv aignet mark
                                           copy strash gatesimp aignet2)))))

  (defthm copies-sized-of-aignet-copy-dfs-rec
    (<= (len copy)
        (len (mv-nth 1 (aignet-copy-dfs-rec
                        id aignet mark copy
                        strash gatesimp aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2)))
    :rule-classes :linear)

  (defthm mark-sized-of-aignet-copy-dfs-rec
    (<= (len mark)
        (len (mv-nth 0 (aignet-copy-dfs-rec
                        id aignet mark copy
                        strash gatesimp aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2)))
    :rule-classes :linear)

  ;; (defthm id-in-bounds-when-memo-tablep-bind-free
  ;;   (implies (and (bind-free '((aignet . aignet)) (aignet))
  ;;                 (< (node-count aignet) (len arr))
  ;;                 (double-rewrite (aignet-idp n aignet)))
  ;;            (id-in-bounds n arr)))

  (defthm aignet-copies-ok-implies-special-bind-free
    (implies (and (bind-free '((aignet1 . aignet)) (aignet1))
                  (aignet-copies-ok (num-nodes aignet1) copy aignet)
                  (aignet-idp k aignet1))
             (aignet-litp (nth-lit k copy) aignet)))

  (local (in-theory (enable lit-negate-cond)))

  (defthm aignet-copies-ok-of-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy
                    strash gatesimp aignet2)))
               (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2))))

  (verify-guards aignet-copy-dfs-rec
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm stype-counts-preserved-of-aignet-copy-dfs-rec
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype (mv-nth 3 (aignet-copy-dfs-rec
                                                  id aignet mark copy
                                                  strash gatesimp aignet2)))
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2)))))





(defsection aignet-ins-copied

  (in-theory (disable aignet-copy-ins))

  (local (in-theory (enable aignet-copy-ins)))

  (defun-sk aignet-ins-copied (aignet copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal (id->type id aignet) (in-type))
                          (equal (io-id->regp id aignet) 0))
                     (equal (lit-eval (nth-lit id copy)
                                      invals regvals aignet2)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable aignet-ins-copied))

  (defthm id-eval-of-input-index
    (implies (< (nfix n) (num-ins aignet))
             (equal (id-eval (node-count (lookup-stype n (pi-stype) aignet))
                             invals regvals aignet)
                    (bfix (nth n invals))))
    :hints(("Goal" 
            :in-theory (enable* id-eval))))

  (defthm aignet-ins-copied-of-aignet-copy-ins
    (implies (equal 0 (num-ins aignet2))
             (b* (((mv copy aignet2)
                   (aignet-copy-ins aignet copy aignet2)))
               (aignet-ins-copied aignet copy aignet2)))
    :hints (("goal" :in-theory (e/d (aignet-ins-copied lit-eval id-eval)))))

  (defthm aignet-copy-regs-preserves-aignet-ins-copied
    (implies (and (aignet-ins-copied aignet copy aignet2)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2))
             (b* (((mv copy aignet2)
                   (aignet-copy-regs aignet copy aignet2)))
               (aignet-ins-copied aignet copy aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-regs))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))))))

(defsection aignet-regs-copied

  (in-theory (disable aignet-copy-regs))

  (local (in-theory (enable aignet-copy-regs)))

  (defun-sk aignet-regs-copied (aignet copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal (id->type id aignet) (in-type))
                          (equal (io-id->regp id aignet) 1))
                     (equal (lit-eval (nth-lit id copy)
                                      invals regvals aignet2)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable aignet-regs-copied))

  (defthm id-eval-of-reg-index
    (implies (< (nfix n) (num-regs aignet))
             (equal (id-eval (regnum->id n aignet)
                             invals regvals aignet)
                    (bfix (nth n regvals))))
    :hints(("Goal" 
            :in-theory (enable* id-eval regnum->id))))

  (defthm aignet-regs-copied-of-aignet-copy-regs
    (implies (equal 0 (num-regs aignet2))
             (b* (((mv copy aignet2)
                   (aignet-copy-regs aignet copy aignet2)))
               (aignet-regs-copied aignet copy aignet2)))
    :hints (("goal" :in-theory (e/d (aignet-regs-copied lit-eval id-eval)))))

  (defthm aignet-copy-ins-preserves-aignet-regs-copied
    (implies (and (aignet-regs-copied aignet copy aignet2)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2))
             (b* (((mv copy aignet2)
                   (aignet-copy-ins aignet copy aignet2)))
               (aignet-regs-copied aignet copy aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-ins))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))))))

(defsection aignet-cis-copied
  (defun-sk aignet-cis-copied (aignet copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal (id->type id aignet) (in-type)))
                     (equal (lit-eval (nth-lit id copy)
                                      invals regvals aignet2)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)
  
  (defthm aignet-cis-copied-when-aignet-ins/regs-copied
    (implies (and (aignet-ins-copied aignet copy aignet2)
                  (aignet-regs-copied aignet copy aignet2))
             (aignet-cis-copied aignet copy aignet2))
    :hints (("goal" :cases ((equal 1 (io-id->regp
                                      (MV-NTH 0 (AIGNET-CIS-COPIED-WITNESS
                                                 AIGNET COPY AIGNET2))
                                      aignet))))))

  (in-theory (disable aignet-cis-copied))

  (defthm aignet-cis-copied-of-aignet-copy-ins/regs
    (implies (and (equal 0 (num-ins aignet2))
                  (equal 0 (num-regs aignet2))
                  (aignet-copies-ok (num-nodes aignet) copy aignet2))
             (b* (((mv copy aignet2)
                   (aignet-copy-ins aignet copy aignet2))
                  ((mv copy aignet2)
                   (aignet-copy-regs aignet copy aignet2)))
               (aignet-cis-copied aignet copy aignet2)))))



;; (defsection aignet-copy-dfs-ext
;;   (defun-sk aignet-copy-dfs-ext (mark-new copy-new mark copy aignet)
;;     (forall id 
;;             (and (implies (equal (nth id mark) 1)
;;                           (equal (nth id mark-new) 1))
;;                  (implies (equal (nth id mark) 1)
;;                           (equal (nth-lit id copy-new)
;;                                  (nth-lit id copy)))
;;                  (implies (equal (id->type id aignet) (in-type))
;;                           (equal (nth-lit id copy-new)
;;                                  (nth-lit id copy))))))

;;   (in-theory (disable aignet-copy-dfs-ext
;;                       aignet-copy-dfs-ext-necc))

;;   (defun aignet-copy-dfs-ext-binding-fn (mark-new copy-new
;;                                                mark-var copy-var iters
;;                                                mfc state)
;;     (declare (xargs :mode :program :stobjs state))
;;     (append (prev-stobj-binding mark-new mark-var iters mfc state)
;;             (prev-stobj-binding copy-new copy-var iters mfc state)
;;             (and (not (assoc 'aignet (acl2::mfc-unify-subst mfc)))
;;                  '((aignet . aignet)))))

;;   (defmacro aignet-copy-dfs-ext-binding (&key (mark-new 'mark-new)
;;                                           (copy-new 'copy-new)
;;                                           (mark-var 'mark)
;;                                           (copy-var 'copy)
;;                                           (iters '1))
;;     `(bind-free (aignet-copy-dfs-ext-binding-fn
;;                  ,mark-new ,copy-new ',mark-var ',copy-var ',iters mfc state)))

;;   (defthm aignet-copy-dfs-ext-transitive
;;     (implies (and (aignet-copy-dfs-ext-binding
;;                    :mark-new mark3 :copy-new copy3
;;                    :mark-var mark2 :copy-var copy2)
;;                   (aignet-copy-dfs-ext mark3 copy3
;;                                        mark2 copy2 aignet)
;;                   (aignet-copy-dfs-ext mark2 copy2
;;                                        mark1 copy1 aignet))
;;              (aignet-copy-dfs-ext mark3 copy3
;;                                   mark1 copy1 aignet))
;;     :hints ((and stable-under-simplificationp
;;                  (let ((term (car (last clause))))
;;                  `(:expand (,term)
;;                    :use ((:instance aignet-copy-dfs-ext-necc
;;                           (mark-new mark3) (copy-new copy3)
;;                           (mark mark2) (copy copy2)
;;                           (id (aignet-copy-dfs-ext-witness . ,(cdr term))))
;;                          (:instance aignet-copy-dfs-ext-necc
;;                           (mark-new mark2) (copy-new copy2)
;;                           (mark mark1) (copy copy1)
;;                           (id (aignet-copy-dfs-ext-witness . ,(cdr term)))))))))))

(defsection aignet-copy-dfs-invar

  ;; (defund-nx dfs-copiedp (id aignet mark)
  ;;   (implies (or (int= (id->type id aignet) (gate-type))
  ;;                (int= (id->type id aignet) (out-type)))
  ;;            (int= (get-bit id mark) 1)))
  
  ;; (local (in-theory (enable dfs-copiedp)))

  ;; (defthm dfs-copiedp-when-get-bit
  ;;   (implies (int= (get-bit id mark) 1)
  ;;            (dfs-copiedp id aignet mark)))

  ;; (defthm dfs-copiedp-when-in/const
  ;;   (implies (and (not (int= (id->type id aignet) (gate-type)))
  ;;                 (not (int= (id->type id aignet) (out-type))))
  ;;            (dfs-copiedp id aignet mark)))

  ;; (defthm not-dfs-copiedp
  ;;   (implies (and (or (int= (id->type id aignet) (gate-type))
  ;;                     (int= (id->type id aignet) (out-type)))
  ;;                 (not (int= (get-bit id mark) 1)))
  ;;            (not (dfs-copiedp id aignet mark))))

  ;; (defthm dfs-copiedp-of-update-diff
  ;;   (implies (not (equal (nfix n) (id-val w)))
  ;;            (equal (dfs-copiedp
  ;;                    w aignet
  ;;                    (update-nth n v mark))
  ;;                   (double-rewrite
  ;;                    (dfs-copiedp w aignet mark))))
  ;;   :hints(("Goal" :in-theory (enable dfs-copiedp))))

  ;; (defcong nat-equiv equal (dfs-copiedp id aignet mark) 1)
  ;; (defcong nth-equiv equal (dfs-copiedp id aignet mark) 3)

  ;; (local (in-theory (disable dfs-copiedp)))

  

  (defun-sk aignet-copy-dfs-invar (aignet mark copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal 1 (get-bit id mark)))
                     (equal (lit-eval (nth-lit id copy)
                                      invals regvals aignet2)
                            (id-eval id invals regvals aignet))))
    :rewrite :direct)

  (in-theory (disable aignet-copy-dfs-invar))

  (local (in-theory (enable (:induction aignet-copy-dfs-rec))))

  (local (in-theory (disable acl2::b-xor lit-negate-cond)))

  (defthm aignet-copy-dfs-rec-preserves-dfs-copiedp
    (implies (equal (nth n mark) 1)
             (equal (nth n (mv-nth 0 (aignet-copy-dfs-rec
                                      id aignet mark copy
                                      strash gatesimp aignet2)))
                    1))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2))
            (and stable-under-simplificationp
                 '(:in-theory (enable dfs-copiedp)))))

  (defthm aignet-copy-dfs-rec-id-marked
    (equal (nth id
                (mv-nth 0 (aignet-copy-dfs-rec
                           id aignet mark copy
                           strash gatesimp aignet2)))
           1)
    :hints (("goal" :expand ((aignet-copy-dfs-rec
                              id aignet mark copy
                              strash gatesimp aignet2)))))

  (defthm aignet-copy-dfs-rec-preserves-copy-when-marked
    (implies (equal (nth i mark) 1)
             (equal (nth-lit i (mv-nth 1 (aignet-copy-dfs-rec
                                           id aignet mark copy
                                           strash gatesimp aignet2)))
                    (nth-lit i copy)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-rec-preserves-ci-copies
    (implies (double-rewrite (equal (id->type i aignet) (in-type)))
             (equal (nth-lit i (mv-nth 1 (aignet-copy-dfs-rec
                                           id aignet mark copy
                                           strash gatesimp aignet2)))
                    (nth-lit i copy)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2))))

  ;; (defthm aignet-copy-dfs-rec-preserves-0-copy
  ;;   (equal (nth-lit 0 (mv-nth 1 (aignet-copy-dfs-rec
  ;;                                id aignet mark copy
  ;;                                strash gatesimp aignet2)))
  ;;          (nth-lit 0 copy))
  ;;   :hints ((acl2::just-induct-and-expand
  ;;            (aignet-copy-dfs-rec
  ;;             id aignet mark copy
  ;;             strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-rec-preserves-aignet-cis-copied
    (implies (and (aignet-cis-copied aignet copy aignet2)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy strash gatesimp aignet2)))
               (aignet-cis-copied aignet copy aignet2)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (local (defthm lit-eval-of-lit-negate-cond
           (equal (lit-eval (lit-negate-cond lit neg)
                            in-vals reg-vals aignet)
                  (acl2::b-xor (lit-eval lit in-vals reg-vals aignet) neg))
           :hints(("Goal" :in-theory (enable lit-negate-cond lit-eval)))))

  (local
   (defthm aignet-copy-dfs-invar-necc-rewrite
     (b* (((mv mark copy & aignet2)
           (aignet-copy-dfs-rec
            id aignet mark copy
            strash gatesimp aignet2)))
       (implies (and (aignet-copy-dfs-invar
                      aignet mark copy aignet2)
                     (aignet-cis-copied aignet copy aignet2)
                     (aignet-idp id aignet))
                (equal (lit-eval
                        (nth-lit id copy)
                        in-vals reg-vals aignet2)
                       (id-eval id in-vals reg-vals aignet))))
     :hints (("goal" :do-not-induct t))))

  (local (defthm equal-mk-lit-rw
           (equal (equal (mk-lit id neg) val)
                  (and (litp val)
                       (equal (nfix id) (lit-id val))
                       (equal (bfix neg) (lit-neg val))))
           :hints(("Goal" :in-theory (disable mk-lit-identity)
                   :use ((:instance mk-lit-identity (lit val)))))))

  (defthm aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (aignet-copy-dfs-invar aignet mark copy aignet2)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (aignet-cis-copied aignet copy aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy
                    strash gatesimp aignet2)))
               (aignet-copy-dfs-invar aignet mark copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2))
            (and stable-under-simplificationp
                 (let ((last (car (last clause))))
                   `(:expand (,last)
                     :do-not '(generalize fertilize eliminate-destructors)
                     :do-not-induct t)))
            (and stable-under-simplificationp
                 (let ((witness (acl2::find-call-lst
                                 'aignet-copy-dfs-invar-witness
                                 clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((mv-nth '0 ,witness) . id2)
                              ((mv-nth '1 ,witness) . invals)
                              ((mv-nth '2 ,witness) . regvals))))))
            (and stable-under-simplificationp
                 '(:in-theory (enable eval-and-of-lits
                                      lit-negate-cond)
                   :expand ((:free (in-vals reg-vals)
                             (id-eval id in-vals reg-vals aignet)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable lit-eval)))
            (and stable-under-simplificationp
                 (member-equal '(NOT (EQUAL (stype (car (lookup-id id aignet))) ':gate))
                               clause)
                 (let ((term '(b* ((fanin (gate-id->fanin0 id aignet)))
                                (aignet-copy-dfs-rec
                                 (lit-id fanin) aignet mark copy
                                 strash gatesimp aignet2))))
                   `(:use ((:instance aignet-copy-dfs-invar-necc
                            (id (lit-id (gate-id->fanin0 id aignet)))
                            (mark (mv-nth 0 ,term))
                            (copy (mv-nth 1 ,term))
                            (aignet2 (mv-nth 3 ,term))))
                     :in-theory (e/d (lit-negate-cond lit-eval)
                                     (aignet-copy-dfs-invar-necc
                                      aignet-copy-dfs-invar-necc-rewrite))))))
    :otf-flg t)

  (defthm lit-eval-in-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (aignet-copy-dfs-invar aignet mark copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (equal (nth-lit 0 copy) 0))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-rec
                    id aignet mark copy strash gatesimp aignet2)))
               (implies (and (aignet-idp id2 aignet)
                             (equal 1 (nth id2 mark)))
                        (equal (lit-eval (nth-lit id2 copy)
                                         invals regvals aignet2)
                               (id-eval id2 invals regvals aignet)))))
    :hints (("goal" :use aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-rec
             :in-theory (disable aignet-copy-dfs-invar-holds-of-aignet-copy-dfs-rec)))))

(defsection aignet-copy-dfs-outs
  (defthm aignet-copy-dfs-rec-is-list-of-mv-nths
    (let ((x (aignet-copy-dfs-rec
              id aignet mark copy strash gatesimp aignet2)))
      (equal (list (mv-nth 0 x) (mv-nth 1 x) (mv-nth 2 x) (mv-nth 3 x))
             x))
    :hints('(:in-theory (enable (:induction aignet-copy-dfs-rec)))
           (and stable-under-simplificationp
                (acl2::just-induct-and-expand
                 (aignet-copy-dfs-rec
                  id aignet mark copy strash gatesimp aignet2)))))

  (defiteration aignet-copy-dfs-outs
    (aignet mark copy strash gatesimp aignet2)
    (declare (xargs :stobjs (aignet mark copy strash aignet2)
                    :guard (and (natp gatesimp)
                                (<= (num-nodes aignet) (bits-length mark))
                                (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-ok
                                 (num-nodes aignet) copy aignet2))))
    (b* ((outid (outnum->id n aignet)))
      (aignet-copy-dfs-rec
       outid aignet mark copy strash gatesimp aignet2))
    :returns (mv mark copy strash aignet2)
    :index n
    :last (num-outs aignet))

  (def-aignet-preservation-thms aignet-copy-dfs-outs-iter
    :stobjname aignet2)

  (defthm memo-tablep-of-aignet-copy-dfs-outs-iter-copy
    (<= (len copy)
        (len (mv-nth 1 (aignet-copy-dfs-outs-iter
                        n aignet mark copy strash gatesimp aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
             n aignet mark copy strash gatesimp
             aignet2)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-copy-dfs-outs-iter-mark
    (<= (len mark)
        (len (mv-nth 0 (aignet-copy-dfs-outs-iter
                        n aignet mark copy strash gatesimp aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
             n aignet mark copy strash gatesimp
             aignet2)))
    :rule-classes :linear)

  (defthm aignet-copy-dfs-outs-iter-preserves-marked
    (implies (equal 1 (nth id mark))
             (equal (nth id (mv-nth 0 (aignet-copy-dfs-outs-iter
                                       n aignet mark copy strash gatesimp
                                       aignet2)))
                    1))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copy-dfs-outs-iter-preserves-marked-lits
    (implies (equal 1 (nth id mark))
             (equal (nth-lit id (mv-nth 1 (aignet-copy-dfs-outs-iter
                                           n aignet mark copy strash gatesimp
                                           aignet2)))
                    (nth-lit id copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copy-dfs-outs-iter-preserves-ci-copy
    (implies (equal (id->type id aignet) (in-type))
             (equal (nth-lit id (mv-nth 1 (aignet-copy-dfs-outs-iter
                                           n aignet mark copy strash gatesimp
                                           aignet2)))
                    (nth-lit id copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-outs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copies-ok-of-aignet-copy-dfs-outs-iter
    (implies (and (<= (nfix n) (num-outs aignet))
                  (aignet-copies-ok (num-nodes aignet) copy aignet2))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-copies-ok (+ 1 (node-count aignet))
                                 copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-outs-iter-preserves-aignet-cis-copied
    (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (<= (nfix n) (num-outs aignet)))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-cis-copied aignet copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (local (defthm decr-less-when-lte
           (implies (<= n m)
                    (and (< (+ -1 n) m)
                         (<= (+ -1 n) m)))))

  (defthm aignet-copy-dfs-outs-iter-preserves-aignet-copy-dfs-invar
    (implies (and (aignet-copy-dfs-invar aignet mark copy aignet2)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (<= (nfix n) (num-outs aignet)))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-outs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-copy-dfs-invar aignet mark copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm outnum-marked-of-aignet-copy-dfs-outs-iter
    (implies (< (nfix m) (nfix n))
             (equal (nth (node-count (lookup-stype m (po-stype) aignet))
                         (mv-nth 0 (aignet-copy-dfs-outs-iter
                                    n aignet mark copy strash gatesimp aignet2)))
                    1))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-dfs-outs-iter
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype (mv-nth 3 (aignet-copy-dfs-outs-iter
                                                  n aignet mark copy
                                                  strash gatesimp aignet2)))
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-outs-iter
              n aignet mark copy
              strash gatesimp aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-dfs-outs
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype (mv-nth 3 (aignet-copy-dfs-outs
                                                  aignet mark copy
                                                  strash gatesimp aignet2)))
                    (stype-count stype aignet2)))))


(defsection aignet-copy-dfs-regs
  (defiteration aignet-copy-dfs-regs
    (aignet mark copy strash gatesimp aignet2)
    (declare (xargs :stobjs (aignet mark copy strash aignet2)
                    :guard (and (natp gatesimp)
                                (<= (num-nodes aignet) (bits-length mark))
                                (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-ok
                                 (num-nodes aignet) copy aignet2))))
    (b* ((regid (reg-id->nxst (regnum->id n aignet) aignet)))
      (aignet-copy-dfs-rec
       regid aignet mark copy strash gatesimp aignet2))
    :returns (mv mark copy strash aignet2)
    :index n
    :last (num-regs aignet))

  (def-aignet-preservation-thms aignet-copy-dfs-regs-iter
    :stobjname aignet2)

  (defthm memo-tablep-of-aignet-copy-dfs-regs-iter-copy
    (<= (len copy)
        (len (mv-nth 1 (aignet-copy-dfs-regs-iter
                        n aignet mark copy strash gatesimp aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
             n aignet mark copy strash gatesimp
             aignet2)))
    :rule-classes :linear)

  (defthm memo-tablep-of-aignet-copy-dfs-regs-iter-mark
    (<= (len mark)
        (len (mv-nth 0 (aignet-copy-dfs-regs-iter
                        n aignet mark copy strash gatesimp aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
             n aignet mark copy strash gatesimp
             aignet2)))
    :rule-classes :linear)

  (defthm aignet-copy-dfs-regs-iter-preserves-marked
    (implies (equal 1 (nth id mark))
             (equal (nth id (mv-nth 0 (aignet-copy-dfs-regs-iter
                                       n aignet mark copy strash gatesimp
                                       aignet2)))
                    1))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copy-dfs-regs-iter-preserves-marked-lits
    (implies (equal 1 (nth id mark))
             (equal (nth-lit id (mv-nth 1 (aignet-copy-dfs-regs-iter
                                           n aignet mark copy strash gatesimp
                                           aignet2)))
                    (nth-lit id copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copy-dfs-regs-iter-preserves-ci-copy
    (implies (equal (id->type id aignet) (in-type))
             (equal (nth-lit id (mv-nth 1 (aignet-copy-dfs-regs-iter
                                           n aignet mark copy strash gatesimp
                                           aignet2)))
                    (nth-lit id copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-dfs-regs-iter
             n aignet mark copy strash gatesimp
             aignet2))))

  (defthm aignet-copies-ok-of-aignet-copy-dfs-regs-iter
    (implies (and (<= (nfix n) (num-regs aignet))
                  (aignet-copies-ok (num-nodes aignet) copy aignet2))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-copies-ok (+ 1 (node-count aignet))
                                 copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm aignet-copy-dfs-regs-iter-preserves-aignet-cis-copied
    (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (<= (nfix n) (num-regs aignet)))
             (b* (((mv & copy & aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-cis-copied aignet copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (local (defthm decr-less-when-lte
           (implies (<= n m)
                    (and (< (+ -1 n) m)
                         (<= (+ -1 n) m)))))

  (defthm aignet-copy-dfs-regs-iter-preserves-aignet-copy-dfs-invar
    (implies (and (aignet-copy-dfs-invar aignet mark copy aignet2)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (aignet-cis-copied aignet copy aignet2)
                  (<= (nfix n) (num-regs aignet)))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-regs-iter
                    n aignet mark copy strash gatesimp aignet2)))
               (aignet-copy-dfs-invar aignet mark copy aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm regnum-marked-of-aignet-copy-dfs-regs-iter
    (implies (< (nfix m) (nfix n))
             (equal (nth (node-count
                          (lookup-reg->nxst
                           (node-count (lookup-stype m (reg-stype) aignet))
                           aignet))
                         (mv-nth 0 (aignet-copy-dfs-regs-iter
                                    n aignet mark copy strash gatesimp aignet2)))
                    1))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet mark copy strash gatesimp aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-dfs-regs-iter
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype (mv-nth 3 (aignet-copy-dfs-regs-iter
                                                  n aignet mark copy
                                                  strash gatesimp aignet2)))
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-regs-iter
              n aignet mark copy
              strash gatesimp aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-dfs-regs
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype (mv-nth 3 (aignet-copy-dfs-regs
                                                  aignet mark copy
                                                  strash gatesimp aignet2)))
                    (stype-count stype aignet2)))))
             



(defsection aignet-copy-dfs

  (local (in-theory (disable acl2::resize-list-when-empty)))

  (defthm aignet-copies-ok-of-init
    (aignet-copies-ok n (resize-list nil m 0)
                      aignet2)
    :hints (("goal" :induct (aignet-copies-ok n (update-nth 0 (resize-list nil m 0) '(nil))
                                              aignet2)
             :expand ((:free (copy)
                       (aignet-copies-ok n copy aignet2)))
             :in-theory (e/d (nth-lit
                              acl2::nth-with-large-index
                              acl2::nth-of-resize-list-split
                              aignet-copies-ok)
                             ((:induction resize-list)
                              (:induction true-listp))))))
  
  (local (in-theory (enable (:induction aignet-copy-regs-iter))))

  ;; (defthm num-regs-of-aignet-copy-regs
  ;;   (implies (aignet-well-formedp aignet2)
  ;;            (equal (nth *num-regs* (mv-nth 1 (aignet-copy-regs-iter n aignet copy aignet2)))
  ;;                   (+ (num-regs aignet2)
  ;;                      (nfix n))))
  ;;   :hints ((acl2::just-induct-and-expand
  ;;            (aignet-copy-regs-iter n aignet copy aignet2))))

  (defund aignet-copy-dfs-setup (aignet mark copy aignet2)
    (declare (xargs :stobjs (aignet mark copy aignet2)))
    (b* ((aignet2 (aignet-init (lnfix (num-outs aignet))
                               (lnfix (num-regs aignet))
                               (lnfix (num-ins aignet))
                               (lnfix (num-nodes aignet))
                               aignet2))
         (mark (bitarr-clear mark))
         (mark (resize-bits (num-nodes aignet) mark))
         (copy (litarr-clear copy))
         (copy (resize-lits (num-nodes aignet) copy))
         ((mv copy aignet2)
          (aignet-copy-ins aignet copy aignet2))
         ((mv copy aignet2)
          (aignet-copy-regs aignet copy aignet2)))
      (mv mark copy aignet2)))

  (local (in-theory (enable aignet-copy-dfs-setup)))

  (defthm aignet-copy-dfs-setup-normalize
    (implies (syntaxp (not (and (equal mark ''nil)
                                (equal copy ''nil))))
             (equal (aignet-copy-dfs-setup aignet mark copy
                                           aignet2)
                    (aignet-copy-dfs-setup aignet nil nil aignet2))))

  (defthm aignet-copy-dfs-setup-arrays-sized
    (b* (((mv mark copy ?aignet2)
          (aignet-copy-dfs-setup aignet mark copy
                                 aignet2)))
      (and (< (node-count aignet) (len mark))
           (< (node-count aignet) (len copy))))
    :rule-classes :linear)

  (defthm aignet-copy-dfs-setup-well-formed
    (b* (((mv ?mark copy aignet2)
          (aignet-copy-dfs-setup aignet mark copy
                                 aignet2)))
      (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)))

  (defthm num-outs-of-aignet-copy-dfs-setup
    (equal (stype-count (po-stype)
                        (mv-nth 2 (aignet-copy-dfs-setup
                                   aignet mark copy aignet2)))
           0))

  (defthm num-regs-of-aignet-copy-dfs-setup
    (equal (stype-count (reg-stype)
                        (mv-nth 2 (aignet-copy-dfs-setup
                                   aignet mark copy aignet2)))
           (stype-count (reg-stype) aignet)))

  (defun aignet-copy-dfs (aignet aignet2 gatesimp)
    (declare (xargs :stobjs (aignet aignet2)
                    :guard (natp gatesimp)))
    (b* (((local-stobjs mark copy strash)
          (mv mark copy strash aignet2))
         ((mv mark copy aignet2)
          (aignet-copy-dfs-setup aignet mark copy aignet2))
         ((mv mark copy strash aignet2)
          (aignet-copy-dfs-regs aignet mark copy strash
                                gatesimp aignet2))
         ((mv mark copy strash aignet2)
          (aignet-copy-dfs-outs aignet mark copy strash
                                gatesimp aignet2))
         (aignet2 (aignet-copy-outs aignet copy aignet2))
         (aignet2 (aignet-copy-nxsts aignet copy aignet2)))
      (mv mark copy strash aignet2)))

  (defthm num-nodes-of-aignet-copy-ins-iter
    (equal (node-count (mv-nth 1 (aignet-copy-ins-iter
                                  n aignet copy aignet2)))
           (+ (nfix n) (node-count aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-ins-iter n aignet copy aignet2))))

  (defthm aignet-copy-ins-iter-copy-of-non-input
    (implies (and (<= (nfix n) (num-ins aignet))
                  (not (and (equal (id->type id aignet) (in-type))
                            (equal (io-id->regp id aignet) 0))))
             (equal (nth-lit id
                             (mv-nth 0 (aignet-copy-ins-iter
                                        n aignet copy aignet2)))
                    (nth-lit id copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-ins-iter n aignet copy aignet2))))

  (defthm eval-id-of-aignet-copy-ins-iter
    (implies (and (aignet-idp id aignet)
                  (equal (num-ins aignet2) 0)
                  (equal (id->type id aignet) (in-type))
                  (equal (io-id->regp id aignet) 0)
                  (< (io-id->ionum id aignet) (nfix n))
                  (<= (nfix n) (num-ins aignet)))
             (mv-let (copy aignet2)
               (aignet-copy-ins-iter n aignet copy aignet2)
               (and (equal (lit-eval (nth-lit id copy)
                                     invals regvals aignet2)
                           (id-eval id invals regvals aignet))
                    (aignet-litp (nth-lit id copy)
                                 aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-ins-iter n aignet copy aignet2))
           (and stable-under-simplificationp
                '(:in-theory (enable* lit-eval)
                  :expand ((:free (aignet)
                            (id-eval (+ n (node-count aignet2))
                                     invals regvals aignet))
                           (:free (aignet)
                            (id-eval id invals regvals aignet)))))
           (and stable-under-simplificationp
                '(:in-theory (enable aignet-litp aignet-idp)))))


  (defthm num-nodes-of-aignet-copy-regs-iter
    (equal (node-count (mv-nth 1 (aignet-copy-regs-iter
                                  n aignet copy aignet2)))
           (+ (nfix n) (node-count aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-regs-iter n aignet copy aignet2))))


  (defthm aignet-copy-regs-iter-copy-of-non-reg
    (implies (and (<= (nfix n) (num-regs aignet))
                  (not (and (equal (id->type id aignet) (in-type))
                            (equal (io-id->regp id aignet) 1))))
             (equal (nth-lit id
                             (mv-nth 0 (aignet-copy-regs-iter
                                        n aignet copy aignet2)))
                    (nth-lit id copy)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-regs-iter n aignet copy aignet2))))

  (defthm eval-id-of-aignet-copy-regs-iter
    (implies (and (aignet-idp id aignet)
                  (equal (num-regs aignet2) 0)
                  (equal (id->type id aignet) (in-type))
                  (equal (io-id->regp id aignet) 1)
                  (< (io-id->ionum id aignet) (nfix n))
                  (<= (nfix n) (num-regs aignet)))
             (mv-let (copy aignet2)
               (aignet-copy-regs-iter n aignet copy aignet2)
               (and (equal (lit-eval (nth-lit id copy)
                                     invals regvals aignet2)
                           (id-eval id invals regvals aignet))
                    (aignet-litp (nth-lit id copy)
                                 aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-regs-iter n aignet copy aignet2))
           (and stable-under-simplificationp
                '(:in-theory (enable* lit-eval)
                  :expand ((:free (aignet)
                            (id-eval (node-count (lookup-stype (+ -1 n) :reg aignet))
                                     invals regvals aignet))
                           (:free (aignet)
                            (id-eval (+ n (node-count aignet2)) invals regvals aignet)))))
           (and stable-under-simplificationp
                '(:in-theory (enable aignet-litp aignet-idp)))))

  (defthm initial-marks-empty
    (not (equal (nth n (resize-list nil m 0)) 1))
    :hints(("Goal" :in-theory (enable acl2::nth-of-resize-list-split))))

  (defthm aignet-copy-dfs-invar-of-aignet-copy-dfs-setup-lemma
    (mv-let (mark copy aignet2)
      (aignet-copy-dfs-setup aignet nil nil aignet2)    
      (implies (and (aignet-idp id aignet)
                    (equal (nth id mark) 1))
               (equal (lit-eval (nth-lit id copy)
                                invals regvals aignet2)
                      (id-eval id invals regvals aignet))))
    :hints(("Goal" :in-theory (e/d ()
                                   (LOOKUP-COPY-OF-AIGNET-COPY-INS-ITER))
            :cases ((equal (id->type id aignet) 0)))
           '(:cases ((equal (io-id->regp id aignet) 1)))
           ;; :expand ((:free (copy aignet2)
           ;;           (lit-eval (nth-lit (id-val id) copy)
           ;;                     invals regvals aignet2))
           ;;          (id-eval id invals regvals aignet))
           ))
  

  (defthm aignet-copy-dfs-invar-of-aignet-copy-dfs-setup
    (mv-let (mark copy aignet2)
      (aignet-copy-dfs-setup aignet nil nil aignet2)
      (aignet-copy-dfs-invar aignet mark copy aignet2))
    :hints(("Goal" :in-theory (e/d (aignet-copy-dfs-invar)
                                   (aignet-copy-dfs-setup)))))

  (defthm aignet-cis-copied-of-aignet-copy-dfs-setup
    (b* (((mv ?mark copy aignet2)
          (aignet-copy-dfs-setup aignet nil nil aignet2)))
      (aignet-cis-copied aignet copy aignet2)))

  (defthm nth-0-copy-of-aignet-copy-dfs-setup
    (b* (((mv ?mark copy ?aignet2)
          (aignet-copy-dfs-setup aignet nil nil aignet2)))
      (equal (nth-lit 0 copy) 0)))


  ;; (defthm aignet-unconnected-regs-p-of-aignet-copy-dfs-setup
  ;;   (implies (aignet-well-formedp aignet)
  ;;            (mv-let (mark copy aignet2)
  ;;              (aignet-copy-dfs-setup aignet nil nil aignet2)
  ;;              (declare (ignore mark copy))
  ;;              (aignet-unconnected-regs-p 0 aignet2))))

  (defthm num-outs-of-aignet-copy-outs-iter
    (equal (stype-count (po-stype) (aignet-copy-outs-iter
                                    n aignet copy aignet2))
           (+ (nfix n) (stype-count (po-stype) aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-outs-iter n aignet copy aignet2))))

  (defthm nth-out-of-aignet-add-out
    (implies (nat-equiv n (stype-count (po-stype) aignet))
             (equal (node-count (lookup-stype n (po-stype) (cons (po-node lit) aignet)))
                    (+ 1 (node-count aignet))))
    :hints(("Goal" :in-theory (enable lookup-stype))))

  (defthm eval-latest-out-of-aignet-add-out
    (let ((aignet-new (cons (po-node lit) aignet)))
      (implies (aignet-litp lit aignet)
               (equal (id-eval (+ 1 (node-count aignet))
                               invals regvals aignet-new)
                      (lit-eval lit invals regvals aignet))))
    :hints(("Goal" :in-theory (e/d* (id-eval)))))

  (defthm eval-out-of-aignet-copy-outs-iter
    (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (<= (nfix n) (num-outs aignet))
                  (< (nfix m) (nfix n))
                  (zp (num-outs aignet2)))
             (let ((aignet2-new (aignet-copy-outs-iter
                                 n aignet copy aignet2)))
               (implies (aignet-extension-p aignet2-ext aignet2-new)
                        (equal (id-eval (node-count (lookup-stype m (po-stype) aignet2-new))
                                        invals regvals aignet2-ext)
                               (lit-eval (nth-lit (node-count (lookup-stype m (po-stype)
                                                                  aignet))
                                                  copy)
                                         invals regvals aignet2)))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-outs-iter n aignet copy aignet2))
           (and stable-under-simplificationp
                '(:cases ((equal (nfix m) (1- n)))))))

  (defthm eval-out-of-aignet-copy-outs
    (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (< (nfix m) (num-outs aignet))
                  (zp (num-outs aignet2)))
             (let ((aignet2-new (aignet-copy-outs aignet copy aignet2)))
               (implies (aignet-extension-p aignet2-ext aignet2-new)
                        (equal (id-eval (node-count (lookup-stype m (po-stype) aignet2-new))
                                        invals regvals aignet2-ext)
                               (lit-eval (nth-lit (node-count (lookup-stype m (po-stype)
                                                                  aignet))
                                                  copy)
                                         invals regvals aignet2)))))
    :hints(("Goal" :in-theory (enable aignet-copy-outs))))
                             
             
  (defthm aignet-copy-dfs-invar-necc-out-special
    (b* (((mv mark copy & aignet2)
          (aignet-copy-dfs-outs-iter n aignet mark copy strash gatesimp
                                     aignet2)))
      (implies
       (aignet-copy-dfs-invar aignet mark copy aignet2)
       (implies (and (aignet-idp id aignet)
                     (equal 1 (get-bit id mark)))
                (equal (lit-eval (nth-lit id copy)
                                 invals regvals aignet2)
                       (id-eval id invals regvals aignet))))))


  (defthm eval-out-of-aignet-copy-dfs
    (implies (< (nfix n) (num-outs aignet))
             (let ((aignet2 (aignet-copy-dfs aignet aignet2 gatesimp)))
               (equal (id-eval (node-count (lookup-stype n (po-stype) aignet2)) in-vals reg-vals
                               aignet2)
                      (id-eval (node-count (lookup-stype n (po-stype) aignet)) in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (e/d* ()
                                    (aignet-copy-dfs-setup)))))


  (defthm lookup-reg->nxst-of-add-nxst
    (implies (aignet-idp reg aignet)
             (equal (lookup-reg->nxst reg
                                      (cons (nxst-node lit reg) aignet))
                    (cons (nxst-node lit reg) aignet)))
    :hints(("Goal" :in-theory (enable lookup-reg->nxst
                                      aignet-idp))))

  (defthm eval-new-node-aignet-set-nxst
    (let ((aignet-new (cons (nxst-node lit reg) aignet)))
      (implies (aignet-litp lit aignet)
               (equal (id-eval (+ 1 (node-count aignet))
                               invals regvals aignet-new)
                      (lit-eval lit invals regvals aignet))))
    :hints(("Goal" :in-theory (e/d* (id-eval)))))

  (defthm lookup-reg->nxst-of-add-different-nxst
    (implies (and (aignet-idp reg aignet)
                  (not (nat-equiv reg reg2)))
             (equal (lookup-reg->nxst reg
                                      (cons (nxst-node lit reg2) aignet))
                    (lookup-reg->nxst reg aignet)))
    :hints(("Goal" :in-theory (enable lookup-reg->nxst))))

  (local (in-theory (enable lookup-stype-in-bounds)))

  (defthm eval-reg-of-aignet-copy-nxsts-iter
    (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (<= (nfix n) (num-regs aignet))
                  (< (nfix m) (nfix n))
                  (<= (num-regs aignet) (num-regs aignet2-orig)))
             (let ((aignet2-new (aignet-copy-nxsts-iter
                                 n aignet copy aignet2)))
               (implies (and (aignet-extension-p aignet2-ext aignet2-new)
                             (aignet-extension-p aignet2 aignet2-orig))
                        (equal (id-eval (node-count
                                         (lookup-reg->nxst
                                          (node-count
                                           (lookup-stype m (reg-stype) aignet2-orig))
                                          aignet2-new))
                                        invals regvals aignet2-ext)
                               (lit-eval (nth-lit (node-count
                                                   (lookup-reg->nxst
                                                    (node-count
                                                     (lookup-stype m (reg-stype) aignet))
                                                     aignet))
                                                   copy)
                                         invals regvals aignet2)))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-nxsts-iter n aignet copy aignet2))
           (and stable-under-simplificationp
                '(:cases ((equal (nfix m) (1- n)))))))

  (defthm eval-reg-of-aignet-copy-nxsts
    (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (< (nfix m) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2-orig)))
             (let ((aignet2-new (aignet-copy-nxsts aignet copy aignet2)))
               (implies (and (aignet-extension-p aignet2-ext aignet2-new)
                             (aignet-extension-p aignet2 aignet2-orig))
                        (equal (id-eval (node-count
                                         (lookup-reg->nxst
                                          (node-count
                                           (lookup-stype m (reg-stype) aignet2-orig))
                                          aignet2-new))
                                        invals regvals aignet2-ext)
                               (lit-eval (nth-lit (node-count
                                                   (lookup-reg->nxst
                                                    (node-count
                                                     (lookup-stype m (reg-stype) aignet))
                                                     aignet))
                                                   copy)
                                         invals regvals aignet2)))))
    :hints(("Goal" :in-theory (enable aignet-copy-nxsts))))
                             
             
  (defthm aignet-copy-dfs-invar-necc-nxst-special
    (b* (((mv mark copy & aignet2)
          (aignet-copy-dfs-regs-iter n aignet mark copy strash gatesimp
                                      aignet2)))
      (implies
       (aignet-copy-dfs-invar aignet mark copy aignet2)
       (implies (and (aignet-idp id aignet)
                     (equal 1 (get-bit id mark)))
                (equal (lit-eval (nth-lit id copy)
                                 invals regvals aignet2)
                       (id-eval id invals regvals aignet))))))


  (defthm eval-regin-of-aignet-copy-dfs
    (implies (and (< (nfix n) (num-regs aignet)))
             (let ((aignet2 (aignet-copy-dfs aignet aignet2 gatesimp)))
               (equal (id-eval (node-count
                                (lookup-reg->nxst
                                 (node-count (lookup-stype n (reg-stype) aignet2))
                                 aignet2))
                               in-vals reg-vals aignet2)
                      (id-eval (node-count
                                (lookup-reg->nxst
                                 (node-count (lookup-stype n (reg-stype) aignet))
                                 aignet))
                               in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (e/d* ()
                                    (aignet-copy-dfs-setup)))))

  (defthm num-outs-of-aignet-copy-dfs
    (equal (stype-count (po-stype) (aignet-copy-dfs aignet aignet2 gatesimp))
           (stype-count (po-stype) aignet)))

  (defthm num-regs-of-aignet-copy-dfs
    (equal (stype-count (reg-stype) (aignet-copy-dfs aignet aignet2 gatesimp))
           (stype-count (reg-stype) aignet)))

  (defthm aignet-copy-dfs-comb-equiv
    (comb-equiv (aignet-copy-dfs aignet aignet2 gatesimp)
                aignet)
    :hints(("Goal" :in-theory (e/d (comb-equiv)
                                   (aignet-copy-dfs))))))



(defsection aignet-mark-measure
  (local (defun aignet-mark-measure-ind (i n mark)
           (if (zp i)
               (list n mark)
             (aignet-mark-measure-ind (1- i) (1- (nfix n)) (cdr mark)))))

  (local (defthm aignet-mark-measure-lemma
           (implies (and (< (nfix i) (nfix n))
                         (not (equal 1 (nth i mark))))
                    (< (acl2::count-listp 1 mark n)
                       (acl2::count-listp 1 (update-nth i 1 mark) n)))
           :hints (("goal" :induct (aignet-mark-measure-ind i n mark)
                    :in-theory (e/d (update-nth nth)
                                    (acl2::zp-when-gt-0))))
           :rule-classes :linear))

  (local (defthm count-listp-<=-end
           (<= (acl2::count-listp a x e) (nfix e))
           :rule-classes :linear))

  (defund-nx aignet-mark-measure (mark aignet)
    (- (+ 1 (node-count aignet))
       (acl2::count-listp 1 mark (+ 1 (node-count aignet)))))

  (defthm natp-aignet-mark-measure
    (natp (aignet-mark-measure mark aignet))
    :hints(("Goal" :in-theory (enable aignet-mark-measure)))
    :rule-classes :type-prescription)

  ;; the above is stronger than the automatic type-prescription
  (in-theory (disable (:type-prescription aignet-mark-measure)))

  (defthm aignet-mark-measure-decr
    (implies (and (aignet-idp id aignet)
                  (not (equal 1 (nth id mark))))
             (< (aignet-mark-measure (update-nth id 1 mark) aignet)
                (aignet-mark-measure mark aignet)))
    :hints(("Goal" :in-theory (enable aignet-mark-measure
                                      aignet-idp)))
    :rule-classes (:rewrite :linear)))

(defsection aignet-mark-dfs-rec

  (defund aignet-mark-dfs-rec (id mark aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-nodes aignet) (bits-length mark))
                                (id-existsp id aignet))
                    :verify-guards nil
                    :measure (aignet-mark-measure mark aignet)))
    (b* (((when (mbe :logic
                     (or (not (id-existsp id aignet))
                         (int= 1 (get-bit id mark)))
                     :exec (int= 1 (get-bit id mark))))
          mark)
         (mark (set-bit id 1 mark))
         (type (id->type id aignet))
         ((when (or (int= type (in-type))
                    (int= type (const-type))))
          mark)
         ((when (int= type (out-type)))
          (aignet-mark-dfs-rec (lit-id (co-id->fanin id aignet))
                               mark aignet)))
      (mbe :logic
           (non-exec
            (b* ((mark1 (aignet-mark-dfs-rec
                                 (lit-id (gate-id->fanin0 id aignet))
                                 mark aignet))
                 ((unless (<= (aignet-mark-measure mark1 aignet)
                              (aignet-mark-measure mark aignet)))
                  mark1))
              (aignet-mark-dfs-rec
               (lit-id (gate-id->fanin1 id aignet))
               mark1 aignet)))
           :exec
           (b* ((mark (aignet-mark-dfs-rec
                               (lit-id (gate-id->fanin0 id aignet))
                               mark aignet)))
             (aignet-mark-dfs-rec
              (lit-id (gate-id->fanin1 id aignet))
              mark aignet)))))

  (local (in-theory (enable aignet-mark-dfs-rec)))

  (defthm aignet-mark-dfs-rec-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-rec id mark aignet)) 1)))

  (defthm aignet-mark-dfs-rec-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-rec id mark aignet)))
    :rule-classes :linear)

  (defthm aignet-mark-dfs-rec-decreases-measure-weak
    (<= (aignet-mark-measure (aignet-mark-dfs-rec id mark aignet) aignet)
        (aignet-mark-measure mark aignet))
    :rule-classes (:rewrite :linear))

  (defthm id-marked-of-aignet-mark-dfs-rec
    (implies (aignet-idp id aignet)
             (equal (nth id (aignet-mark-dfs-rec id mark aignet))
                    1)))

  (local (in-theory (disable len)))

  (defthm len-of-update-nth
    (<= (len x)
        (len (update-nth n v x)))
    :rule-classes :linear)
  
  (local (in-theory (disable acl2::len-update-nth1
                             acl2::len-update-nth)))

  (verify-guards aignet-mark-dfs-rec
    :guard-debug t
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp)))
            (and stable-under-simplificationp
                 '(:clause-processor stype-cp)))))


(defsection aignet-mark-comb-invar

  (defmacro gate-fanins-marked (id aignet mark)
    `(let ((look (lookup-id ,id ,aignet)))
       (and (equal (nth (lit-id
                         (aignet-lit-fix
                          (gate-node->fanin0 (car look))
                          (cdr look)))
                        ,mark)
                   1)
            (equal (nth (lit-id
                         (aignet-lit-fix
                          (gate-node->fanin1 (car look))
                          (cdr look)))
                        ,mark)
                   1))))

  (defmacro co-fanin-marked (id aignet mark)
    `(let ((look (lookup-id ,id ,aignet)))
       (equal (nth (lit-id
                    (aignet-lit-fix
                     (co-node->fanin (car look))
                     (cdr look)))
                   ,mark)
              1)))


  ;; The non-inductive, nicer invariant:
  ;;  -- For all nodes that are marked, their fanins are also marked.
  (defun-sk aignet-mark-comb-invar (mark aignet)
    (forall id
            (implies
             (and (aignet-idp id aignet)
                  (equal 1 (get-bit id mark)))
             (and (implies (equal (id->type id aignet) (gate-type))
                           (gate-fanins-marked id aignet mark))
                  (implies (equal (id->type id aignet) (out-type))
                           (co-fanin-marked id aignet mark)))))
    :rewrite :direct)

  (in-theory (disable aignet-mark-comb-invar))


  (local
   (defsection aignet-mark-comb-invar-inductive

     ;; The inductive invariant:
     ;; -- All nodes marked in the original are marked in the result
     ;; -- For all nodes marked in the result that were not
     ;;    marked in the original, their fanins are also marked
     ;;    in the result.
     (defun-sk aignet-mark-comb-invar1 (mark1 mark2 aignet)
       (forall
        id
        (and
         (implies
          (and (aignet-idp id aignet)
               (not (equal 1 (get-bit id mark1)))
               (equal 1 (get-bit id mark2)))
          (and (implies (equal (id->type id aignet) (gate-type))
                        (gate-fanins-marked id aignet mark2))
               (implies (equal (id->type id aignet) (out-type))
                        (co-fanin-marked id aignet mark2))))
         (implies (and (aignet-idp id aignet)
                       (equal 1 (get-bit id mark1)))
                  (equal (nth id mark2) 1))))
       :rewrite :direct)

     (in-theory (disable aignet-mark-comb-invar1))

     (defthm aignet-mark-comb-invar1-mark-preserved
       (implies (and (aignet-mark-comb-invar1 mark1 mark2 aignet)
                     (aignet-idp id aignet)
                     (equal 1 (get-bit id mark1)))
                (equal (nth id mark2) 1)))


     (defthmd aignet-mark-comb-invar1-transitive-lemma
       (implies (and (aignet-mark-comb-invar1 mark2 mark3 aignet)
                     (aignet-mark-comb-invar1 mark1 mark2 aignet)
                     (aignet-idp id aignet))
                (and
                 (implies
                  (and (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark3)))
                  (and (implies (equal (id->type id aignet) (gate-type))
                                (gate-fanins-marked id aignet mark3))
                       (implies (equal (id->type id aignet) (out-type))
                                (co-fanin-marked id aignet mark3))))
                 (implies (equal 1 (get-bit id mark1))
                          (equal (nth id mark3) 1))))
       :hints (("goal" :in-theory (disable aignet-mark-comb-invar1-necc)
                :use ((:instance aignet-mark-comb-invar1-necc)
                      (:instance aignet-mark-comb-invar1-necc
                       (mark1 mark2) (mark2 mark3))))))

     (defthm aignet-mark-comb-invar1-transitive
       (implies (and (aignet-mark-comb-invar1 mark1 mark2 aignet)
                     (aignet-mark-comb-invar1 mark2 mark3 aignet))
                (aignet-mark-comb-invar1 mark1 mark3 aignet))
       :hints (("goal" :in-theory (enable
                                   aignet-mark-comb-invar1-transitive-lemma)
                :expand ((aignet-mark-comb-invar1 mark1 mark3 aignet)))))


     (defthmd aignet-mark-comb-invar-special-gate-lemma
       (implies (and (aignet-mark-comb-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (gate-type))
                     (gate-fanins-marked id1 aignet mark2))
                (and
                 (implies
                  (and (aignet-idp id aignet)
                       (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark2)))
                  (and (implies (equal (id->type id aignet) (gate-type))
                                (gate-fanins-marked id aignet mark2))
                       (implies (equal (id->type id aignet) (out-type))
                                (co-fanin-marked id aignet mark2))))
                 (implies (and (aignet-idp id aignet)
                               (equal 1 (get-bit id mark1)))
                          (equal (nth id mark2) 1))))
       :hints (("goal"
                :in-theory (disable aignet-mark-comb-invar1-necc)
                :use
                ((:instance aignet-mark-comb-invar1-necc
                  (mark1 (update-nth id1 1 mark1)))))))


     (defthm aignet-mark-comb-invar-special-gate
       (implies (and (bind-free '((id1 . id)) (id1))
                     (aignet-mark-comb-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (gate-type))
                     (gate-fanins-marked id1 aignet mark2))
                (aignet-mark-comb-invar1 mark1 mark2 aignet))
       :hints (("goal"
                :expand ((aignet-mark-comb-invar1 mark1 mark2 aignet))
                :in-theory (enable aignet-mark-comb-invar-special-gate-lemma))))

     (defthmd aignet-mark-comb-invar-special-co-lemma
       (implies (and (aignet-mark-comb-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (out-type))
                     (co-fanin-marked id1 aignet mark2))
                (and
                 (implies
                  (and (aignet-idp id aignet)
                       (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark2)))
                  (and (implies (equal (id->type id aignet) (gate-type))
                                (gate-fanins-marked id aignet mark2))
                       (implies (equal (id->type id aignet) (out-type))
                                (co-fanin-marked id aignet mark2))))
                 (implies (and (aignet-idp id aignet)
                               (equal 1 (get-bit id mark1)))
                          (equal (nth id mark2) 1))))
       :hints (("goal"
                :in-theory (disable aignet-mark-comb-invar1-necc)
                :use
                ((:instance aignet-mark-comb-invar1-necc
                  (mark1 (update-nth id1 1 mark1)))))))


     (defthm aignet-mark-comb-invar-special-co
       (implies (and (bind-free '((id1 . id)) (id1))
                     (aignet-mark-comb-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (out-type))
                     (co-fanin-marked id1 aignet mark2))
                (aignet-mark-comb-invar1 mark1 mark2 aignet))
       :hints (("goal"
                :expand ((aignet-mark-comb-invar1 mark1 mark2 aignet))
                :in-theory (enable aignet-mark-comb-invar-special-co-lemma))))


     (defthm aignet-mark-comb-invar1-self
       (aignet-mark-comb-invar1 mark mark aignet)
       :hints (("goal" :in-theory (enable aignet-mark-comb-invar1))))

     (defthm aignet-mark-comb-invar1-mark-non-gate/co
       (implies (and (not (equal (id->type id aignet) (gate-type)))
                     (not (equal (id->type id aignet) (out-type))))
                (aignet-mark-comb-invar1 mark (update-nth id 1 mark) aignet))
       :hints (("goal" :in-theory (enable aignet-mark-comb-invar1))))

     (defthm aignet-mark-comb-invar1-mark-const
       (implies (equal (id->type id aignet) (const-type))
                (aignet-mark-comb-invar1 mark (update-nth id 1 mark) aignet))
       :hints (("goal" :in-theory (enable aignet-mark-comb-invar1))))

     (local (defthm stype-possibilities-comb
              (implies (and (not (equal (stype x) (gate-stype)))
                            (not (equal (ctype (stype x)) (in-ctype)))
                            (not (equal (ctype (stype x)) (out-ctype))))
                       (equal (stype x) (const-stype)))
              :hints(("Goal" :in-theory (enable stype stype-fix stypep)))))


     (defthm aignet-mark-comb-invar1-of-aignet-mark-dfs-rec
       (aignet-mark-comb-invar1
        mark
        (aignet-mark-dfs-rec id mark aignet)
        aignet)
       :hints (("goal" :induct (aignet-mark-dfs-rec id mark aignet)
                :in-theory (enable (:induction aignet-mark-dfs-rec))
                :expand ((aignet-mark-dfs-rec id mark aignet)))
               (and stable-under-simplificationp
                    '(:cases ((equal (id->type id aignet) 1))))))


     (defthmd aignet-mark-comb-invar-by-aignet-mark-comb-invar1-lemma
       (implies (and (aignet-mark-comb-invar mark1 aignet)
                     (aignet-mark-comb-invar1 mark1 mark2 aignet))
                (implies
                 (and (aignet-idp id aignet)
                      (equal 1 (get-bit id mark2)))
                 (and (implies (equal (id->type id aignet) (gate-type))
                               (gate-fanins-marked id aignet mark2))
                      (implies (equal (id->type id aignet) (out-type))
                               (co-fanin-marked id aignet mark2)))))
       :hints (("goal" :use ((:instance aignet-mark-comb-invar-necc
                              (mark mark1))
                             (:instance aignet-mark-comb-invar1-necc))
                :in-theory (disable aignet-mark-comb-invar1-necc
                                    aignet-mark-comb-invar-necc))))

     (defthm aignet-mark-comb-invar-by-aignet-mark-comb-invar1
       (implies (and (aignet-mark-comb-invar mark1 aignet)
                     (aignet-mark-comb-invar1 mark1 mark2 aignet))
                (aignet-mark-comb-invar mark2 aignet))
       :hints (("goal" :expand ((aignet-mark-comb-invar mark2 aignet))
                :in-theory
                (enable
                 aignet-mark-comb-invar-by-aignet-mark-comb-invar1-lemma))))))

  (local (defthm bit-equiv-of-equal-1
           (implies (and (bit-equiv x (double-rewrite y))
                         (syntaxp (not (equal x y))))
                    (equal (equal 1 y)
                           (equal 1 x)))))

  (defcong bits-equiv equal (aignet-mark-comb-invar mark aignet) 1
    :hints(("goal" :cases ((aignet-mark-comb-invar mark aignet)))
           (and stable-under-simplificationp
                (let* ((term (assoc 'aignet-mark-comb-invar clause))
                       (other-var (if (eq (cadr term) 'mark)
                                      'acl2::mark-equiv
                                    'mark)))
                  `(:expand (,term)
                    :use ((:instance aignet-mark-comb-invar-necc
                           (mark ,other-var)
                           (id ,(cons 'aignet-mark-comb-invar-witness
                                      (cdr term))))))))))

  (defthm aignet-mark-comb-invar-of-empty
    (aignet-mark-comb-invar nil aignet)
    :hints(("Goal" :in-theory (enable aignet-mark-comb-invar))))

  
  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-rec
    (implies (aignet-mark-comb-invar mark aignet)
             (aignet-mark-comb-invar
              (aignet-mark-dfs-rec id mark aignet)
              aignet)))

  (defthm aignet-mark-comb-invar-of-aignet-copy-dfs-setup
    (aignet-mark-comb-invar
     (mv-nth 0 (aignet-copy-dfs-setup aignet mark copy aignet2))
     aignet)
    :hints(("Goal" :in-theory (enable aignet-mark-comb-invar
                                      aignet-copy-dfs-setup)))))


(defsection aignet-mark-dfs-comb
  (defiteration aignet-mark-dfs-outs (mark aignet)
    (declare (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-nodes aignet) (bits-length mark)))))
    (aignet-mark-dfs-rec (outnum->id n aignet) mark aignet)
    :returns mark
    :index n
    :last (num-outs aignet))

  (in-theory (disable aignet-mark-dfs-outs))
  (local (in-theory (enable aignet-mark-dfs-outs)))

  (defthm outputs-marked-of-aignet-mark-dfs-outs-iter
    (implies (and (< (nfix n) (nfix m))
                  (<= (nfix m) (stype-count (po-stype) aignet)))
             (equal (nth (node-count (lookup-stype n (po-stype) aignet))
                         (aignet-mark-dfs-outs-iter m mark aignet))
                    1))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-outs-iter m mark aignet))))

  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-outs-iter
    (implies (and (aignet-mark-comb-invar mark aignet))
             (aignet-mark-comb-invar
              (aignet-mark-dfs-outs-iter m mark aignet)
              aignet))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-outs-iter m mark aignet))))

  (defthm aignet-mark-dfs-outs-iter-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-outs-iter m mark aignet)) 1))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-outs-iter m mark aignet))))

  (defthm aignet-mark-dfs-outs-iter-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-outs-iter m mark aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-outs-iter m mark aignet)))
    :rule-classes :linear)

  (defthm outputs-marked-of-aignet-mark-dfs-outs
    (implies (and (< (nfix n) (stype-count (po-stype) aignet)))
             (equal (nth (node-count (lookup-stype n (po-stype) aignet))
                         (aignet-mark-dfs-outs mark aignet))
                    1)))

  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-outs
    (implies (and (aignet-mark-comb-invar mark aignet))
             (aignet-mark-comb-invar
              (aignet-mark-dfs-outs mark aignet)
              aignet)))

  (defthm aignet-mark-dfs-outs-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-outs mark aignet)) 1)))

  (defthm aignet-mark-dfs-outs-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-outs mark aignet)))
    :rule-classes :linear)


  (defiteration aignet-mark-dfs-nxsts (mark aignet)
    (declare (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-nodes aignet) (bits-length mark)))))
    (aignet-mark-dfs-rec (reg-id->nxst (regnum->id n aignet) aignet) mark aignet)
    :returns mark
    :index n
    :last (num-regs aignet))

  (in-theory (disable aignet-mark-dfs-nxsts))
  (local (in-theory (enable aignet-mark-dfs-nxsts
                            (:induction aignet-mark-dfs-nxsts-iter))))

  (defthm nxsts-marked-of-aignet-mark-dfs-nxsts-iter
    (implies (and (< (nfix n) (nfix m))
                  (<= (nfix m) (stype-count (reg-stype) aignet)))
             (equal (nth (node-count
                          (lookup-reg->nxst
                           (node-count
                            (lookup-stype n (reg-stype) aignet))
                           aignet))
                         (aignet-mark-dfs-nxsts-iter m mark aignet))
                    1))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-nxsts-iter m mark aignet))))

  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-nxsts-iter
    (implies (and (aignet-mark-comb-invar mark aignet))
             (aignet-mark-comb-invar
              (aignet-mark-dfs-nxsts-iter m mark aignet)
              aignet))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-nxsts-iter m mark aignet))))

  (defthm aignet-mark-dfs-nxsts-iter-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-nxsts-iter m mark aignet)) 1))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-nxsts-iter m mark aignet))))

  (defthm aignet-mark-dfs-nxsts-iter-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-nxsts-iter m mark aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-nxsts-iter m mark aignet)))
    :rule-classes :linear)

  (defthm nxsts-marked-of-aignet-mark-dfs-nxsts
    (implies (and (< (nfix n) (stype-count (reg-stype) aignet)))
             (equal (nth (node-count
                          (lookup-reg->nxst
                           (node-count
                            (lookup-stype n (reg-stype) aignet))
                           aignet))
                         (aignet-mark-dfs-nxsts mark aignet))
                    1)))

  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-nxsts
    (implies (and (aignet-mark-comb-invar mark aignet))
             (aignet-mark-comb-invar
              (aignet-mark-dfs-nxsts mark aignet)
              aignet)))

  (defthm aignet-mark-dfs-nxsts-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-nxsts mark aignet)) 1)))

  (defthm aignet-mark-dfs-nxsts-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-nxsts mark aignet)))
    :rule-classes :linear)

  (local (in-theory (disable aignet-mark-dfs-outs
                             aignet-mark-dfs-nxsts)))

  (defund aignet-mark-dfs-comb (mark aignet)
    (declare (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-nodes aignet) (bits-length mark)))))
    (b* ((mark (aignet-mark-dfs-outs mark aignet)))
      (aignet-mark-dfs-nxsts mark aignet)))

  (local (in-theory (enable aignet-mark-dfs-comb)))


  (defthm nxsts-marked-of-aignet-mark-dfs-comb
    (implies (and (< (nfix n) (stype-count (reg-stype) aignet)))
             (equal (nth (node-count
                          (lookup-reg->nxst
                           (node-count
                            (lookup-stype n (reg-stype) aignet))
                           aignet))
                         (aignet-mark-dfs-comb mark aignet))
                    1)))

  (defthm outputs-marked-of-aignet-mark-dfs-comb
    (implies (and (< (nfix n) (stype-count (po-stype) aignet)))
             (equal (nth (node-count (lookup-stype n (po-stype) aignet))
                         (aignet-mark-dfs-comb mark aignet))
                    1)))

  (defthm aignet-mark-comb-invar-preserved-by-aignet-mark-dfs-comb
    (implies (and (aignet-mark-comb-invar mark aignet))
             (aignet-mark-comb-invar
              (aignet-mark-dfs-comb mark aignet)
              aignet)))

  (defthm aignet-mark-dfs-comb-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-comb mark aignet)) 1)))

  (defthm aignet-mark-dfs-comb-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-comb mark aignet)))
    :rule-classes :linear))



(defsection aignet-copy-marked

  
  ;; was originally going to create i/o nodes, but maybe not
       ;; :in (b* ((regp (int= (io-id->regp id aignet) 1))
       ;;          ((mv lit aignet2)
       ;;           (if regp
       ;;               (aignet-add-reg aignet2)
       ;;             (aignet-add-in aignet2)))
       ;;          (copy (set-lit id lit copy)))
       ;;       (mv copy strash aignet2))
       ;; :out (b* ((lit0 (snode-co->fanin slot0))
       ;;           (lit-copy (lit-copy lit0 copy))
       ;;           (regp (int= (io-id->regp id aignet) 1))
       ;;           ((unless regp)
       ;;            (b* ((aignet2 (aignet-add-out lit-copy aignet2)))
       ;;              (mv copy strash aignet2)))
       ;;           (ro (regin-id->ro id aignet))
       ;;           ((when (int= ro 0))
       ;;            ;; doesn't count as anything really
       ;;            (mv copy strash aignet2))
       ;;           (regnum (io-id->ionum ro aignet))
       ;;           (reg-id (regnum->id regnum aignet2))
       ;;           (aignet2 (aignet-add-regin lit-copy reg-id aignet2)))
       ;;        (mv copy strash aignet2))



  ;; Copy all CIs as well as any marked nodes, to maintain combinational equivalence
  (defiteration aignet-copy-marked (aignet mark copy strash gatesimp aignet2)
    (declare (xargs :stobjs (mark copy aignet strash aignet2)
                    :guard (and (<= (num-nodes aignet) (bits-length mark))
                                (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-ok
                                 (num-nodes aignet) copy aignet2)
                                (natp gatesimp))
                    :guard-hints (("goal" :in-theory (enable aignet-idp)))))
    (b* ((id n)
         (copyp (int= (get-bit id mark) 1))
         ((unless copyp)
          (mv copy strash aignet2))
         (slot0 (id->slot id 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate (b* ((lit0 (snode->fanin slot0))
                  (lit1 (gate-id->fanin1 id aignet))
                  ((mv lit strash aignet2)
                   (aignet-hash-and
                    (lit-copy lit0 copy)
                    (lit-copy lit1 copy)
                    gatesimp strash aignet2))
                  (copy (set-lit id lit copy)))
               (mv copy strash aignet2))
       ;; assumes inputs already taken care of
       :in (mv copy strash aignet2)
       ;; record literal, but do not build output
       :out (b* ((lit (snode->fanin slot0))
                 (copy (set-lit id (lit-copy lit copy) copy)))
              (mv copy strash aignet2))
       :const (b* ((copy (set-lit id (to-lit 0) copy)))
                (mv copy strash aignet2))))
    :returns (mv copy strash aignet2)
    :index n
    :last (num-nodes aignet))

  (in-theory (disable aignet-copy-marked))
  (local (in-theory (enable aignet-copy-marked)))

  (def-aignet-preservation-thms aignet-copy-marked-iter
    :stobjname aignet2)

  (def-aignet-preservation-thms aignet-copy-marked
    :stobjname aignet2)


  (defthm stype-counts-preserved-of-aignet-copy-marked-iter
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count
                     stype
                     (mv-nth 2
                             (aignet-copy-marked-iter
                              n aignet mark copy strash gatesimp aignet2)))
                    (stype-count stype aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter
                              n aignet mark copy strash gatesimp aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-marked
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count
                     stype
                     (mv-nth 2
                             (aignet-copy-marked
                              aignet mark copy strash gatesimp aignet2)))
                    (stype-count stype aignet2))))

  (defthm len-copies-of-aignet-copy-marked-iter
    (<= (len copy)
        (len (mv-nth 0 (aignet-copy-marked-iter
                        n aignet mark copy strash gatesimp aignet2))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter
             n aignet mark copy strash gatesimp aignet2)))
    :rule-classes :linear)

  (defthm len-copies-of-aignet-copy-marked
    (<= (len copy)
        (len (mv-nth 0 (aignet-copy-marked
                        aignet mark copy strash gatesimp aignet2))))
    :rule-classes :linear)


  (defthm nth-copy-preserved-by-aignet-copy-marked-iter
    (implies (or (equal (id->type idn aignet) (in-type))
                 (<= (nfix n) (nfix idn)))
             (b* (((mv copy1 & &)
                   (aignet-copy-marked-iter n aignet mark copy strash gatesimp aignet2)))
               (equal (nth-lit idn copy1)
                      (nth-lit idn copy))))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter n aignet mark copy strash gatesimp
                                          aignet2))))

  (defthm input-copies-preserved-by-aignet-copy-marked
    (implies (equal (id->type idn aignet) (in-type))
             (b* (((mv copy1 & &)
                   (aignet-copy-marked aignet mark copy strash gatesimp aignet2)))
               (equal (nth-lit idn copy1)
                      (nth-lit idn copy)))))

  (defthm aignet-copy-marked-iter-preserves-aignet-copies-ok
    (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (<= (nfix n) (+ 1 (node-count aignet))))
             (b* (((mv copy1 & aignet2)
                   (aignet-copy-marked-iter n aignet mark copy strash gatesimp aignet2)))
               (aignet-copies-ok (+ 1 (node-count aignet)) copy1 aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter n aignet mark copy strash gatesimp
                                          aignet2))))

  (defthm aignet-copy-marked-preserves-aignet-copies-ok
    (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2))
             (b* (((mv copy1 & aignet2)
                   (aignet-copy-marked aignet mark copy strash gatesimp aignet2)))
               (aignet-copies-ok (+ 1 (node-count aignet)) copy1 aignet2))))

  (defun-sk aignet-copy-marked-iter-invar (n aignet mark copy aignet2)
    (forall (id invals regvals)
            (implies (and (aignet-idp id aignet)
                          (equal (nth id mark) 1)
                          (or (equal (id->type id aignet) (in-type))
                              (< (nfix id) (nfix n))))
                     (and (aignet-idp (lit-id (nth-lit id copy)) aignet2)
                          (equal (lit-eval (nth-lit id copy)
                                           invals regvals aignet2)
                                 (id-eval id invals regvals aignet)))))
    :rewrite :direct)

  (in-theory (disable aignet-copy-marked-iter-invar))

  ;; (local (defthm lit-eval-of-mk-lit-of-lit-id
  ;;          (equal (lit-eval (mk-lit (lit-id lit) neg) invals regvals aignet)
  ;;                 (b-xor (b-xor neg (lit-neg lit))
  ;;                        (lit-eval lit invals regvals aignet)))
  ;;          :hints(("Goal" :expand ((:free (lit) (lit-eval lit invals regvals aignet)))))))

  (local (in-theory (disable 
                             nth-copy-preserved-by-aignet-copy-marked-iter)))




  (defthm aignet-copy-marked-invar-of-aignet-copy-dfs-setup
    (mv-let (mark copy aignet2)
      (aignet-copy-dfs-setup aignet nil nil aignet2)
      (declare (ignore mark))
      (aignet-copy-marked-iter-invar
       0 aignet mark2 copy aignet2))
    :hints(("Goal" :in-theory (e/d (aignet-copy-marked-iter-invar
                                    lit-eval id-eval
                                    aignet-copy-dfs-setup)))))

  (defthm aignet-copy-marked-iter-invar-preserved
    (implies (and (aignet-mark-comb-invar mark aignet)
                  (aignet-copy-marked-iter-invar 0 aignet mark copy
                                                      aignet2)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (<= (nfix n) (num-nodes aignet)))
             (b* (((mv copy & aignet2)
                   (aignet-copy-marked-iter n aignet mark copy strash gatesimp aignet2)))
               (aignet-copy-marked-iter-invar n aignet mark copy
                                                   aignet2)))
    :hints((acl2::just-induct-and-expand
            (aignet-copy-marked-iter n aignet mark copy strash gatesimp
                                          aignet2))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))
                  :do-not-induct t
                  :do-not '(generalize fertilize eliminate-destructors)))
           (and stable-under-simplificationp
                (let ((witness (acl2::find-call-lst
                                'aignet-copy-marked-iter-invar-witness
                                clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '(((mv-nth '0 ,witness) . id)
                              ((mv-nth '1 ,witness) . invals)
                              ((mv-nth '2 ,witness) . regvals))))))
           (and stable-under-simplificationp
                '(:cases ((< (nfix id) (+ -1 n)))
                  :expand ((id-eval id invals regvals aignet)
                           (id-eval (+ -1 n) invals regvals aignet))
                  :in-theory (enable lit-eval eval-and-of-lits)))))

  (defthm aignet-copy-marked-invar-preserved
    (implies (and (aignet-mark-comb-invar mark aignet)
                  (aignet-copy-marked-iter-invar 0 aignet mark copy
                                                      aignet2)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2))
             (b* (((mv copy & aignet2)
                   (aignet-copy-marked aignet mark copy strash gatesimp aignet2)))
               (aignet-copy-marked-iter-invar
                (+ 1 (node-count aignet)) aignet mark copy aignet2))))

  (defthm aignet-copy-marked-invar-preserved-rw
    (implies (and (aignet-mark-comb-invar mark aignet)
                  (aignet-copy-marked-iter-invar 0 aignet mark copy
                                                      aignet2)
                  (aignet-copies-ok (num-nodes aignet) copy aignet2))
             (b* (((mv copy & aignet2)
                   (aignet-copy-marked aignet mark copy strash gatesimp
                                            aignet2)))
               (implies (and (aignet-idp id aignet)
                             (equal (nth id mark) 1))
                        (equal (lit-eval (nth-lit id copy)
                                         invals regvals aignet2)
                               (id-eval id invals regvals aignet)))))
    :hints (("goal" :use aignet-copy-marked-invar-preserved
             :in-theory (e/d (aignet-idp)
                             (aignet-copy-marked-invar-preserved
                              aignet-copy-marked))))))


(defsection aignet-prune-comb

  (local (defthm stype-when-out-of-bounds
           (implies (< (node-count aignet) (nfix id))
                    (equal (stype (car (lookup-id id aignet)))
                           (const-stype)))
           :hints(("Goal" :in-theory (enable lookup-id)))))

  (defthm aignet-copy-marked-iter-invar-of-aignet-copy-outs
    (implies (aignet-copy-marked-iter-invar
              (+ 1 (node-count aignet))
              aignet mark copy aignet2)
             (aignet-copy-marked-iter-invar
              (+ 1 (node-count aignet))
              aignet mark copy
              (aignet-copy-outs aignet copy aignet2)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-copy-marked-iter-invar-of-aignet-copy-nxsts
    (implies (aignet-copy-marked-iter-invar
              (+ 1 (node-count aignet))
              aignet mark copy aignet2)
             (aignet-copy-marked-iter-invar
              (+ 1 (node-count aignet))
              aignet mark copy
              (aignet-copy-nxsts aignet copy aignet2)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            ;; (and stable-under-simplificationp
            ;;      (let ((witness (acl2::find-call-lst
            ;;                      'aignet-copy-marked-iter-invar-witness
            ;;                      clause)))
            ;;        `(:clause-processor
            ;;          (acl2::simple-generalize-cp
            ;;           clause '(((mv-nth '0 ,witness) . id)
            ;;                    ((mv-nth '1 ,witness) . invals)
            ;;                    ((mv-nth '2 ,witness) . regvals))))))
            ))

  (define aignet-prune-comb-aux (mark copy aignet
                                      (gatesimp :type (integer 0 *))
                                      strash aignet2)
    (b* (((mv mark copy aignet2)
          (aignet-copy-dfs-setup aignet mark copy aignet2))
         (mark (aignet-mark-dfs-outs mark aignet))
         (mark (aignet-mark-dfs-nxsts mark aignet))
         ((mv copy strash aignet2)
          (aignet-copy-marked
           aignet mark copy strash gatesimp aignet2))
         (aignet2 (aignet-copy-outs aignet copy aignet2))
         (aignet2 (aignet-copy-nxsts aignet copy aignet2)))
      (mv mark copy strash aignet2))

    ///

    (defthm aignet-copy-marked-invar-of-aignet-prune-comb-aux
      (b* (((mv mark copy & aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (aignet-copy-marked-iter-invar
         (+ 1 (node-count aignet))
         aignet mark copy aignet2)))

    (defthm aignet-outs-marked-of-aignet-prune-comb-aux
      (b* (((mv mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (implies (< (nfix n) (num-outs aignet))
                 (let ((id (node-count (lookup-stype n (po-stype) aignet))))
                   (equal (nth id mark) 1)))))

    (defthm aignet-nxsts-marked-of-aignet-prune-comb-aux
      (b* (((mv mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (implies (< (nfix n) (num-regs aignet))
                 (let ((id (node-count
                            (lookup-reg->nxst
                             (node-count (lookup-stype n (reg-stype) aignet))
                             aignet))))
                   (equal (nth id mark) 1)))))

    (defthm aignet-copies-ok-of-aignet-prune-comb-aux
      (b* (((mv ?mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)))

    (defthm eval-output-of-aignet-prune-comb-aux
      (b* (((mv ?mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (implies (< (nfix n) (num-outs aignet))
                 (equal (id-eval (node-count (lookup-stype n (po-stype) aignet2))
                                 invals regvals aignet2)
                        (id-eval (node-count (lookup-stype n (po-stype) aignet))
                                 invals regvals aignet)))))

    (defthm eval-nxst-of-aignet-prune-comb-aux
      (b* (((mv ?mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (implies (< (nfix n) (num-regs aignet))
                 (equal (id-eval (node-count
                                  (lookup-reg->nxst
                                   (node-count (lookup-stype n (reg-stype)
                                                             aignet2))
                                   aignet2))
                                 invals regvals aignet2)
                        (id-eval (node-count
                                  (lookup-reg->nxst
                                   (node-count (lookup-stype n (reg-stype)
                                                             aignet))
                                   aignet))
                                 invals regvals aignet)))))

    (defthm stype-counts-of-aignet-prune-comb-aux
      (b* (((mv ?mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (implies (member stype (list (po-stype)
                                     (pi-stype)
                                     (reg-stype)))
                 (equal (stype-count stype aignet2)
                        (stype-count stype aignet))))
      :hints ((and stable-under-simplificationp
                   '(:in-theory (enable aignet-copy-dfs-setup)))))

    (defthm comb-equiv-of-aignet-prune-comb-aux
      (b* (((mv ?mark ?copy & ?aignet2)
            (aignet-prune-comb-aux
             mark copy aignet gatesimp strash aignet2)))
        (comb-equiv aignet2 aignet))
      :hints(("Goal" :in-theory (e/d (comb-equiv)
                                     (aignet-prune-comb-aux))))))


  (define aignet-prune-comb (aignet aignet2 (gatesimp :type (integer 0 *)))
    (b* (((local-stobjs mark copy strash)
          (mv mark copy strash aignet2)))
      (aignet-prune-comb-aux mark copy aignet gatesimp strash aignet2))

    ///
    

    (defthm eval-output-of-aignet-prune-comb
      (b* ((aignet2
            (aignet-prune-comb aignet aignet2 gatesimp)))
        (implies (< (nfix n) (num-outs aignet))
                 (equal (id-eval (node-count (lookup-stype n (po-stype) aignet2))
                                 invals regvals aignet2)
                        (id-eval (node-count (lookup-stype n (po-stype) aignet))
                                 invals regvals aignet)))))

    (defthm eval-nxst-of-aignet-prune-comb
      (b* ((aignet2
            (aignet-prune-comb aignet aignet2 gatesimp)))
        (implies (< (nfix n) (num-regs aignet))
                 (equal (id-eval (node-count
                                  (lookup-reg->nxst
                                   (node-count (lookup-stype n (reg-stype)
                                                             aignet2))
                                   aignet2))
                                 invals regvals aignet2)
                        (id-eval (node-count
                                  (lookup-reg->nxst
                                   (node-count (lookup-stype n (reg-stype)
                                                             aignet))
                                   aignet))
                                 invals regvals aignet)))))

    (defthm stype-counts-of-aignet-prune-comb
      (implies (member stype (list (po-stype)
                                   (pi-stype)
                                   (reg-stype)))
               (equal (stype-count stype (aignet-prune-comb
                                          aignet aignet2 gatesimp))
                      (stype-count stype aignet))))

    (defthm comb-equiv-of-aignet-prune-comb
      (comb-equiv (aignet-prune-comb aignet aignet2 gatesimp)
                  aignet))))
  





(defsection aignet-mark-dfs-seq-rec

  (defund aignet-mark-dfs-seq-rec (id mark aignet)
    (declare (type (integer 0 *) id)
             (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-nodes aignet) (bits-length mark))
                                (id-existsp id aignet))
                    :verify-guards nil
                    :measure (aignet-mark-measure mark aignet)))
    (b* (((when (mbe :logic
                     (or (not (id-existsp id aignet))
                         (int= 1 (get-bit id mark)))
                     :exec (int= 1 (get-bit id mark))))
          mark)
         (mark (set-bit id 1 mark))
         (type (id->type id aignet)))
      (aignet-seq-case
       type (io-id->regp id aignet)
       :const mark
       :pi mark
       :co (aignet-mark-dfs-seq-rec
            (lit-id (co-id->fanin id aignet)) mark aignet)
       :reg (aignet-mark-dfs-seq-rec
             (reg-id->nxst id aignet) mark aignet)
       :gate
       (mbe :logic
            (non-exec
             (b* ((mark1 (aignet-mark-dfs-seq-rec
                          (lit-id (gate-id->fanin0 id aignet))
                          mark aignet))
                  ((unless (<= (aignet-mark-measure mark1 aignet)
                               (aignet-mark-measure mark aignet)))
                   mark1))
               (aignet-mark-dfs-seq-rec
                (lit-id (gate-id->fanin1 id aignet))
                mark1 aignet)))
            :exec
            (b* ((mark (aignet-mark-dfs-seq-rec
                        (lit-id (gate-id->fanin0 id aignet))
                        mark aignet)))
              (aignet-mark-dfs-seq-rec
               (lit-id (gate-id->fanin1 id aignet))
               mark aignet))))))

  (local (in-theory (enable aignet-mark-dfs-seq-rec)))

  (defthm aignet-mark-dfs-seq-rec-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-seq-rec id mark aignet)) 1)))

  (defthm aignet-mark-dfs-seq-rec-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-seq-rec id mark aignet)))
    :rule-classes :linear)

  (defthm aignet-mark-dfs-seq-rec-decreases-measure-weak
    (<= (aignet-mark-measure (aignet-mark-dfs-seq-rec id mark aignet) aignet)
        (aignet-mark-measure mark aignet))
    :rule-classes (:rewrite :linear))

  (defthm id-marked-of-aignet-mark-dfs-seq-rec
    (implies (aignet-idp id aignet)
             (equal (nth id (aignet-mark-dfs-seq-rec id mark aignet))
                    1)))

  (local (in-theory (disable len)))

  (defthm len-of-update-nth
    (<= (len x)
        (len (update-nth n v x)))
    :rule-classes :linear)
  
  (local (in-theory (disable acl2::len-update-nth1
                             acl2::len-update-nth)))

  (verify-guards aignet-mark-dfs-seq-rec
    :guard-debug t
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp)))
            (and stable-under-simplificationp
                 '(:clause-processor stype-cp)))))



(defsection aignet-mark-seq-invar

  ;; (defmacro gate-fanins-marked (id aignet mark)
  ;;   `(let ((look (lookup-id ,id ,aignet)))
  ;;      (and (equal (nth (lit-id
  ;;                        (aignet-lit-fix
  ;;                         (gate-node->fanin0 (car look))
  ;;                         (cdr look)))
  ;;                       ,mark)
  ;;                  1)
  ;;           (equal (nth (lit-id
  ;;                        (aignet-lit-fix
  ;;                         (gate-node->fanin1 (car look))
  ;;                         (cdr look)))
  ;;                       ,mark)
  ;;                  1))))

  ;; (defmacro co-fanin-marked (id aignet mark)
  ;;   `(let ((look (lookup-id ,id ,aignet)))
  ;;      (equal (nth (lit-id
  ;;                   (aignet-lit-fix
  ;;                    (co-node->fanin (car look))
  ;;                    (cdr look)))
  ;;                  ,mark)
  ;;             1)))

  (defmacro reg-nxst-marked (id aignet mark)
    `(let* ((nxst (node-count
                    (lookup-reg->nxst
                     ,id ,aignet))))
       (equal (nth nxst ,mark) 1)))


  ;; The non-inductive, nicer invariant:
  ;;  -- For all nodes that are marked, their fanins are also marked.
  (defun-sk aignet-mark-seq-invar (mark aignet)
    (forall id
            (implies
             (and (aignet-idp id aignet)
                  (equal 1 (get-bit id mark)))
             (and (implies (equal (id->type id aignet) (gate-type))
                           (gate-fanins-marked id aignet mark))
                  (implies (equal (id->type id aignet) (out-type))
                           (co-fanin-marked id aignet mark))
                  (implies (equal (stype (car (lookup-id id aignet)))
                                  (reg-stype))
                           (reg-nxst-marked id aignet mark)))))
    :rewrite :direct)

  (in-theory (disable aignet-mark-seq-invar))


;;  (local
   (defsection aignet-mark-seq-invar-inductive

     ;; The inductive invariant:
     ;; -- All nodes marked in the original are marked in the result
     ;; -- For all nodes marked in the result that were not
     ;;    marked in the original, their fanins are also marked
     ;;    in the result.
     (defun-sk aignet-mark-seq-invar1 (mark1 mark2 aignet)
       (forall
        id
        (and
         (implies
          (and (aignet-idp id aignet)
               (not (equal 1 (get-bit id mark1)))
               (equal 1 (get-bit id mark2)))
          (and (implies (equal (id->type id aignet) (gate-type))
                        (gate-fanins-marked id aignet mark2))
               (implies (equal (id->type id aignet) (out-type))
                        (co-fanin-marked id aignet mark2))
               (implies (equal (stype (car (lookup-id id aignet)))
                               (reg-stype))
                        (reg-nxst-marked id aignet mark2))))
         (implies (and (aignet-idp id aignet)
                       (equal 1 (get-bit id mark1)))
                  (equal (nth id mark2) 1))))
       :rewrite :direct)

     (in-theory (disable aignet-mark-seq-invar1))

     (defthm aignet-mark-seq-invar1-mark-preserved
       (implies (and (aignet-mark-seq-invar1 mark1 mark2 aignet)
                     (aignet-idp id aignet)
                     (equal 1 (get-bit id mark1)))
                (equal (nth id mark2) 1)))


     (defthmd aignet-mark-seq-invar1-transitive-lemma
       (implies (and (aignet-mark-seq-invar1 mark2 mark3 aignet)
                     (aignet-mark-seq-invar1 mark1 mark2 aignet)
                     (aignet-idp id aignet))
                (and
                 (implies
                  (and (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark3)))
                  (and (implies (equal (id->type id aignet) (gate-type))
                                (gate-fanins-marked id aignet mark3))
                       (implies (equal (id->type id aignet) (out-type))
                                (co-fanin-marked id aignet mark3))
                       (implies (equal (stype (car (lookup-id id aignet)))
                                       (reg-stype))
                                (reg-nxst-marked id aignet mark3))))
                 (implies (equal 1 (get-bit id mark1))
                          (equal (nth id mark3) 1))))
       :hints (("goal" :in-theory (disable aignet-mark-seq-invar1-necc)
                :use ((:instance aignet-mark-seq-invar1-necc)
                      (:instance aignet-mark-seq-invar1-necc
                       (mark1 mark2) (mark2 mark3))))))

     (defthm aignet-mark-seq-invar1-transitive
       (implies (and (aignet-mark-seq-invar1 mark1 mark2 aignet)
                     (aignet-mark-seq-invar1 mark2 mark3 aignet))
                (aignet-mark-seq-invar1 mark1 mark3 aignet))
       :hints (("goal" :in-theory (enable
                                   aignet-mark-seq-invar1-transitive-lemma)
                :expand ((aignet-mark-seq-invar1 mark1 mark3 aignet)))))


     (defthmd aignet-mark-seq-invar-special-gate-lemma
       (implies (and (aignet-mark-seq-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (gate-type))
                     (gate-fanins-marked id1 aignet mark2))
                (and
                 (implies
                  (and (aignet-idp id aignet)
                       (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark2)))
                  (and (implies (equal (id->type id aignet) (gate-type))
                                (gate-fanins-marked id aignet mark2))
                       (implies (equal (id->type id aignet) (out-type))
                                (co-fanin-marked id aignet mark2))
                       (implies (equal (stype (car (lookup-id id aignet)))
                                       (reg-stype))
                                (reg-nxst-marked id aignet mark2))))
                 (implies (and (aignet-idp id aignet)
                               (equal 1 (get-bit id mark1)))
                          (equal (nth id mark2) 1))))
       :hints (("goal"
                :in-theory (disable aignet-mark-seq-invar1-necc)
                :use
                ((:instance aignet-mark-seq-invar1-necc
                  (mark1 (update-nth id1 1 mark1)))))))


     (defthm aignet-mark-seq-invar-special-gate
       (implies (and (bind-free '((id1 . id)) (id1))
                     (aignet-mark-seq-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (gate-type))
                     (gate-fanins-marked id1 aignet mark2))
                (aignet-mark-seq-invar1 mark1 mark2 aignet))
       :hints (("goal"
                :expand ((aignet-mark-seq-invar1 mark1 mark2 aignet))
                :in-theory (enable aignet-mark-seq-invar-special-gate-lemma))))

     (defthmd aignet-mark-seq-invar-special-co-lemma
       (implies (and (aignet-mark-seq-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (out-type))
                     (co-fanin-marked id1 aignet mark2))
                (and
                 (implies
                  (and (aignet-idp id aignet)
                       (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark2)))
                  (and (implies (equal (id->type id aignet) (gate-type))
                                (gate-fanins-marked id aignet mark2))
                       (implies (equal (id->type id aignet) (out-type))
                                (co-fanin-marked id aignet mark2))
                       (implies (equal (stype (car (lookup-id id aignet)))
                                       (reg-stype))
                                (reg-nxst-marked id aignet mark2))))
                 (implies (and (aignet-idp id aignet)
                               (equal 1 (get-bit id mark1)))
                          (equal (nth id mark2) 1))))
       :hints (("goal"
                :in-theory (disable aignet-mark-seq-invar1-necc)
                :use
                ((:instance aignet-mark-seq-invar1-necc
                  (mark1 (update-nth id1 1 mark1)))))))


     (defthm aignet-mark-seq-invar-special-co
       (implies (and (bind-free '((id1 . id)) (id1))
                     (aignet-mark-seq-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (id->type id1 aignet) (out-type))
                     (co-fanin-marked id1 aignet mark2))
                (aignet-mark-seq-invar1 mark1 mark2 aignet))
       :hints (("goal"
                :expand ((aignet-mark-seq-invar1 mark1 mark2 aignet))
                :in-theory (enable aignet-mark-seq-invar-special-co-lemma))))

     (defthmd aignet-mark-seq-invar-special-reg-lemma
       (implies (and (aignet-mark-seq-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (stype (car (lookup-id id1 aignet)))
                            (reg-stype))
                     (reg-nxst-marked id1 aignet mark2))
                (and
                 (implies
                  (and (aignet-idp id aignet)
                       (not (equal 1 (get-bit id mark1)))
                       (equal 1 (get-bit id mark2)))
                  (and (implies (equal (id->type id aignet) (gate-type))
                                (gate-fanins-marked id aignet mark2))
                       (implies (equal (id->type id aignet) (out-type))
                                (co-fanin-marked id aignet mark2))
                       (implies (equal (stype (car (lookup-id id aignet)))
                                       (reg-stype))
                                (reg-nxst-marked id aignet mark2))))
                 (implies (and (aignet-idp id aignet)
                               (equal 1 (get-bit id mark1)))
                          (equal (nth id mark2) 1))))
       :hints (("goal"
                :in-theory (disable aignet-mark-seq-invar1-necc)
                :use
                ((:instance aignet-mark-seq-invar1-necc
                  (mark1 (update-nth id1 1 mark1)))))))


     (defthm aignet-mark-seq-invar-special-reg
       (implies (and (bind-free '((id1 . id)) (id1))
                     (aignet-mark-seq-invar1
                      (update-nth id1 1 mark1)
                      mark2 aignet)
                     (equal (stype (car (lookup-id id1 aignet)))
                            (reg-stype))
                     (reg-nxst-marked id1 aignet mark2))
                (aignet-mark-seq-invar1 mark1 mark2 aignet))
       :hints (("goal"
                :expand ((aignet-mark-seq-invar1 mark1 mark2 aignet))
                :in-theory (enable aignet-mark-seq-invar-special-reg-lemma))))

     (defthm aignet-mark-seq-invar1-self
       (aignet-mark-seq-invar1 mark mark aignet)
       :hints (("goal" :in-theory (enable aignet-mark-seq-invar1))))

     (defthm aignet-mark-seq-invar1-mark-non-gate/co/reg
       (implies (and (not (equal (id->type id aignet) (gate-type)))
                     (not (equal (id->type id aignet) (out-type)))
                     (not (equal (stype (car (lookup-id id aignet))) (reg-stype))))
                (aignet-mark-seq-invar1 mark (update-nth id 1 mark) aignet))
       :hints (("goal" :in-theory (enable aignet-mark-seq-invar1))))

     (defthm aignet-mark-seq-invar1-mark-const
       (implies (equal (id->type id aignet) (const-type))
                (aignet-mark-seq-invar1 mark (update-nth id 1 mark) aignet))
       :hints (("goal" :in-theory (enable aignet-mark-seq-invar1))))

     (local (defthm stype-possibilities-comb
              (implies (and (not (equal (stype x) (gate-stype)))
                            (not (equal (ctype (stype x)) (in-ctype)))
                            (not (equal (ctype (stype x)) (out-ctype))))
                       (equal (stype x) (const-stype)))
              :hints(("Goal" :in-theory (enable stype stype-fix stypep)))))


     (defthm aignet-mark-seq-invar1-of-aignet-mark-dfs-seq-rec
       (aignet-mark-seq-invar1
        mark
        (aignet-mark-dfs-seq-rec id mark aignet)
        aignet)
       :hints (("goal" :induct (aignet-mark-dfs-seq-rec id mark aignet)
                :in-theory (enable (:induction aignet-mark-dfs-seq-rec))
                :expand ((aignet-mark-dfs-seq-rec id mark aignet)))
               (and stable-under-simplificationp
                    '(:cases ((equal (id->type id aignet) 1))))))


     (defthmd aignet-mark-seq-invar-by-aignet-mark-seq-invar1-lemma
       (implies (and (aignet-mark-seq-invar mark1 aignet)
                     (aignet-mark-seq-invar1 mark1 mark2 aignet))
                (implies
                 (and (aignet-idp id aignet)
                      (equal 1 (get-bit id mark2)))
                 (and (implies (equal (id->type id aignet) (gate-type))
                               (gate-fanins-marked id aignet mark2))
                      (implies (equal (id->type id aignet) (out-type))
                               (co-fanin-marked id aignet mark2))
                      (implies (equal (stype (car (lookup-id id aignet)))
                                      (reg-stype))
                               (reg-nxst-marked id aignet mark2)))))
       :hints (("goal" :use ((:instance aignet-mark-seq-invar-necc
                              (mark mark1))
                             (:instance aignet-mark-seq-invar1-necc))
                :in-theory (disable aignet-mark-seq-invar1-necc
                                    aignet-mark-seq-invar-necc))))

     (defthm aignet-mark-seq-invar-by-aignet-mark-seq-invar1
       (implies (and (aignet-mark-seq-invar mark1 aignet)
                     (aignet-mark-seq-invar1 mark1 mark2 aignet))
                (aignet-mark-seq-invar mark2 aignet))
       :hints (("goal" :expand ((aignet-mark-seq-invar mark2 aignet))
                :in-theory
                (enable
                 aignet-mark-seq-invar-by-aignet-mark-seq-invar1-lemma)))))

  (local (defthm bit-equiv-of-equal-1
           (implies (and (bit-equiv x (double-rewrite y))
                         (syntaxp (not (equal x y))))
                    (equal (equal 1 y)
                           (equal 1 x)))))

  (defcong bits-equiv equal (aignet-mark-seq-invar mark aignet) 1
    :hints(("goal" :cases ((aignet-mark-seq-invar mark aignet)))
           (and stable-under-simplificationp
                (let* ((term (assoc 'aignet-mark-seq-invar clause))
                       (other-var (if (eq (cadr term) 'mark)
                                      'acl2::mark-equiv
                                    'mark)))
                  `(:expand (,term)
                    :use ((:instance aignet-mark-seq-invar-necc
                           (mark ,other-var)
                           (id ,(cons 'aignet-mark-seq-invar-witness
                                      (cdr term))))))))))

  (defthm aignet-mark-seq-invar-of-empty
    (aignet-mark-seq-invar nil aignet)
    :hints(("Goal" :in-theory (enable aignet-mark-seq-invar))))

  
  (defthm aignet-mark-seq-invar-preserved-by-aignet-mark-dfs-seq-rec
    (implies (aignet-mark-seq-invar mark aignet)
             (aignet-mark-seq-invar
              (aignet-mark-dfs-seq-rec id mark aignet)
              aignet)))

  (defthm aignet-mark-seq-invar-of-aignet-copy-dfs-setup
    (aignet-mark-seq-invar
     (mv-nth 0 (aignet-copy-dfs-setup aignet mark copy aignet2))
     aignet)
    :hints(("Goal" :in-theory (enable aignet-mark-seq-invar
                                      aignet-copy-dfs-setup)))))


(defsection aignet-mark-dfs-seq
  (defiteration aignet-mark-dfs-seq (mark aignet)
    (declare (xargs :stobjs (mark aignet)
                    :guard (and (<= (num-nodes aignet) (bits-length mark)))))
    (aignet-mark-dfs-seq-rec (outnum->id n aignet) mark aignet)
    :returns mark
    :index n
    :last (num-outs aignet))

  (in-theory (disable aignet-mark-dfs-seq))
  (local (in-theory (enable aignet-mark-dfs-seq)))

  (defthm outputs-marked-of-aignet-mark-dfs-seq-iter
    (implies (and (< (nfix n) (nfix m))
                  (<= (nfix m) (stype-count (po-stype) aignet)))
             (equal (nth (node-count (lookup-stype n (po-stype) aignet))
                         (aignet-mark-dfs-seq-iter m mark aignet))
                    1))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-seq-iter m mark aignet))))

  (defthm aignet-mark-seq-invar-preserved-by-aignet-mark-dfs-seq-iter
    (implies (and (aignet-mark-seq-invar mark aignet))
             (aignet-mark-seq-invar
              (aignet-mark-dfs-seq-iter m mark aignet)
              aignet))
    :hints((acl2::just-induct-and-expand
            (aignet-mark-dfs-seq-iter m mark aignet))))

  (defthm aignet-mark-dfs-seq-iter-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-seq-iter m mark aignet)) 1))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-seq-iter m mark aignet))))

  (defthm aignet-mark-dfs-seq-iter-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-seq-iter m mark aignet)))
    :hints ((acl2::just-induct-and-expand
             (aignet-mark-dfs-seq-iter m mark aignet)))
    :rule-classes :linear)

  (defthm outputs-marked-of-aignet-mark-dfs-seq
    (implies (and (< (nfix n) (stype-count (po-stype) aignet)))
             (equal (nth (node-count (lookup-stype n (po-stype) aignet))
                         (aignet-mark-dfs-seq mark aignet))
                    1)))

  (defthm aignet-mark-seq-invar-preserved-by-aignet-mark-dfs-seq
    (implies (and (aignet-mark-seq-invar mark aignet))
             (aignet-mark-seq-invar
              (aignet-mark-dfs-seq mark aignet)
              aignet)))

  (defthm aignet-mark-dfs-seq-preserves-mark
    (implies (equal 1 (nth n mark))
             (equal (nth n (aignet-mark-dfs-seq mark aignet)) 1)))

  (defthm aignet-mark-dfs-seq-preserves-memo-tablep
    (<= (len mark)
        (len (aignet-mark-dfs-seq mark aignet)))
    :rule-classes :linear))


(define marked-reg-count ((n :type (integer 0 *))
                           mark aignet)
  :guard (and (<= n (num-regs aignet))
              (<= (num-nodes aignet) (bits-length mark)))
  (b* (((when (zp n)) 0)
       (n (1- n))
       (reg (regnum->id n aignet)))
    (+ (get-bit reg mark)
       (marked-reg-count n mark aignet)))
  ///
  (defcong nat-equiv equal (marked-reg-count n mark aignet) 1)
  (defcong bits-equiv equal (marked-reg-count n mark aignet) 2)

  (defthm marked-reg-count-monotonic
    (implies (<= (nfix n) (nfix m))
             (<= (marked-reg-count n mark aignet)
                 (marked-reg-count m mark aignet))))

  (defthm marked-reg-count-monotonic-strong
    (implies (and (< (nfix n) (nfix m))
                  (equal 1 (nth (node-count (lookup-stype n :reg aignet)) mark)))
             (< (marked-reg-count n mark aignet)
                (marked-reg-count m mark aignet)))
    :hints (("goal" :use ((:instance marked-reg-count-monotonic
                           (n (+ 1 (nfix n)))))
             :expand ((marked-reg-count (+ 1 (nfix n)) mark aignet))
             :in-theory (e/d () (marked-reg-count-monotonic))))
    :rule-classes (:rewrite :linear)))



(defsection aignet-copy-marked-regs

  ;; Adds a aignet2 reg for every reg of aignet, and sets the copy
  (defiteration aignet-copy-marked-regs (aignet mark copy aignet2)
    (declare (xargs :stobjs (aignet mark copy aignet2)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (<= (num-nodes aignet) (bits-length mark)))))
    (b* ((ro (regnum->id n aignet))
         ((unless (int= (get-bit ro mark) 1))
          (mv copy aignet2))
         (reglit (mk-lit (num-nodes aignet2) 0))
         (aignet2 (aignet-add-reg aignet2))
         (copy (set-lit ro reglit copy)))
      (mv copy aignet2))
    :returns (mv copy aignet2)
    :last (num-regs aignet)
    :index n
    :package aignet::bla)


  (in-theory (disable aignet-copy-marked-regs))
  (local (in-theory (enable (:induction aignet-copy-marked-regs-iter)
                            aignet-copy-marked-regs)))

  (def-aignet-preservation-thms aignet-copy-marked-regs-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-marked-regs-iter n aignet mark copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-marked-regs-iter n aignet mark copy aignet2))
              (:free (copy) (aignet-copy-marked-regs-iter n aignet mark copy aignet2))
              (:free (aignet2) (aignet-copy-marked-regs-iter n aignet mark copy
                                                      aignet2))))
            '(:do-not-induct t))))

  (defthm stype-counts-preserved-of-aignet-copy-marked-regs-iter
    (implies (not (equal (stype-fix stype) (reg-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-marked-regs-iter
                                                  n aignet mark copy aignet2)))
                    (stype-count stype aignet2))))

  (defthm aignet-copy-size-of-aignet-copy-marked-regs-iter
    (implies (<= (num-nodes aignet) (lits-length copy))
             (< (node-count aignet)
                (len (mv-nth 0 (aignet-copy-marked-regs-iter n aignet mark copy
                                                      aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copies-ok-of-aignet-copy-marked-regs-iter
    (implies (aignet-copies-ok (num-nodes aignet) copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-marked-regs-iter n aignet mark copy aignet2)
               (aignet-copies-ok
                (+ 1 (node-count aignet))
                copy aignet2))))

  (local (defthmd dumb-num-regs-lemma
           (implies (<= n (stype-count (reg-stype) aignet))
                    (< (+ -1 n) (stype-count (reg-stype) aignet)))))


  (defthm num-regs-of-aignet-copy-marked-regs-iter
    (implies (<= (nfix n) (num-regs aignet))
             (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-marked-regs-iter
                                                        n aignet mark copy aignet2)))
                    (+ (marked-reg-count n mark aignet)
                       (stype-count (reg-stype) aignet2))))
    :hints(("Goal" :in-theory (enable marked-reg-count))))


  ;; (defthm node-count-of-aignet-copy-marked-regs-iter
  ;;   (implies (<= (nfix n) (num-regs aignet))
  ;;            (equal (node-count (mv-nth 1 (aignet-copy-marked-regs-iter
  ;;                                          n aignet mark copy aignet2)))
  ;;                   (+ (if (zp n)
  ;;                          0
  ;;                        (marked-reg-count mark (lookup-stype (1- n) (reg-stype) aignet)))
  ;;                      (node-count aignet2))))
  ;;   :hints(("Goal" :in-theory (enable marked-reg-count-of-lookup-stype))))

  (local (defthm <-of-minus-1
           (implies (<= n a)
                    (not (< a (+ -1 n))))))

  (local (defthm lookup-stype-of-new-node
           (implies (and (equal (nfix n) (stype-count stype aignet))
                         (equal (stype new-node) stype))
                    (equal (lookup-stype n
                                         stype
                                         (cons new-node aignet))
                           (cons new-node aignet)))
           :hints(("Goal" :in-theory (enable lookup-stype stype-count)))))

  (defthm lookup-copy-of-aignet-copy-marked-regs-iter
    (implies (and (aignet-idp id aignet)
                  (<= (nfix n) (num-regs aignet)))
             (b* (((mv aignet-copy-new ?aignet2-new)
                   (aignet-copy-marked-regs-iter n aignet mark copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (not (equal (io-id->regp id aignet) 1))
                              (not (equal (nth id mark) 1))
                              (<= (nfix n) (io-id->ionum id aignet)))
                          (get-lit id copy)
                        (mk-lit
                         (regnum->id (+ (marked-reg-count
                                         (io-id->ionum id aignet) mark aignet)
                                        (num-regs aignet2))
                                     aignet2-new)
                         0)))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((aignet-copy-marked-regs-iter
                             0 aignet mark copy aignet2))
                   :in-theory (enable lookup-stype-in-bounds)
                   :do-not nil
                   :do-not-induct t)))
    :otf-flg t)

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-marked-regs :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-marked-regs
    (implies (not (equal (stype-fix stype) (reg-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-marked-regs
                                                  aignet mark copy aignet2)))
                    (stype-count stype aignet2))))

  (defthm aignet-copy-size-of-aignet-copy-marked-regs
    (implies (<= (num-nodes aignet) (lits-length copy))
             (< (node-count aignet)
                (len (mv-nth 0 (aignet-copy-marked-regs aignet mark copy
                                                 aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copies-ok-of-aignet-copy-marked-regs
    (implies (aignet-copies-ok (num-nodes aignet) copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-marked-regs aignet mark copy aignet2)
               (aignet-copies-ok
                (+ 1 (node-count aignet))
                copy aignet2))))

  (defthm num-regs-of-aignet-copy-marked-regs
    (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-marked-regs
                                               aignet mark copy aignet2)))
           (+ (marked-reg-count (num-regs aignet) mark aignet)
              (stype-count (reg-stype) aignet2))))
  
  (defthm lookup-copy-of-aignet-copy-marked-regs
    (implies (aignet-idp id aignet)
             (b* (((mv aignet-copy-new ?aignet2-new)
                   (aignet-copy-marked-regs aignet mark copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (not (equal (io-id->regp id aignet) 1))
                              (not (equal (nth id mark) 1)))
                          (get-lit id copy)
                        (mk-lit
                         (regnum->id (+ (marked-reg-count
                                         (io-id->ionum id aignet) mark aignet)
                                        (num-regs aignet2))
                                     aignet2-new)
                         0)))))))


(defsection aignet-copy-marked-nxsts

  ;; Adds a aignet2 next state for every nextstate of aignet, and sets the copy
  (defiteration aignet-copy-marked-nxsts (aignet mark copy aignet2)
    (declare (xargs :stobjs (aignet mark copy aignet2)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (<= (num-nodes aignet) (bits-length mark))
                                (<= (marked-reg-count (num-regs aignet) mark aignet)
                                    (num-regs aignet2))
                                (aignet-copies-ok
                                 (num-nodes aignet) copy aignet2))
                    :verify-guards nil))
    (b* ((ro (regnum->id n aignet))
         ((unless (int= (get-bit ro mark) 1))
          (mv next-reg aignet2))
         (nxst (reg-id->nxst ro aignet))
         (ro2 (regnum->id next-reg aignet2))
         (fanin (get-lit nxst copy))
         (aignet2 (aignet-set-nxst fanin ro2 aignet2)))
      (mv (+ 1 next-reg) aignet2))
    :init-vals ((next-reg 0))
    :returns (mv next-reg aignet2)
    :iter-guard (eql next-reg (marked-reg-count n mark aignet))
    :top-returns aignet2
    :last (num-regs aignet)
    :index n
    :package aignet::bla)

  (in-theory (disable aignet-copy-marked-nxsts))
  (local (in-theory (enable aignet-copy-marked-nxsts)))
  
  (verify-guards aignet-copy-marked-nxsts-step$inline
    :hints (("goal" :use ((:instance marked-reg-count-monotonic-strong
                           (n n) (m (stype-count :reg aignet))))
             :in-theory (disable marked-reg-count-monotonic-strong)
             :do-not-induct t)))


  (verify-guards aignet-copy-marked-nxsts-tailrec
    :hints (("goal" :expand ((marked-reg-count (+ 1 n) mark aignet)))))

  (verify-guards aignet-copy-marked-nxsts$inline
    :hints (("goal" :expand ((marked-reg-count 0 mark aignet)))))

  (def-aignet-preservation-thms aignet-copy-marked-nxsts-iter
    :stobjname aignet2)
  (def-aignet-preservation-thms aignet-copy-marked-nxsts
    :stobjname aignet2))


(define aignet-prune-seq (aignet (gatesimp :type (integer 0 *)) aignet2)
  (b* (((local-stobjs mark copy strash)
        (mv mark copy strash aignet2))
       (mark (resize-bits (num-nodes aignet) mark))
       (copy (resize-lits (num-nodes aignet) copy))
       (mark (aignet-mark-dfs-seq mark aignet))
       (nregs (marked-reg-count (num-regs aignet) mark aignet))
       (aignet2 (aignet-init (num-outs aignet)
                             nregs
                             (num-ins aignet)
                             (num-nodes aignet)
                             aignet2))
       ((mv copy aignet2) (aignet-copy-ins aignet copy aignet2))
       ((mv copy aignet2) (aignet-copy-marked-regs aignet mark copy aignet2))
       ((mv copy strash aignet2)
        (aignet-copy-marked aignet mark copy strash gatesimp aignet2))
       (aignet2 (aignet-copy-marked-nxsts aignet mark copy aignet2))
       (aignet2 (aignet-copy-outs aignet copy aignet2)))
    (mv mark copy strash aignet2)))





;; (define stype-next (stype aignet)
;;   :non-executable t
;;   :verify-guards nil
;;   (cond ((atom aignet) aignet)
;;         ((stype-equiv (stype (car aignet)) stype)
;;          aignet)
;;         (t (stype-next stype (cdr aignet))))
;;   ///
;;   (defcong stype-equiv equal (stype-next stype aignet) 1)
;;   (defthm lookup-stype-redef
;;     (equal (lookup-stype n stype aignet)
;;            (cond ((atom aignet) aignet)
;;                  ((and (stype-equiv (stype (car aignet)) stype)
;;                        (equal (stype-count stype (cdr aignet))
;;                               (lnfix n)))
;;                   aignet)
;;                  (t (lookup-stype n stype (stype-next stype (cdr aignet))))))
;;     :hints(("Goal" :in-theory (enable lookup-stype)))
;;     :rule-classes ((:definition
;;                     :install-body nil
;;                     :clique (lookup-stype)
;;                     :controller-alist ((lookup-stype nil nil t)))))

;;   (defthm stype-count-of-stype-next
;;     (equal (stype-count stype (stype-next stype aignet))
;;            (stype-count stype aignet)))

;;   (defthm acl2-count-of-stype-next
;;     (<= (acl2-count (stype-next stype aignet)) (acl2-count aignet))
;;     :rule-classes :linear)

;;   (defthm aignet-extension-p-of-stype-next
;;     (aignet-extension-p aignet (stype-next stype aignet))
;;     :hints(("Goal" :in-theory (enable aignet-extension-p))))

;;   (defthm aignet-extension-p-of-stype-next-trans
;;     (implies (aignet-extension-p new orig)
;;              (aignet-extension-p new (stype-next stype orig)))
;;     :hints(("Goal" :in-theory (enable aignet-extension-p))))

;;   (add-aignet-lookup-fn (stype-next stype new))

;;   (defthm stype-next-preserves-aignet-extension
;;     (implies (aignet-extension-p new orig)
;;              (aignet-extension-p
;;               (stype-next stype new) (stype-next stype orig)))
;;     :hints(("Goal" :in-theory (enable aignet-extension-p)))))

;; (define count-marked-regs (mark aignet)
;;   :non-executable t
;;   :verify-guards nil
;;   (b* (((when (atom aignet)) 0)
;;        ((unless (and (equal (stype (car aignet)) (reg-stype))
;;                      (equal (nth (node-count aignet) mark) 1)))
;;         (count-marked-regs mark (stype-next (reg-stype) (cdr aignet)))))
;;     (+ 1 (count-marked-regs mark (stype-next (reg-stype) (cdr aignet)))))
;;   ///
;;   (defthm count-marked-regs-of-stype-next
;;     (equal (count-marked-regs mark (stype-next (reg-stype) aignet))
;;            (count-marked-regs mark aignet))
;;     :hints(("Goal" :in-theory (enable stype-next))))

;;   (defthm count-marked-regs-of-aignet-extension-bind-inverse
;;     (implies (aignet-extension-bind-inverse)
;;              (<= (count-marked-regs mark orig) (count-marked-regs mark new)))
;;     :rule-classes ((:linear :trigger-terms
;;                     ((count-marked-regs mark orig))))
;;     :hints(("Goal" :in-theory (e/d (aignet-extension-p))
;;             :induct (aignet-extension-p new orig) :do-not-induct t
;;             :expand ((count-marked-regs mark orig)
;;                      (count-marked-regs mark new))))))

  

;; (define lookup-marked-reg (n mark aignet)
;;   :non-executable t
;;   :verify-guards nil
;;   (b* (((when (atom aignet)) 0)
;;        ((when (and (equal (stype (car aignet)) (reg-stype))
;;                    (equal (nth (node-count aignet) mark) 1)
;;                    (equal (nfix n) (count-marked-regs mark (cdr aignet)))))
;;         aignet))
;;     (lookup-marked-reg n mark (stype-next (reg-stype) (cdr aignet))))
;;   ///
;;   (defthm aignet-extension-lookup-marked-reg
;;     (aignet-extension-p aignet (lookup-marked-reg n mark aignet))))
;;     :hints (("Goal" :induct t)
;;             (and stable-under-simplificationp)

;;   (add-aignet-lookup-fn (lookup-marked-reg n mark new)))

;;   (defthm lookup-marked-reg-of-stype-next
;;     (equal (lookup-marked-reg n mark (stype-next (reg-stype) aignet))
;;            (lookup-marked-reg n mark aignet))
;;     :hints(("Goal" :in-theory (enable stype-next))))

;;   (defthm lookup-marked-reg-nonempty
;;     (iff (< 0 (node-count (lookup-marked-reg n mark aignet)))
;;          (< (nfix n) (count-marked-regs mark aignet)))
;;     :hints(("Goal" :in-theory (enable count-marked-regs))))

;;   (defthm count-marked-regs-of-lookup-marked-reg
;;     (implies (< (nfix n) (count-marked-regs mark aignet))
;;              (equal (count-marked-regs mark (lookup-marked-reg
;;                                              n mark aignet))
;;                     (+ 1 (nfix n))))
;;     :hints(("Goal" :in-theory (enable count-marked-regs))))

;;   (defthm lookup-marked-reg-is-marked-reg
;;     (implies (< (nfix n) (count-marked-regs mark aignet))
;;              (let ((look (lookup-marked-reg n mark aignet)))
;;                (and (equal (stype (car look)) (reg-stype))
;;                     (equal (nth (node-count look) mark) 1))))
;;     :hints(("Goal" :in-theory (enable count-marked-regs))))

;;   (defthm lookup-marked-reg-of-count-marked-regs
;;     (implies (and (




;; (define nth-marked-reg (n marks aignet)


;; (define translate-marked-regvals (n marks regvals aignet)
;;   (if (zp n)
;;       nil
;;     (cons (nth 


;; ;; (define lookup-marked-reg (n 
    
       


;; ;; (define marked-reg-count (mark aignet)
;; ;;   :non-executable t
;; ;;   :verify-guards nil
;; ;;   (b* (((when (atom aignet))
;; ;;         0)
;; ;;        ((unless (and (equal (nth (node-count aignet) mark) 1)
;; ;;                      (equal (stype (car aignet)) (reg-stype))))
;; ;;         (marked-reg-count mark (cdr aignet))))
;; ;;     (+ 1 (marked-reg-count mark (cdr aignet))))

;; ;;   ///

;; ;;   (local (defthm rewrite-equal-1-under-bit-equiv
;; ;;            (implies (and (bit-equiv y (double-rewrite x))
;; ;;                          (syntaxp (not (equal x y))))
;; ;;                     (equal (equal x 1)
;; ;;                            (equal y 1)))))

;; ;;   (defcong bits-equiv equal (marked-reg-count mark aignet) 1)

;; ;;   (defthm marked-reg-count-when-aignet-extension-p
;; ;;     (implies (aignet-extension-p new old)
;; ;;              (<= (marked-reg-count mark old) (marked-reg-count mark new)))
;; ;;     :hints(("Goal" :in-theory (enable aignet-extension-p))))

;; ;;   (defthm marked-reg-count-when-aignet-extension-bind-inverse
;; ;;     (implies (aignet-extension-bind-inverse)
;; ;;              (<= (marked-reg-count mark orig) (marked-reg-count mark new)))
;; ;;     :rule-classes ((:linear :trigger-terms ((marked-reg-count mark orig)))))

;; ;;   (defthm stype-count-extension-thm
;; ;;     (implies (and (aignet-extension-p a b)
;; ;;                   (equal (stype-count stype a) (stype-count stype b))
;; ;;                   (equal (stype (car a)) stype)
;; ;;                   (equal (stype (car b)) stype))
;; ;;              (equal a b))
;; ;;     :hints(("Goal" :in-theory (enable aignet-extension-p
;; ;;                                       stype-count)))
;; ;;     :rule-classes nil)

;; ;;   (defthm stype-count-of-lookup-stype-full
;; ;;     (implies (< (nfix n) (stype-count stype aignet))
;; ;;              (equal (stype-count stype (lookup-stype n stype aignet))
;; ;;                     (+ 1 (nfix n))))
;; ;;     :hints(("Goal" :in-theory (enable lookup-stype))))

;; ;;   (defthmd marked-reg-count-of-lookup-stype-1
;; ;;     (implies (and (aignet-extension-p a (lookup-stype n (reg-stype) aignet))
;; ;;                   (< (nfix n) (num-regs aignet))
;; ;;                   (equal (stype-count (reg-stype) a) (+ 1 (nfix n))))
;; ;;              (equal (marked-reg-count mark a)
;; ;;                     (marked-reg-count mark (lookup-stype n (reg-stype)
;; ;;                                                          aignet))))
;; ;;     :hints(("Goal" :in-theory (enable aignet-extension-p)
;; ;;             :induct (marked-reg-count mark a))
;; ;;            (and stable-under-simplificationp
;; ;;                 '(:use ((:instance stype-count-extension-thm
;; ;;                          (a a) (b (lookup-stype n :reg aignet))
;; ;;                          (stype :reg)))))))

;; ;;   (defthm aignet-extensions-imply-one-extends-the-other-by-node-count
;; ;;     (implies (and (aignet-extension-p x a)
;; ;;                   (aignet-extension-p x b)
;; ;;                   (<= (node-count a) (node-count b)))
;; ;;              (aignet-extension-p b a))
;; ;;     :hints(("Goal" :in-theory (enable aignet-extension-p)))
;; ;;     :rule-classes nil)

;; ;;   (defthm aignet-extensions-imply-one-extends-the-other-by-stype-count
;; ;;     (implies (and (aignet-extension-p x a)
;; ;;                   (aignet-extension-p x b)
;; ;;                   (< (stype-count stype a) (stype-count stype b)))
;; ;;              (aignet-extension-p b a))
;; ;;     :hints(("Goal" :in-theory (enable aignet-extension-p)))
;; ;;     :rule-classes nil)

;; ;;   (local (defthm aignet-extension-p-lookup-stype-lemma
;; ;;            (implies (and (<= (nfix n) (nfix m))
;; ;;                          (< (nfix m) (stype-count stype aignet)))
;; ;;                     (aignet-extension-p (lookup-stype m stype aignet)
;; ;;                                         (lookup-stype n stype aignet)))
;; ;;            :hints(("Goal" :in-theory (enable aignet-extension-p
;; ;;                                              lookup-stype
;; ;;                                              stype-count)))))

;; ;;   (defthm aignet-extension-p-cdr-lookup-stype
;; ;;     (implies (and (< (nfix n) (nfix m))
;; ;;                   (< (nfix m) (stype-count stype aignet)))
;; ;;              (aignet-extension-p (cdr (lookup-stype m stype aignet))
;; ;;                                  (lookup-stype n stype aignet)))
;; ;;     :hints (("goal" :use (aignet-extension-p-lookup-stype-lemma
;; ;;                           stype-count-of-lookup-stype-full
;; ;;                           (:instance stype-count-of-lookup-stype-full
;; ;;                            (n m)))
;; ;;              :in-theory (e/d (aignet-extension-p)
;; ;;                              (aignet-extension-p-lookup-stype-lemma)))))

;; ;;   (defthmd marked-reg-count-of-lookup-stype
;; ;;     (implies (and (< (nfix n) (num-regs aignet))
;; ;;                   (not (zp n)))
;; ;;              (equal (marked-reg-count mark (lookup-stype n :reg aignet))
;; ;;                     (+ (bfix (nth (node-count (lookup-stype n :reg aignet))
;; ;;                                   mark))
;; ;;                        (marked-reg-count mark (lookup-stype (+ -1 n) :reg
;; ;;                                                             aignet)))))
;; ;;     :hints (("Goal" :use ((:instance marked-reg-count-of-lookup-stype-1
;; ;;                            (n (1- n))
;; ;;                            (a (cdr (lookup-stype n :reg aignet)))))
;; ;;             :in-theory (enable lookup-stype-in-bounds))))

;; ;;   (defthm marked-reg-count-when-no-regs
;; ;;     (implies (equal (stype-count :reg aignet) 0)
;; ;;              (equal (marked-reg-count mark aignet) 0))
;; ;;     :hints(("Goal" :in-theory (enable stype-count))))

;; ;;   (defthm marked-reg-count-of-lookup-stype-0
;; ;;     (implies (< 0 (num-regs aignet))
;; ;;              (equal (marked-reg-count mark (lookup-stype 0 :reg aignet))
;; ;;                     (bfix (nth (node-count (lookup-stype 0 :reg aignet))
;; ;;                                mark))))
;; ;;     :hints (("goal" :expand ((marked-reg-count mark (lookup-stype 0 :reg
;; ;;                                                                   aignet)))
;; ;;              :in-theory (enable lookup-stype-in-bounds)))))

;; ;; (define lookup-marked-reg (n mark aignet)
;; ;;   :non-executable t
;; ;;   :verify-guards nil
;; ;;   (b* (((when (atom aignet)) aignet)
;; ;;        ((unless (and (equal (nth (node-count aignet) mark) 1)
;; ;;                      (equal (stype (car aignet)) (reg-stype))
;; ;;                      (equal (nfix n) (marked-reg-count mark (cdr aignet)))))
;; ;;         (lookup-marked-reg n mark (cdr aignet))))
;; ;;     aignet)
;; ;;   ///
;; ;;   (local (defthm rewrite-equal-1-under-bit-equiv
;; ;;            (implies (and (bit-equiv y (double-rewrite x))
;; ;;                          (syntaxp (not (equal x y))))
;; ;;                     (equal (equal x 1)
;; ;;                            (equal y 1)))))
;; ;;   (defcong nat-equiv equal (lookup-marked-reg n mark aignet) 1)
;; ;;   (defcong bits-equiv equal (lookup-marked-reg n mark aignet) 2)

;; ;;   (defthm marked-reg-count-of-lookup-marked-reg
;; ;;     (implies (< 0 (node-count (lookup-marked-reg n mark aignet)))
;; ;;              (equal (marked-reg-count mark (cdr (lookup-marked-reg n mark aignet)))
;; ;;                     (nfix n))))

;; ;;   (defthm lookup-marked-reg-aignet-extension-p
;; ;;     (aignet-extension-p aignet (lookup-marked-reg n mark aignet))
;; ;;     :hints(("Goal" :in-theory (enable aignet-extension-p))))

  
;; ;;   (defthm marked-reg-count-when-lookup
;; ;;     (iff (< 0 (node-count (lookup-marked-reg n mark aignet)))
;; ;;          (< (nfix n) (marked-reg-count mark aignet)))
;; ;;     :hints(("Goal" :in-theory (enable marked-reg-count))))

;; ;;   (defthm car-of-lookup-marked-reg
;; ;;     (implies (< (nfix n) (marked-reg-count mark aignet))
;; ;;              (and (equal (stype (car (lookup-marked-reg n mark aignet)))
;; ;;                          (reg-stype))
;; ;;                   (equal (nth (node-count (lookup-marked-reg n mark aignet))
;; ;;                               mark)
;; ;;                          1)))
;; ;;     :hints(("Goal" :in-theory (enable marked-reg-count))))

;; ;;   (defthm lookup-marked-reg-of-marked-reg-count
;; ;;     (implies (and (aignet-extension-p aignet suffix)
;; ;;                   (equal (nth (node-count suffix) mark) 1)
;; ;;                   (equal (stype (car suffix)) (reg-stype)))
;; ;;              (equal (lookup-marked-reg (marked-reg-count mark (cdr suffix))
;; ;;                                        mark aignet)
;; ;;                     suffix))
;; ;;     :hints(("Goal" :in-theory (enable aignet-extension-p
;; ;;                                       marked-reg-count))
;; ;;            (and stable-under-simplificationp
;; ;;                 '(:use ((:instance marked-reg-count-when-aignet-extension-p
;; ;;                          (old suffix) (new (cdr aignet))))
;; ;;                   :in-theory (e/d (marked-reg-count)
;; ;;                                   (marked-reg-count-when-aignet-extension-p
;; ;;                                       marked-reg-count-when-aignet-extension-bind-inverse)))))))
       
    




;; (defsection aignet-copy-marked-nxsts


;;   ;; Adds a aignet2 regin for every register of aignet.
;;   ;; assumes the copy of each regin ID is set to the fanin lit,
;;   ;; does not change this to the new node.
;;   ;; Connects the regin to the corresponding reg in aignet2.  Therefore, we must
;;   ;; assume there are at least as many regs in aignet2 as in aignet.
;;   (defiteration aignet-copy-marked-nxsts (aignet mark copy aignet2)
;;     (declare (xargs :stobjs (aignet mark copy aignet2)
;;                     :guard (and (<= (num-nodes aignet) (lits-length copy))
;;                                 (<= (num-nodes aignet) (bits-length mark))
;;                                 (<= (num-regs aignet) (num-regs aignet2))
;;                                 (aignet-copies-ok (num-nodes aignet)
;;                                                   copy aignet2))))
;;     (b* ((reg (regnum->id n aignet))
;;          ((unless (int= (get-bit reg mark) 1))
;;           aignet2)
;;          (nxst (reg-id->nxst reg aignet))
;;          (fanin-copy (get-lit nxst copy))
;;          (ro-copy (regnum->id n aignet2)))
;;       (aignet-set-nxst fanin-copy ro-copy aignet2))
;;     :returns aignet2
;;     :last (num-regs aignet)
;;     :index n
;;     :package aignet::bla)

;;   (in-theory (disable aignet-copy-marked-nxsts))
;;   (local (in-theory (enable (:induction aignet-copy-marked-nxsts-iter)
;;                             aignet-copy-marked-nxsts)))

;;   (def-aignet-preservation-thms aignet-copy-marked-nxsts-iter :stobjname aignet2)

;;   (local (set-default-hints
;;           '((acl2::just-induct-and-expand
;;              (aignet-copy-marked-nxsts-iter n aignet mark copy aignet2)
;;              :expand-others
;;              ((:free (aignet) (aignet-copy-marked-nxsts-iter n aignet mark copy aignet2))
;;               (:free (copy) (aignet-copy-marked-nxsts-iter n aignet mark copy aignet2))
;;               (:free (aignet2) (aignet-copy-marked-nxsts-iter n aignet mark copy
;;                                                      aignet2))))
;;             '(:do-not-induct t))))
  
;;   (defthm stype-counts-preserved-of-aignet-copy-marked-nxsts-iter
;;     (implies (not (equal (stype-fix stype) (nxst-stype)))
;;              (equal (stype-count stype
;;                                  (aignet-copy-marked-nxsts-iter n aignet mark copy aignet2))
;;                     (stype-count stype aignet2))))

;;   (local (in-theory (enable aignet-extension-implies-node-count-gte
;;                             lookup-stype-in-bounds)))

;;   (defthm lookup-nxst-of-aignet-copy-marked-nxsts-iter
;;     (implies (and (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
;;                   (<= (nfix n) (num-regs aignet))
;;                   (<= (num-regs aignet) (num-regs aignet2))
;;                   (< (nfix m) (nfix n)))
;;              (b* ((aignet21 (aignet-copy-marked-nxsts-iter n aignet mark copy aignet2))
;;                   (regid (node-count (lookup-stype m (reg-stype) aignet2)))
;;                   (mth-nxst-look2 (lookup-reg->nxst regid aignet21))
;;                   (mth-nxst-look (lookup-reg->nxst
;;                                   (node-count (lookup-stype m (reg-stype) aignet))
;;                                   aignet))
;;                   (fanin (nth-lit (node-count mth-nxst-look)
;;                                   copy)))
;;                (and (consp mth-nxst-look2)
;;                     (equal (car mth-nxst-look2)
;;                            (nxst-node fanin regid))
;;                     (aignet-litp fanin (cdr mth-nxst-look2))
;;                     (aignet-idp regid (cdr mth-nxst-look2)))))
;;     :hints ((and stable-under-simplificationp
;;                  '(:expand ((:free (n stype a b)
;;                              (lookup-stype n stype (cons a b)))
;;                             (:free (n a b)
;;                              (lookup-reg->nxst n (cons a b))))))))

;;   (local (set-default-hints nil))

;;   (def-aignet-preservation-thms aignet-copy-marked-nxsts :stobjname aignet2)

;;   (defthm stype-counts-preserved-of-aignet-copy-marked-nxsts
;;     (implies (not (equal (stype-fix stype) (nxst-stype)))
;;              (equal (stype-count stype
;;                                  (aignet-copy-marked-nxsts aignet mark copy aignet2))
;;                     (stype-count stype aignet2))))

;;   (defthm lookup-nxst-of-aignet-copy-marked-nxsts
;;     (implies (and (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
;;                   (< (nfix m) (num-regs aignet))
;;                   (<= (num-regs aignet) (num-regs aignet2)))
;;              (b* ((aignet21 (aignet-copy-marked-nxsts aignet mark copy aignet2))
;;                   (regid (node-count (lookup-stype m (reg-stype) aignet2)))
;;                   (mth-nxst-look2 (lookup-reg->nxst regid aignet21))
;;                   (mth-nxst-look (lookup-reg->nxst
;;                                   (node-count (lookup-stype m (reg-stype) aignet))
;;                                   aignet))
;;                   (fanin (nth-lit (node-count mth-nxst-look)
;;                                   copy)))
;;                (and (consp mth-nxst-look2)
;;                     (equal (car mth-nxst-look2)
;;                            (nxst-node fanin regid))
;;                     (aignet-litp fanin (cdr mth-nxst-look2))
;;                     (aignet-idp regid (cdr mth-nxst-look2)))))))




