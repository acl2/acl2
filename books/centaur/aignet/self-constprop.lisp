; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2018 Centaur Technology
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

(include-book "copying")
(local (include-book "std/lists/resize-list" :dir :system ))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/nth" :dir :System))
(local (include-book "std/util/termhints" :dir :System))
(local (in-theory (disable nth update-nth nfix ifix (tau-system)
                           resize-list
                           acl2::resize-list-when-atom
                           ;; acl2::resize-list-when-empty
                           )))
(local (std::add-default-post-define-hook :fix))


(defstobj-clone vals bitarr :strsubst (("BIT" . "AIGNET-VAL")))
(defstobj-clone constmarks bitarr :strsubst (("BIT" . "AIGNET-CONSTMARKS")))





(define lit-directly-implies ((parent-lit litp)
                              (child-lit litp)
                              aignet)
  :guard (and (fanin-litp parent-lit aignet)
              (fanin-litp child-lit aignet))
  :measure (lit-id (aignet-lit-fix parent-lit aignet))
  :prepwork ((local (in-theory (disable lookup-id-out-of-bounds
                                        lookup-id-in-bounds-when-positive
                                        satlink::equal-of-lit-fix-backchain))))
  :hooks nil
  (b* ((parent-lit (mbe :logic (non-exec (aignet-lit-fix parent-lit aignet)) :exec parent-lit))
       (child-lit (mbe :logic (non-exec (aignet-lit-fix child-lit aignet)) :exec child-lit))
       ((when (int= (lit-fix parent-lit) (lit-fix child-lit))) t)
       ((when (int= (lit->neg parent-lit) 1)) nil)
       (parent-id (lit->var parent-lit))
       ((unless (and (int= (id->type parent-id aignet) (gate-type))
                     (eql 0 (id->regp parent-id aignet))))
        nil))
    (or (lit-directly-implies (gate-id->fanin0 parent-id aignet) child-lit aignet)
        (lit-directly-implies (gate-id->fanin1 parent-id aignet) child-lit aignet)))
  ///
  (local (in-theory (enable lit-eval-of-aignet-lit-fix)))

  (local (defthm equal-of-lit-fix-fwd
           (implies (equal (lit-fix x) y)
                    (lit-equiv x y))
           :rule-classes :forward-chaining))

  (defthm lit-directly-implies-of-aignet-lit-fix-parent
    (equal (lit-directly-implies (aignet-lit-fix parent-lit aignet) child-lit aignet)
           (lit-directly-implies parent-lit child-lit aignet)))
  (defthm lit-directly-implies-of-aignet-lit-fix-child
    (equal (lit-directly-implies parent-lit (aignet-lit-fix child-lit aignet) aignet)
           (lit-directly-implies parent-lit child-lit aignet)))

  (fty::deffixequiv lit-directly-implies
    :hints (("goal" :induct (lit-directly-implies parent-lit child-lit aignet)
                         :expand ((:free (child-lit aignet) (lit-directly-implies parent-lit child-lit aignet))
                                  (:free (child-lit aignet) (lit-directly-implies (lit-fix parent-lit) child-lit aignet))))))

  (local
   (defthmd not-lit-directly-implies-when-lit-eval-lemma
     (implies (and (aignet-litp parent-lit aignet)
                   (aignet-litp child-lit aignet))
              (implies (and (equal 1 (lit-eval parent-lit invals regvals aignet))
                            (equal 0 (lit-eval child-lit invals regvals aignet)))
                       (not (lit-directly-implies parent-lit child-lit aignet))))
     :hints (("goal" :induct (lit-directly-implies parent-lit child-lit aignet))
             (and stable-under-simplificationp
                  '(:expand ((lit-eval parent-lit invals regvals aignet)
                             (id-eval (lit->var parent-lit) invals regvals aignet))
                    :in-theory (enable eval-and-of-lits))))))

  (defthm not-lit-directly-implies-when-lit-eval
    (implies (and (equal 1 (lit-eval parent-lit invals regvals aignet))
                  (equal 0 (lit-eval child-lit invals regvals aignet)))
             (not (lit-directly-implies parent-lit child-lit aignet)))
    :hints (("goal" :use ((:instance not-lit-directly-implies-when-lit-eval-lemma
                           (parent-lit (aignet-lit-fix parent-lit aignet))
                           (child-lit (aignet-lit-fix child-lit aignet)))))))

  (defthm lit-directly-implies-transitive
    (implies (and (lit-directly-implies a b aignet)
                  (lit-directly-implies b c aignet))
             (lit-directly-implies a c aignet))
    :hints (("goal" :induct (lit-directly-implies a b aignet)
             :expand ((:free (b) (lit-directly-implies a b aignet)))))))



(define aignet-mark-const-nodes-rec ((lit litp :type (integer 0 *))
                                     aignet
                                     mark
                                     vals)
  :guard (and (fanin-litp lit aignet)
              (< (lit-id lit) (bits-length mark))
              (< (lit-id lit) (bits-length vals)))
  :split-types t
  :measure (lit->var (aignet-lit-fix lit aignet))
  :returns (mv new-mark new-vals)
  :verify-guards nil
  (b* ((lit (mbe :logic (non-exec (aignet-lit-fix lit aignet)) :exec lit))
       (id (lit->var lit))
       ((when (int= (get-bit id mark) 1))
        (mv mark vals))
       (slot0 (id->slot id 0 aignet))
       (type (snode->type slot0))
       ((when (int= type (in-type)))
        (b* ((mark (set-bit id 1 mark))
             (vals (set-bit id (b-not (lit->neg lit)) vals)))
          (mv mark vals)))
       ((unless (int= type (gate-type)))
        (mv mark vals))

       (slot1 (id->slot id 1 aignet))
       (xor (snode->regp slot1))
       ((when (or (int= (lit->neg lit) 1)
                  (int= xor 1)))
        ;; can't go through a negated AND or an xor
        (mv mark vals))
       
       (mark (set-bit id 1 mark))

       ((mv mark vals) (aignet-mark-const-nodes-rec (snode->fanin slot0) aignet mark vals)))
    (aignet-mark-const-nodes-rec (snode->fanin slot1) aignet mark vals))
  ///

  ;; (defun-sk aignet-mark-const-nodes-invar-cond (lit mark new-mark new-vals aignet)
  ;;   (forall id
  ;; (implies (and (equal (get-bit id new-mark) 1)
  ;;                         (equal (get-bit id mark) 0))
  ;;                    (lit-directly-implies lit
  ;;                                          (lit-negate-cond id (get-bit id new-vals))
  ;;                                          aignet)))
  ;;   :rewrite :direct)

  (local (in-theory (disable (:d aignet-mark-const-nodes-rec))))

  (local (defthm equal-1-bit-equiv-congruence
           (implies (bit-equiv a b)
                    (equal (equal 1 a) (equal 1 b)))
           :rule-classes :congruence))

  (defret aignet-mark-const-nodes-rec-preserves-marked-nodes
    (implies (bit-equiv (nth n mark) 1)
             (bit-equiv (nth n new-mark) 1))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (defret aignet-mark-const-nodes-rec-preserves-marked-node-vals
    (implies (bit-equiv (nth n mark) 1)
             (equal (nth n new-vals)
                    (nth n vals)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (local (defthm lit-fix-equal-make-lit
           (equal (equal (lit-fix lit) (make-lit (lit->var lit) neg))
                  (equal (bfix neg) (lit->neg lit)))
           :hints(("Goal" :in-theory (enable satlink::equal-of-make-lit)))))

  (local (defthm b-not-when-not-1
           (implies (not (equal x 1))
                    (equal (b-not x) 1))
           :hints(("Goal" :in-theory (enable b-not)))))

  (defret aignet-mark-const-nodes-invar
    (implies (and (equal (get-bit id new-mark) 1)
                  (equal (get-bit id mark) 0)
                  (equal (id->type id aignet) (in-type)))
             (lit-directly-implies lit
                                   (make-lit id (b-not (get-bit id new-vals)))
                                   aignet))
    :hints(("Goal" :induct <call>
            :expand (<call>
                     (:free (child) (lit-directly-implies lit child aignet))))))

  (defret aignet-mark-const-nodes-invar-implies-eval
    (implies (and (equal (get-bit id new-mark) 1)
                  (equal (get-bit id mark) 0)
                  (equal (id->type id aignet) (in-type))
                  (equal 1 (lit-eval lit invals regvals aignet)))
             (bit-equiv (nth id new-vals)
                        (id-eval id invals regvals aignet)))
    :hints (("goal" :use ((:instance aignet-mark-const-nodes-invar))
             :in-theory (e/d (bfix) (aignet-mark-const-nodes-invar))
             :expand ((:free (neg) (lit-eval (make-lit id neg) invals regvals aignet)))
             :do-not-induct t)))

  (defret mark-length-of-<fn>
    (<= (len mark) (len new-mark))
    :hints ((acl2::just-induct-and-expand <call>))
    :rule-classes :linear)

  (defret vals-length-of-<fn>
    (<= (len vals) (len new-vals))
    :hints ((acl2::just-induct-and-expand <call>))
    :rule-classes :linear)

  (local (defthm len-update-nth-when-greater
           (implies (< (nfix n) (len x))
                    (equal (len (update-nth n v x))
                           (len x)))))

  (verify-guards aignet-mark-const-nodes-rec
    :hints (("goal" :do-not-induct t)))

  (defret aignet-mark-const-nodes-rec-of-aignet-lit-fix
    (equal (let ((lit (aignet-lit-fix lit aignet))) <call>)
           <call>)
    :hints (("goal" :expand ((:free (lit) <call>))))))
                             



(define aignet-self-constprop-init-pis ((n natp :type (integer 0 *))
                                        mark
                                        vals
                                        aignet
                                        copy)
  :guard (and (<= n (num-ins aignet))
              (< (max-fanin aignet) (bits-length mark))
              (< (max-fanin aignet) (bits-length vals))
              (< (max-fanin aignet) (lits-length copy)))
  :returns (new-copy)
  :verify-guards nil
  :measure (nfix (- (num-ins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (int= n (num-ins aignet))))
        copy)
       (id (innum->id n aignet))
       ((unless (int= (get-bit id mark) 1))
        (b* ((copy (set-lit id (mk-lit id 0) copy)))
          (aignet-self-constprop-init-pis (1+ (lnfix n)) mark vals aignet copy)))
       (copy (set-lit id (mk-lit 0 (get-bit id vals)) copy)))
    (aignet-self-constprop-init-pis (1+ (lnfix n)) mark vals aignet copy))
  ///
  (local (in-theory (disable (:d aignet-self-constprop-init-pis))))

  (defret nth-of-<fn>
    (equal (nth-lit k new-copy)
           (if (and (equal (id->type k aignet) (in-type))
                    (equal (id->regp k aignet) 0)
                    (<= (nfix n) (io-id->ionum k aignet)))
               (if (eql 1 (nth k mark))
                       (mk-lit 0 (get-bit k vals))
                 (mk-lit k 0))
             (nth-lit k copy)))
    :hints (("goal" :induct <call>
             :expand (<call>)
             :in-theory (enable* arith-equiv-forwarding))))

  (defret length-of-<fn>
    (implies (< (max-fanin aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints (("goal" :induct <call>
             :expand (<call>))))

  (verify-guards aignet-self-constprop-init-pis))


(define aignet-self-constprop-init-regs ((n natp :type (integer 0 *))
                                        mark
                                        vals
                                        aignet
                                        copy)
  :guard (and (<= n (num-regs aignet))
              (< (max-fanin aignet) (bits-length mark))
              (< (max-fanin aignet) (bits-length vals))
              (< (max-fanin aignet) (lits-length copy)))
  :returns (new-copy)
  :verify-guards nil
  :measure (nfix (- (num-regs aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (int= n (num-regs aignet))))
        copy)
       (id (regnum->id n aignet))
       ((unless (int= (get-bit id mark) 1))
        (b* ((copy (set-lit id (mk-lit id 0) copy)))
          (aignet-self-constprop-init-regs (1+ (lnfix n)) mark vals aignet copy)))
       (copy (set-lit id (mk-lit 0 (get-bit id vals)) copy)))
    (aignet-self-constprop-init-regs (1+ (lnfix n)) mark vals aignet copy))
  ///
  (defret nth-of-<fn>
    (equal (nth-lit k new-copy)
           (if (and (equal (id->type k aignet) (in-type))
                    (equal (id->regp k aignet) 1)
                    (<= (nfix n) (io-id->ionum k aignet)))
               (if (eql 1 (nth k mark))
                       (mk-lit 0 (get-bit k vals))
                 (mk-lit k 0))
             (nth-lit k copy)))
    :hints (("goal" :induct <call>
             :in-theory (enable* arith-equiv-forwarding))))

  (defret length-of-<fn>
    (implies (< (max-fanin aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (verify-guards aignet-self-constprop-init-regs))

(defthm aignet-input-copies-in-bounds-of-self-constprop-init
  (b* ((copy (aignet-self-constprop-init-pis 0 constmarks vals aignet copy))
       (copy (aignet-self-constprop-init-regs 0 constmarks vals aignet copy)))
    (aignet-input-copies-in-bounds copy aignet aignet))
  :hints(("Goal" :in-theory (enable aignet-input-copies-in-bounds aignet-litp))))

(defthm aignet-marked-copies-in-bounds-of-resize-empty
  (aignet-marked-copies-in-bounds copy (resize-list nil n 0) aignet)
  :hints(("Goal" :in-theory (enable aignet-marked-copies-in-bounds))))

(defthm dfs-copy-onto-invar-of-resize-empty
  (dfs-copy-onto-invar  aignet (resize-list nil n 0) copy aignet2)
  :hints(("Goal" :in-theory (enable dfs-copy-onto-invar))))


(defsection marked-nodes-invar
  (defun-sk marked-nodes-invar (mark vals invals regvals aignet)
    (forall id
            (implies (and (equal (id->type id aignet) (in-type))
                          (equal (get-bit id mark) 1))
                     (equal (id-eval id invals regvals aignet)
                            (get-bit id vals))))
    :rewrite :direct)

  (in-theory (disable marked-nodes-invar))

  (defthm aignet-mark-const-nodes-rec-preserves-marked-nodes-invar
    (implies (and (equal (lit-eval lit invals regvals aignet) 1)
                  (marked-nodes-invar mark vals invals regvals aignet))
             (b* (((mv new-mark new-vals) (aignet-mark-const-nodes-rec lit aignet mark vals)))
               (marked-nodes-invar new-mark new-vals invals regvals aignet)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (let ((witness (acl2::find-call-lst
                                 'marked-nodes-invar-witness
                                 clause)))
                   `(:clause-processor
                     (acl2::simple-generalize-cp
                      clause '((,witness . witness))))))
            (and stable-under-simplificationp
                 '(:cases ((equal 1 (get-bit witness mark)))))))

  (defthm marked-nodes-invar-of-empty-mark
    (marked-nodes-invar (resize-list nil k 0) vals invals regvals aignet)
    :hints(("Goal" :in-theory (enable marked-nodes-invar)))))

(in-theory (disable marked-nodes-invar-necc))
(local (in-theory (enable marked-nodes-invar-necc)))



(defsection constprop-marked-pis-true
  (defun-sk constprop-marked-pis-true (n
                                       constmarks
                                       vals
                                       aignet
                                       invals
                                       regvals)
    (forall id
            (implies (and (equal (id->type id aignet) (in-type))
                          (equal (id->regp id aignet) 0)
                          (<= (nfix n) (io-id->ionum id aignet))
                          (equal (get-bit id constmarks) 1))
                     (equal (id-eval id invals regvals aignet)
                            (get-bit id vals))))
    :rewrite :direct)

  (in-theory (disable constprop-marked-pis-true))

  (local (in-theory (disable id-eval-of-input-index)))

  (defthm constprop-marked-pis-true-when-true-for-one-greater
    (implies (and (constprop-marked-pis-true (+ 1 (nfix n)) constmarks vals aignet invals regvals)
                  (let ((id (innum->id n aignet)))
                    (implies (and (equal (id->type id aignet) (in-type))
                                  (equal (id->regp id aignet) 0)
                                  (<= (nfix n) (io-id->ionum id aignet))
                                  (equal (get-bit id constmarks) 1))
                             (equal (id-eval id invals regvals aignet)
                                    (get-bit id vals)))))
             (constprop-marked-pis-true n constmarks vals aignet invals regvals))
    :hints (("goal" :in-theory (enable* arith-equiv-forwarding))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (let ((witness (acl2::find-call-lst
                                 'constprop-marked-pis-true-witness
                                 clause)))
                   `(:clause-processor
                     (acl2::simple-generalize-cp
                      clause '((,witness . witness))))))
            (and stable-under-simplificationp
                 '(:cases ((nat-equiv n (io-id->ionum witness aignet))))))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

  (defthm constprop-marked-pis-true-end
    (implies (<= (num-ins aignet) (nfix n))
             (constprop-marked-pis-true n constmarks vals aignet invals regvals))
    :hints(("Goal" :in-theory (enable constprop-marked-pis-true))))


  (defthm constprop-marked-pis-true-implies-one-greater
    (implies (constprop-marked-pis-true n constmarks vals aignet invals regvals)
             (constprop-marked-pis-true (+ 1 (nfix n)) constmarks vals aignet invals regvals))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  
  (defthm constprop-marked-pis-true-implies-nth-invals
    (implies (and (constprop-marked-pis-true n constmarks vals aignet invals regvals)
                  (<= (nfix n) (nfix k))
                  (< (nfix k) (num-ins aignet))
                  (equal (nth (innum->id k aignet) constmarks) 1))
             (bit-equiv (nth k invals)
                        (get-bit (innum->id k aignet) vals)))
    :hints (("goal" :use ((:instance constprop-marked-pis-true-necc
                           (id (innum->id k aignet))))
             :in-theory (e/d (id-eval-of-input-index)
                             (constprop-marked-pis-true-necc)))))

  (defthm constprop-marked-pis-true-of-mark-const-nodes
    (implies (and (constprop-marked-pis-true 0 constmarks vals aignet invals regvals)
                  (marked-nodes-invar constmarks vals invals regvals aignet)
                  (equal (lit-eval lit invals regvals aignet) 1))
             (b* (((mv new-constmarks new-vals)
                   (aignet-mark-const-nodes-rec lit aignet constmarks vals)))
               (constprop-marked-pis-true 0 new-constmarks new-vals aignet invals regvals)))
    :hints (("goal" :use ((:instance aignet-mark-const-nodes-rec-preserves-marked-nodes-invar
                           (mark constmarks)))
             :in-theory (disable aignet-mark-const-nodes-rec-preserves-marked-nodes-invar))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm constprop-marked-pis-true-of-empty-constmarks
    (constprop-marked-pis-true n (resize-list nil k 0) vals aignet invals regvals)
    :hints(("Goal" :in-theory (enable constprop-marked-pis-true)))))

(defsection constprop-marked-regs-true
  (defun-sk constprop-marked-regs-true (n
                                       constmarks
                                       vals
                                       aignet
                                       invals
                                       regvals)
    (forall id
            (implies (and (equal (id->type id aignet) (in-type))
                          (equal (id->regp id aignet) 1)
                          (<= (nfix n) (io-id->ionum id aignet))
                          (equal (get-bit id constmarks) 1))
                     (equal (id-eval id invals regvals aignet)
                            (get-bit id vals))))
    :rewrite :direct)

  (in-theory (disable constprop-marked-regs-true))

  (local (in-theory (disable id-eval-of-reg-index)))

  (defthm constprop-marked-regs-true-when-true-for-one-greater
    (implies (and (constprop-marked-regs-true (+ 1 (nfix n)) constmarks vals aignet invals regvals)
                  (let ((id (regnum->id n aignet)))
                    (implies (and (equal (id->type id aignet) (in-type))
                                  (equal (id->regp id aignet) 1)
                                  (<= (nfix n) (io-id->ionum id aignet))
                                  (equal (get-bit id constmarks) 1))
                             (equal (id-eval id invals regvals aignet)
                                    (get-bit id vals)))))
             (constprop-marked-regs-true n constmarks vals aignet invals regvals))
    :hints (("goal" :in-theory (enable* arith-equiv-forwarding))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (let ((witness (acl2::find-call-lst
                                 'constprop-marked-regs-true-witness
                                 clause)))
                   `(:clause-processor
                     (acl2::simple-generalize-cp
                      clause '((,witness . witness))))))
            (and stable-under-simplificationp
                 '(:cases ((nat-equiv n (io-id->ionum witness aignet))))))
    :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))


  (defthm constprop-marked-regs-true-end
    (implies (<= (num-regs aignet) (nfix n))
             (constprop-marked-regs-true n constmarks vals aignet invals regvals))
    :hints(("Goal" :in-theory (enable constprop-marked-regs-true))))


  (defthm constprop-marked-regs-true-implies-one-greater
    (implies (constprop-marked-regs-true n constmarks vals aignet invals regvals)
             (constprop-marked-regs-true (+ 1 (nfix n)) constmarks vals aignet invals regvals))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  
  (defthm constprop-marked-regs-true-implies-nth-regvals
    (implies (and (constprop-marked-regs-true n constmarks vals aignet invals regvals)
                  (<= (nfix n) (nfix k))
                  (< (nfix k) (num-regs aignet))
                  (equal (nth (regnum->id k aignet) constmarks) 1))
             (bit-equiv (nth k regvals)
                        (get-bit (regnum->id k aignet) vals)))
    :hints (("goal" :use ((:instance constprop-marked-regs-true-necc
                           (id (regnum->id k aignet))))
             :in-theory (e/d (id-eval-of-reg-index)
                             (constprop-marked-regs-true-necc)))))

  (defthm constprop-marked-regs-true-of-mark-const-nodes
    (implies (and (constprop-marked-regs-true 0 constmarks vals aignet invals regvals)
                  (marked-nodes-invar constmarks vals invals regvals aignet)
                  (equal (lit-eval lit invals regvals aignet) 1))
             (b* (((mv new-constmarks new-vals)
                   (aignet-mark-const-nodes-rec lit aignet constmarks vals)))
               (constprop-marked-regs-true 0 new-constmarks new-vals aignet invals regvals)))
    :hints (("goal" :use ((:instance aignet-mark-const-nodes-rec-preserves-marked-nodes-invar
                           (mark constmarks)))
             :in-theory (disable aignet-mark-const-nodes-rec-preserves-marked-nodes-invar))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm constprop-marked-regs-true-of-empty-constmarks
    (constprop-marked-regs-true n (resize-list nil k 0) vals aignet invals regvals)
    :hints(("Goal" :in-theory (enable constprop-marked-regs-true)))))



(define aignet-self-copy-dfs-rec ((id natp :type (integer 0 *))
                                  aignet
                                  mark
                                  copy
                                  strash
                                  (gatesimp gatesimp-p))
  :returns (mv new-mark
               new-copy
               new-strash
               new-aignet)
  :measure (nfix id)
  :guard (and (id-existsp id aignet)
              (< id (bits-length mark))
              (< id (lits-length copy))
              (ec-call (aignet-marked-copies-in-bounds copy mark aignet))
              (non-exec (ec-call (aignet-input-copies-in-bounds copy aignet aignet))))

  :verify-guards nil
  (b* (((when (int= (get-bit id mark) 1))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv mark copy strash aignet)))
       (slot0 (id->slot id 0 aignet))
       (type (snode->type slot0))
       ((when (int= type (out-type)))
        ;; copy the fanin of the output and set the output ID's copy to be
        ;; that of the fanin lit
        (b* ((f (co-id->fanin id aignet))
             ((mv mark copy strash aignet)
              (aignet-self-copy-dfs-rec
               (lit-id f) aignet mark copy strash gatesimp))
             (f-copy (lit-copy f copy))
             (copy (set-lit id f-copy copy))
             (mark (set-bit id 1 mark)))
          (mv mark copy strash aignet)))

       ((when (int= type (const-type)))
        (b* ((mark (set-bit id 1 mark))
             (copy (set-lit id 0 copy))
             (aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv mark copy strash aignet)))

       ((unless (int= type (gate-type)))
        (b* ((mark (set-bit id 1 mark))
             (aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv mark copy strash aignet)))

       ;; gate: recur on each fanin, then hash an AND of the two copies
       (f0 (snode->fanin slot0))
       (slot1 (id->slot id 1 aignet))
       (f1 (snode->fanin slot1))
       ((mv mark copy strash aignet)
        (aignet-self-copy-dfs-rec
         (lit-id f0) aignet mark copy strash gatesimp))
       (f0-copy (lit-copy f0 copy))
       (xor (snode->regp slot1))
       ((when (and (int= f0-copy 0) (eql xor 0)))
        ;; first branch was 0 so exit early
        (b* ((copy (set-lit id 0 copy))
             (mark (set-bit id 1 mark)))
          (mv mark copy strash aignet)))
       ((mv mark copy strash aignet)
        (aignet-self-copy-dfs-rec
         (lit-id f1) aignet mark copy strash gatesimp))
       (f1-copy (lit-copy f1 copy))
       ((mv id-copy strash aignet)
        (if (eql xor 1)
            (aignet-hash-xor f0-copy f1-copy gatesimp strash aignet)
          (aignet-hash-and f0-copy f1-copy gatesimp strash aignet)))
       (copy (set-lit id id-copy copy))
       (mark (set-bit id 1 mark)))
    (mv mark copy strash aignet))
  ///

  (local (in-theory (e/d* (acl2::arith-equiv-forwarding)
                          (lit-negate-cond acl2::b-xor
                                           (:d aignet-self-copy-dfs-rec)
                                           cons-equal
                                           ;; aignet-copies-ok
                                           ))))


  (local (def-aignet-preservation-thms aignet-self-copy-dfs-rec :stobjname aignet))

  (defthm aignet-copy-dfs-rec-of-extension
    (implies (and (aignet-extension-binding)
                  (id-existsp id orig))
             (equal (aignet-copy-dfs-rec id new mark copy strash gatesimp aignet2)
                    (aignet-copy-dfs-rec id orig mark copy strash gatesimp aignet2)))
    :hints(("Goal" :in-theory (enable (:i aignet-copy-dfs-rec))
            :expand ((:free (aignet) (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2))))))

  (defthm aignet-self-copy-dfs-rec-is-aignet-copy-dfs-rec
    (equal (aignet-self-copy-dfs-rec id aignet mark copy strash gatesimp)
           (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet))
    :hints (("goal" :induct (aignet-self-copy-dfs-rec id aignet mark copy strash gatesimp)
             :expand ((aignet-self-copy-dfs-rec id aignet mark copy strash gatesimp)
                      (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet)))))

  (verify-guards aignet-self-copy-dfs-rec))


;; BOZO redundant with def in cnf.lisp
(define lits-max-id-val ((lits lit-listp))
  (if (atom lits)
      0
    (max (lit-id (car lits))
         (lits-max-id-val (cdr lits)))))

(defthmd lits-max-id-val-when-aignet-lit-listp
  (implies (aignet-lit-listp lits aignet)
           (<= (lits-max-id-val lits) (node-count (find-max-fanin aignet))))
  :hints(("Goal" :in-theory (enable aignet-lit-listp lits-max-id-val)))
  :rule-classes :forward-chaining)



(define marks-boundedp ((limit natp) mark)
  :non-executable t
  (not (member 1 (nthcdr limit mark)))
  ///
  (local (defthm nth-is-member
           (implies (not (equal (nth n x) nil))
                    (member (nth n x) x))
           :hints (("goal" :induct (nth n x)
                    :in-theory (enable (:i nth))
                    :expand ((nth n x))))))

  (local (defthm blah
           (equal (+ x (- x) y)
                  (fix y))))


  (defthmd lookup-when-marks-boundedp
    (implies (and (marks-boundedp limit mark)
                  (<= (nfix limit) (nfix n)))
             (bit-equiv (nth n mark) 0))
    :hints(("Goal" :in-theory (disable acl2::nthcdr-of-cdr
                                       nth-is-member)
            :use ((:instance nth-is-member
                   (n (- (nfix n) (nfix limit)))
                   (x (nthcdr limit mark)))))))

  (local (defthm nthcdr-of-update-nth
           (implies (< (nfix m) (nfix n))
                    (equal (nthcdr n (update-nth m val x))
                           (nthcdr n x)))
           :hints(("Goal" :in-theory (e/d (update-nth nthcdr)
                                          (acl2::nthcdr-of-cdr))))))

  (defthm marks-boundedp-of-update-nth
    (implies (and (marks-boundedp limit x)
                  (< (nfix n) (nfix limit)))
             (marks-boundedp limit (update-nth n val x))))

  (local (in-theory (disable aignet-copy-dfs-rec-preserves-ci-copies
                             aignet-copy-dfs-rec-preserves-copy-when-marked
                             lookup-id-out-of-bounds
                             lookup-id-in-bounds-when-positive)))

  (defthm aignet-copy-dfs-rec-preserves-marks-boundedp
    (implies (and (marks-boundedp limit mark)
                  (< (nfix id) (nfix limit)))
             (b* (((mv new-mark & & &)
                   (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))
               (marks-boundedp limit new-mark)))
    :hints(("Goal" :in-theory (e/d ((:i aignet-copy-dfs-rec)) (marks-boundedp))
            :induct (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)
            :expand ((aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))))

  (defthm marks-boundedp-when-lesser
    (implies (and (marks-boundedp limit1 mark)
                  (<= (nfix limit1) (nfix limit)))
             (marks-boundedp limit mark)))

  (local (defthm member-resize-list-nil
           (not (member 1 (resize-list nil n 0)))
           :hints(("Goal" :in-theory (enable acl2::resize-list-when-atom
                                             acl2::repeat)))))

  (defthm marks-boundedp-of-resize-list
    (marks-boundedp limit (resize-list nil n 0))))

(define lit-list-copies ((lits lit-listp)
                         (copy))
  :guard (< (lits-max-id-val lits) (lits-length copy))
  :guard-hints (("goal" :in-theory (enable lits-max-id-val)))
  :returns (lits lit-listp)
  (if (atom lits)
      nil
    (cons (lit-copy (car lits) copy)
          (lit-list-copies (cdr lits) copy))))

(define lit-list-marked ((lits lit-listp)
                         (mark))
  :guard (< (lits-max-id-val lits) (bits-length mark))
  :guard-hints (("goal" :in-theory (enable lits-max-id-val)))
  (if (atom lits)
      t
    (and (eql (get-bit (lit->var (car lits)) mark) 1)
         (lit-list-marked (cdr lits) mark)))
  ///
  (defthm aignet-lit-listp-of-lit-list-copies-when-marked
    (implies (and (aignet-marked-copies-in-bounds copy mark aignet)
                  (lit-list-marked lits mark))
             (aignet-lit-listp (lit-list-copies lits copy) aignet))
    :hints(("Goal" :in-theory (enable lit-list-copies))))

  (defthm lit-eval-list-of-copies-when-dfs-copy-onto-invar
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (lit-list-marked lits mark))
             (equal (lit-eval-list (lit-list-copies lits copy) invals regvals aignet2)
                    (lit-eval-list lits
                                   (input-copy-values 0 invals regvals aignet copy aignet2)
                                   (reg-copy-values 0 invals regvals aignet copy aignet2)
                                   aignet)))
    :hints(("Goal" :in-theory (enable lit-list-copies lit-eval-list)
            :expand ((:free (invals regvals) (lit-eval (car lits) invals regvals aignet)))))))




(define aignet-self-copy-dfs-rec-list ((lits lit-listp)
                                       aignet
                                       mark
                                       copy
                                       strash
                                       (gatesimp gatesimp-p))
  :returns (mv new-mark
               new-copy
               new-strash
               new-aignet)
  :guard (and (aignet-lit-listp lits aignet)
              (< (lits-max-id-val lits) (bits-length mark))
              (< (lits-max-id-val lits) (lits-length copy))
              (ec-call (aignet-marked-copies-in-bounds copy mark aignet))
              (non-exec (ec-call (aignet-input-copies-in-bounds copy aignet aignet))))
  :verify-guards nil
  (b* (((when (atom lits))
        (b* ((aignet (mbe :logic (non-exec (node-list-fix aignet))
                          :exec aignet)))
          (mv mark copy strash aignet)))
       ((mv mark copy strash aignet)
        (aignet-self-copy-dfs-rec (lit->var (car lits)) aignet mark copy strash gatesimp)))
    (aignet-self-copy-dfs-rec-list (cdr lits) aignet mark copy strash gatesimp))
  ///
  (local (in-theory (disable (:d aignet-self-copy-dfs-rec-list))))
  (defret mark-len-of-<fn>
    (<= (len mark) (len new-mark))
    :hints ((acl2::just-induct-and-expand <call>))
    :rule-classes :linear)

  (defret copy-len-of-<fn>
    (<= (len copy) (len new-copy))
    :hints ((acl2::just-induct-and-expand <call>))
    :rule-classes :linear)

  (def-aignet-preservation-thms aignet-self-copy-dfs-rec-list)

  (verify-guards aignet-self-copy-dfs-rec-list
    :hints (("goal" :in-theory (enable lits-max-id-val))))

  (defret aignet-input-copies-in-bounds-of-<fn>
    (implies (and (aignet-input-copies-in-bounds copy aignet aignet)
                  ;; (aignet-lit-listp lits aignet)
                  )
             (aignet-input-copies-in-bounds new-copy new-aignet new-aignet))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-marked-copies-in-bounds-of-<fn>
    (implies (and (aignet-marked-copies-in-bounds copy mark aignet)
                  (aignet-input-copies-in-bounds copy aignet aignet)
                  ;; (aignet-lit-listp lits aignet)
                  )
             (aignet-marked-copies-in-bounds new-copy new-mark new-aignet))
    :hints ((acl2::just-induct-and-expand <call>)))

  (local
   (defthm aignet-litp-implies-less-than-max-fanin
     (implies (aignet-litp lit aignet)
              (and (< (lit->var lit) (+ 1 (node-count (find-max-fanin aignet))))
                   (<= (lit->var lit) (node-count (find-max-fanin aignet)))))))

  (defret marks-boundedp-of-<fn>
    (implies (and (marks-boundedp limit mark)
                  (< (lits-max-id-val lits) (nfix limit)))
             (marks-boundedp limit new-mark))
    :hints (("goal" :in-theory (enable lits-max-id-val))
            (acl2::just-induct-and-expand <call>)))
  
  (local (defthmd lookup-when-marks-boundedp-split
           (implies (and (marks-boundedp limit mark)
                         (case-split (<= (nfix limit) (nfix n))))
                    (and (bit-equiv (nth n mark) 0)
                         (not (equal 1 (nth n mark)))))
           :hints(("Goal" :use lookup-when-marks-boundedp))))

  (local (defthmd lookup-when-marks-boundedp-really-split
           (implies (marks-boundedp limit mark)
                    (equal (equal 1 (nth n mark))
                           (and (< (nfix n) (nfix limit))
                                (hide (equal 1 (nth n mark))))))
           :hints(("Goal" :use lookup-when-marks-boundedp
                   :expand ((:free (x) (hide x)))))))

  (defthm input-copy-values-of-extension
    (implies (and (aignet-extension-binding)
                  (equal (stype-count :pi new) (stype-count :pi orig)))
             (equal (input-copy-values n invals regvals new copy aignet2)
                    (input-copy-values n invals regvals orig copy aignet2)))
    :hints(("Goal" :in-theory (enable input-copy-values))))

  (defthm reg-copy-values-of-extension
    (implies (and (aignet-extension-binding)
                  (equal (stype-count :reg new) (stype-count :reg orig)))
             (equal (reg-copy-values n invals regvals new copy aignet2)
                    (reg-copy-values n invals regvals orig copy aignet2)))
    :hints(("Goal" :in-theory (enable reg-copy-values))))

  (defthm dfs-copy-onto-invar-of-extension
    (implies (and (aignet-extension-binding)
                  (marks-boundedp (+ 1 (node-count orig)) mark)
                  (equal (stype-count :pi new) (stype-count :pi orig))
                  (equal (stype-count :reg new) (stype-count :reg orig)))
             (iff (dfs-copy-onto-invar new mark copy aignet2)
                  (dfs-copy-onto-invar orig mark copy aignet2)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(assoc 'dfs-copy-onto-invar clause))
                   :in-theory (enable aignet-idp lookup-when-marks-boundedp-split)))))
             

  (defret dfs-copy-onto-invar-holds-of-<fn>
    (implies (and (aignet-lit-listp lits aignet)
                  (marks-boundedp (+ 1 (node-count aignet)) mark)
                  (dfs-copy-onto-invar aignet mark copy aignet)
                  (aignet-input-copies-in-bounds copy aignet aignet)
                  (aignet-marked-copies-in-bounds copy mark aignet))
             (dfs-copy-onto-invar aignet new-mark new-copy new-aignet))
    :hints ((acl2::just-induct-and-expand <call>)
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))
                            (lits-max-id-val lits)
                            <call>)
                   :use ((:instance marks-boundedp-of-aignet-self-copy-dfs-rec-list
                          (limit (+ 1 (node-count aignet)))))
                   :in-theory (e/d (aignet-idp lookup-when-marks-boundedp-really-split
                                               lits-max-id-val-when-aignet-lit-listp)
                                   (marks-boundedp-of-aignet-self-copy-dfs-rec-list))))))

  (defret marks-preserved-of-<fn>
    (implies (equal (nth n mark) 1)
             (equal (nth n new-mark) 1))
    :hints ((acl2::just-induct-and-expand <call>)))


  (defret <fn>-copies-preserved-of-marked
    (implies (equal (nth n mark) 1)
             (equal (nth-lit n new-copy) (nth-lit n copy)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret lit-list-marked-of-<fn>
    (lit-list-marked lits new-mark)
    :hints (("goal" :in-theory (enable lit-list-marked))
            (acl2::just-induct-and-expand <call>)))

  (defret stype-count-of-<fn>
    (implies (and (not (equal (stype-fix stype) :and))
                  (not (equal (stype-fix stype) :xor)))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret input-copy-values-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet)
             (equal (input-copy-values n invals regvals aignet new-copy new-aignet)
                    (input-copy-values n invals regvals aignet copy aignet)))
    :hints ((acl2::just-induct-and-expand <call>)))
    ;; :hints(("Goal" :in-theory (enable input-copy-values)
    ;;         :induct (input-copy-values n invals regvals aignet copy aignet)
    ;;         :expand ((:free (aignet aignet2 copy)
    ;;                   (input-copy-values n invals regvals aignet copy aignet2))))))

  (defret reg-copy-values-of-<fn>
    (implies (aignet-input-copies-in-bounds copy aignet aignet)
             (equal (reg-copy-values n invals regvals aignet new-copy new-aignet)
                    (reg-copy-values n invals regvals aignet copy aignet)))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret lit-eval-list-of-<fn>
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet)
                  (marks-boundedp (+ 1 (node-count aignet)) mark)
                  (aignet-input-copies-in-bounds copy aignet aignet)
                  (aignet-marked-copies-in-bounds copy mark aignet)
                  (aignet-lit-listp lits aignet))
             (equal (lit-eval-list (lit-list-copies lits new-copy)
                                   invals regvals new-aignet)
                    (lit-eval-list lits
                                   (input-copy-values 0 invals regvals aignet copy aignet)
                                   (reg-copy-values 0 invals regvals aignet copy aignet)
                                   aignet)))
    :hints (("goal" :use ((:instance lit-eval-list-of-copies-when-dfs-copy-onto-invar
                           (aignet2 new-aignet)
                           (copy new-copy)
                           (mark new-mark)))
             :in-theory (disable <fn>
                                 lit-eval-list-of-copies-when-dfs-copy-onto-invar)))))


(define aignet-parametrize-copyarr ((hyp litp) aignet copy)
  :guard (and (fanin-litp hyp aignet)
              (non-exec (equal copy (create-copy))))
  :returns (new-copy)
  (b* (((acl2::local-stobjs constmarks vals)
        (mv copy constmarks vals))
       (constmarks (resize-bits (+ 1 (max-fanin aignet)) constmarks))
       (vals (resize-bits (+ 1 (max-fanin aignet)) vals))
       ((mv constmarks vals) (aignet-mark-const-nodes-rec hyp aignet constmarks vals))
       (copy (mbe :logic (non-exec (create-copy))
                  :exec copy))
       (copy (resize-lits (+ 1 (max-fanin aignet)) copy))
       (copy (aignet-self-constprop-init-pis 0 constmarks vals aignet copy))
       (copy (aignet-self-constprop-init-regs 0 constmarks vals aignet copy)))
    (mv copy constmarks vals))
  ///

  (defret normalize-aignet-parametrize-copyarr
    (implies (syntaxp (not (equal copy ''nil)))
             (equal new-copy
                    (let ((copy nil)) <call>))))

  (defret size-of-aignet-parametrize-copyarr
    (equal (len new-copy) (+ 1 (max-fanin aignet))))

  (local
   (progn

     (defthm nth-of-take
       (equal (nth i (take n l))
              (and (< (nfix i) (nfix n))
                   (nth i l))))

     (defthm input-copy-values-of-aignet-self-constprop-init-regs
       (bits-equiv (input-copy-values n invals regvals aignet
                                      (aignet-self-constprop-init-regs k constmarks vals aignet copy)
                                      aignet)
                   (input-copy-values n invals regvals aignet copy aignet))
       :hints(("Goal" :in-theory (enable bits-equiv))
              (acl2::use-termhint
               (b* ((new-copy (aignet-self-constprop-init-regs k constmarks vals aignet copy))
                    (a (input-copy-values n invals regvals aignet new-copy aignet))
                    (b (input-copy-values n invals regvals aignet copy aignet))
                    (witness (acl2::bits-equiv-witness a b)))
                 `'(:cases ((< (+ (nfix n) (nfix ,(acl2::hq witness))) (num-ins aignet))))))))

     (defthm input-copy-values-of-aignet-self-constprop-init-pis
       (implies (constprop-marked-pis-true 0 constmarks vals aignet invals regvals)
                (bits-equiv (input-copy-values 0 invals regvals aignet
                                               (aignet-self-constprop-init-pis 0 constmarks vals aignet copy)
                                               aignet)
                            (take (num-ins aignet) invals)))
       :hints(("Goal" :in-theory (e/d (bits-equiv) (acl2::nth-of-take)))
              (acl2::use-termhint
               (b* ((new-copy (aignet-self-constprop-init-pis 0 constmarks vals aignet copy))
                    (a (input-copy-values 0 invals regvals aignet new-copy aignet))
                    (b (take (num-ins aignet) invals))
                    (witness (acl2::bits-equiv-witness a b)))
                 `'(:cases ((< (nfix ,(acl2::hq witness)) (num-ins aignet)))
                    :expand ((:free (id neg)
                              (lit-eval (make-lit id neg) invals regvals aignet))))))))

     (defthm reg-copy-values-of-aignet-self-constprop-init-ins
       (bits-equiv (reg-copy-values n invals regvals aignet
                                    (aignet-self-constprop-init-pis k constmarks vals aignet copy)
                                    aignet)
                   (reg-copy-values n invals regvals aignet copy aignet))
       :hints(("Goal" :in-theory (enable bits-equiv))
              (acl2::use-termhint
               (b* ((new-copy (aignet-self-constprop-init-pis k constmarks vals aignet copy))
                    (a (reg-copy-values n invals regvals aignet new-copy aignet))
                    (b (reg-copy-values n invals regvals aignet copy aignet))
                    (witness (acl2::bits-equiv-witness a b)))
                 `'(:cases ((< (+ (nfix n) (nfix ,(acl2::hq witness))) (num-regs aignet))))))))

     (defthm reg-copy-values-of-aignet-self-constprop-init-regs
       (implies (constprop-marked-regs-true 0 constmarks vals aignet invals regvals)
                (bits-equiv (reg-copy-values 0 invals regvals aignet
                                             (aignet-self-constprop-init-regs 0 constmarks vals aignet copy)
                                             aignet)
                            (take (num-regs aignet) regvals)))
       :hints(("Goal" :in-theory (e/d (bits-equiv) (acl2::nth-of-take)))
              (acl2::use-termhint
               (b* ((new-copy (aignet-self-constprop-init-regs 0 constmarks vals aignet copy))
                    (a (reg-copy-values 0 invals regvals aignet new-copy aignet))
                    (b (take (num-regs aignet) regvals))
                    (witness (acl2::bits-equiv-witness a b)))
                 `'(:cases ((< (nfix ,(acl2::hq witness)) (num-regs aignet)))
                    :expand ((:free (id neg)
                              (lit-eval (make-lit id neg) invals regvals aignet))))))))))

  (defret input-copy-values-of-<fn>
    (implies (equal (lit-eval hyp invals regvals aignet) 1)
             (bits-equiv (input-copy-values 0 invals regvals aignet new-copy aignet)
                         (take (num-ins aignet) invals))))

  (defret reg-copy-values-of-<fn>
    (implies (equal (lit-eval hyp invals regvals aignet) 1)
             (bits-equiv (reg-copy-values 0 invals regvals aignet new-copy aignet)
                         (take (num-regs aignet) regvals))))

  (defret aignet-input-copies-in-bounds-of-<fn>
    (aignet-input-copies-in-bounds new-copy aignet aignet))

  (defret <fn>-of-aignet-lit-fix
    (equal (let ((hyp (aignet-lit-fix hyp aignet))) <call>)
           new-copy)))
       



(define aignet-lit-list-fix ((lits lit-listp) aignet)
  :guard (non-exec (aignet-lit-listp lits aignet))
  :returns (new-lits (aignet-lit-listp new-lits aignet))
  :verify-guards nil
  :inline t
  (mbe :logic (non-exec (if (atom lits)
                            nil
                          (cons (aignet-lit-fix (car lits) aignet)
                                (aignet-lit-list-fix (cdr lits) aignet))))
       :exec lits)
  ///
  (defret <fn>-when-aignet-lit-listp
    (implies (aignet-lit-listp lits aignet)
             (equal new-lits (lit-list-fix lits))))

  (defret len-of-<fn>
    (equal (len new-lits) (len lits)))

  (defret consp-of-<fn>
    (equal (consp new-lits) (consp lits)))

  (defret car-of-aignet-lit-list-fix
    (implies (consp lits)
             (equal (car new-lits)
                    (aignet-lit-fix (car lits) aignet))))

  (defret cdr-of-aignet-lit-list-fix
    (equal (cdr new-lits)
           (aignet-lit-list-fix (cdr lits) aignet)))

  (verify-guards aignet-lit-list-fix$inline))

(defcong bits-equiv equal (lit-eval-list x invals regvals aignet) 2)
(defcong bits-equiv equal (lit-eval-list x invals regvals aignet) 3)
(defthm lit-eval-list-of-take-num-ins
  (equal (lit-eval-list x (take (stype-count :pi aignet) invals)
                        regvals aignet)
         (lit-eval-list x invals regvals aignet)))

(defthm lit-eval-list-of-take-num-regs
  (equal (lit-eval-list x invals
                        (take (stype-count :reg aignet) regvals) aignet)
         (lit-eval-list x invals regvals aignet)))

(defthm lit-eval-list-of-aignet-lit-list-fix
  (equal (lit-eval-list (aignet-lit-list-fix x aignet) invals regvals aignet)
         (lit-eval-list x invals regvals aignet))
  :hints(("Goal" :in-theory (enable aignet-lit-list-fix
                                    lit-eval-of-aignet-lit-fix))))


(define self-constprop-invar (hyp mark copy aignet)
  :non-executable t
  :prepwork ((defun-sk self-constprop-copies-ok (hyp copy aignet)
               (forall (invals regvals)
                       (implies (equal 1 (lit-eval hyp invals regvals aignet))
                                (and (bits-equiv (input-copy-values 0 invals regvals aignet copy aignet)
                                                 (take (num-ins aignet) invals))
                                     (bits-equiv (reg-copy-values 0 invals regvals aignet copy aignet)
                                                 (take (num-regs aignet) regvals)))))
               :rewrite :direct)
             (in-theory (disable self-constprop-copies-ok)))
  :verify-guards nil
  :hooks nil
  (and (dfs-copy-onto-invar aignet mark copy aignet)
       (marks-boundedp (+ 1 (node-count aignet)) mark)
       (aignet-input-copies-in-bounds copy aignet aignet)
       (aignet-marked-copies-in-bounds copy mark aignet)
       (self-constprop-copies-ok hyp copy aignet))
  ///
  (defthm self-constprop-invar-preserved-by-aignet-copy-dfs-rec
    (implies (and (self-constprop-invar hyp mark copy aignet)
                  (aignet-litp hyp aignet)
                  (aignet-idp id aignet))
             (b* (((mv mark copy & aignet)
                   (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet)))
               (self-constprop-invar hyp mark copy aignet)))
    :hints(("Goal" :in-theory (enable aignet-idp))
           (and stable-under-simplificationp
                `(:expand (,(assoc 'self-constprop-copies-ok clause))))))

  (defthm self-constprop-invar-preserved-by-aignet-self-copy-dfs-rec-list
    (implies (and (self-constprop-invar hyp mark copy aignet)
                  (aignet-litp hyp aignet)
                  (aignet-lit-listp lits aignet))
             (b* (((mv mark copy & aignet)
                   (aignet-self-copy-dfs-rec-list lits aignet mark copy strash gatesimp)))
               (self-constprop-invar hyp mark copy aignet)))
    :hints(("goal" :in-theory (enable lits-max-id-val-when-aignet-lit-listp))
           (and stable-under-simplificationp
                `(:expand (,(assoc 'self-constprop-copies-ok clause))))))

  (defthm self-constprop-invar-of-aignet-parametrize-copyarr
    (self-constprop-invar hyp (resize-list nil n 0)
                          (aignet-parametrize-copyarr hyp aignet copy)
                          aignet)
    :hints ((and stable-under-simplificationp
                 `(:expand (,(assoc 'self-constprop-copies-ok clause))))))

  (defthm marked-lit-copy-when-self-constprop-invar
    (implies (and (self-constprop-invar hyp mark copy aignet)
                  (equal 1 (lit-eval hyp invals regvals aignet))
                  (equal 1 (get-bit id mark)))
             (equal (lit-eval (nth-lit id copy) invals regvals aignet)
                    (id-eval id invals regvals aignet))))

  (defthm marked-lit-copies-when-self-constprop-invar
    (implies (and (self-constprop-invar hyp mark copy aignet)
                  (equal 1 (lit-eval hyp invals regvals aignet))
                  (lit-list-marked lits mark))
             (equal (lit-eval-list (lit-list-copies lits copy) invals regvals aignet)
                    (lit-eval-list lits invals regvals aignet)))))



(define aignet-parametrize-lit ((lit litp)
                                (hyp litp)
                                strash
                                aignet)
  :returns (mv (new-lit litp :rule-classes :type-prescription)
               (new-strash)
               (new-aignet))
  :guard (and (fanin-litp hyp aignet)
              (fanin-litp lit aignet))
  (b* (((acl2::local-stobjs copy mark)
        (mv lit strash aignet copy mark))
       (lit (mbe :logic (non-exec (aignet-lit-fix lit aignet)) :exec lit))
       (copy (aignet-parametrize-copyarr hyp aignet copy))
       (mark (resize-bits (+ 1 (max-fanin aignet)) mark))
       ((mv mark copy strash aignet)
        (aignet-self-copy-dfs-rec (lit->var lit) aignet mark copy strash (default-gatesimp))))
    (mv (lit-copy lit copy) strash aignet copy mark))
  ///
  (defret aignet-litp-of-<fn>
    (aignet-litp new-lit new-aignet))

  (defret stype-count-of-<fn>
    (implies (and (not (equal (stype-fix stype) :and))
                  (not (equal (stype-fix stype) :xor)))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  ;; (local (defthm lit-eval-of-0-lit
  ;;          (equal (lit-eval (make-lit 0 neg) invals regvals aignet)
  ;;                 (bfix neg))
  ;;          :hints (("goal" :expand ((lit-eval (make-lit 0 neg) invals regvals aignet))))))


  (defret eval-of-<fn>
    (implies (equal (lit-eval hyp invals regvals aignet) 1)
             (equal (lit-eval new-lit invals regvals new-aignet)
                    (lit-eval lit invals regvals aignet)))
    :hints (("goal" :expand ((lit-eval (aignet-lit-fix lit aignet) invals regvals aignet))
             :use ((:instance lit-eval-of-aignet-lit-fix (x lit)))
             :in-theory (disable lit-eval-of-aignet-lit-fix)))))





(define aignet-parametrize-lit-list ((lits lit-listp)
                                     (hyp litp)
                                     strash
                                     aignet)
  :returns (mv (new-lits lit-listp :rule-classes :type-prescription)
               (new-strash)
               (new-aignet))
  :guard (and (fanin-litp hyp aignet)
              (non-exec (aignet-lit-listp lits aignet)))
  :guard-hints (("goal" :in-theory (enable lits-max-id-val-when-aignet-lit-listp)))
  (b* (((acl2::local-stobjs copy mark)
        (mv lits strash aignet copy mark))
       (copy (aignet-parametrize-copyarr hyp aignet copy))
       (mark (resize-bits (+ 1 (max-fanin aignet)) mark))
       (lits (aignet-lit-list-fix lits aignet))
       ((mv mark copy strash aignet)
        (aignet-self-copy-dfs-rec-list lits aignet mark copy strash (default-gatesimp))))
    (mv (lit-list-copies lits copy) strash aignet copy mark))
  ///
  (defthm aignet-litp-of-aignet-parametrize-lit-list
    (b* (((mv new-lits  & new-aignet)
          (aignet-parametrize-lit-list lits hyp strash aignet)))
      (aignet-lit-listp new-lits new-aignet))
    :hints ((acl2::use-termhint
             (b* ((copy (create-copy)) (mark (create-mark))
                  (copy (aignet-parametrize-copyarr hyp aignet copy))
                  (mark (resize-bits (+ 1 (max-fanin aignet)) mark))
                  (lits (aignet-lit-list-fix lits aignet))
                  ((mv mark copy ?strash aignet)
                   (aignet-self-copy-dfs-rec-list lits aignet mark copy strash (default-gatesimp))))
               `'(:use ((:instance aignet-lit-listp-of-lit-list-copies-when-marked
                         (lits ,(acl2::hq lits))
                         (mark ,(acl2::hq mark))
                         (copy ,(acl2::hq copy))
                         (aignet ,(acl2::hq aignet))))
                  :in-theory (disable aignet-lit-listp-of-lit-list-copies-when-marked))))))

  (defret stype-count-of-<fn>
    (implies (and (not (equal (stype-fix stype) :and))
                  (not (equal (stype-fix stype) :xor)))
             (equal (stype-count stype new-aignet)
                    (stype-count stype aignet))))

  (defret eval-of-<fn>
    (implies (equal (lit-eval hyp invals regvals aignet) 1)
             (equal (lit-eval-list new-lits invals regvals new-aignet)
                    (lit-eval-list lits invals regvals aignet)))
    :hints (("goal" :expand ((lit-eval (aignet-lit-fix lit aignet) invals regvals aignet))
             :use ((:instance lit-eval-of-aignet-lit-fix (x lit)))
             :in-theory (disable lit-eval-of-aignet-lit-fix)))))


       
                                  








  
