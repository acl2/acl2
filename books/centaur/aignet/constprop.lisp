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
(include-book "self-constprop")
(include-book "transform-utils")

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

(local (xdoc::set-default-parents constprop))



;; (define aignet-unmark-non-inputs ((n natp :type (integer 0 *)) mark aignet)
;;   :guard (and (<= n (+ 1 (max-fanin aignet)))
;;               (< (max-fanin aignet) (bits-length mark)))
;;   :measure (nfix (+ 1 (- (max-fanin aignet) (nfix n))))
;;   :returns (new-mark)
;;   :verify-guards nil
;;   (b* (((when (mbe :logic (zp (+ 1 (- (max-fanin aignet) (nfix n))))
;;                    :exec (int= n (+ 1 (max-fanin aignet)))))
;;         mark)
;;        (mark (if (eql (id->type n aignet) (in-type))
;;                  mark
;;                (set-bit n 0 mark))))
;;     (aignet-unmark-non-inputs (1+ (lnfix n)) mark aignet))
;;   ///
;;   (defret nth-of-<fn>-split
;;     (bit-equiv (nth k new-mark)
;;                (cond ((< (nfix k) (nfix n))
;;                       (nth k mark))
;;                      ((<= (nfix k) (max-fanin aignet))
;;                       (b-and (bool->bit (eql (id->type k aignet) (in-type)))
;;                              (nth k mark)))
;;                      (t (nth k mark)))))

;;   (defret length-of-<fn>
;;     (implies (< (max-fanin aignet) (len mark))
;;              (equal (len new-mark) (len mark))))

;;   (verify-guards aignet-unmark-non-inputs
;;     :hints(("Goal" :in-theory (enable aignet-idp)))))


(defstobj-clone constmarks bitarr :strsubst (("BIT" . "AIGNET-CONSTMARKS")))
        
(define aignet-constprop-init-pis ((n natp :type (integer 0 *))
                                   constmarks
                                   vals
                                   aignet
                                   copy
                                   aignet2)
  :guard (and (eql (num-ins aignet) (num-ins aignet2))
              (<= n (num-ins aignet))
              (<= (num-fanins aignet) (bits-length constmarks))
              (<= (num-fanins aignet) (bits-length vals))
              (<= (num-fanins aignet) (lits-length copy)))
  :returns (new-copy)
  :verify-guards nil
  :measure (nfix (- (num-ins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (int= n (num-ins aignet))))
        copy)
       (id (innum->id n aignet))
       ((unless (int= (get-bit id constmarks) 1))
        (b* ((copy (set-lit id (mk-lit (innum->id n aignet2) 0) copy)))
          (aignet-constprop-init-pis (1+ (lnfix n)) constmarks vals aignet copy aignet2)))
       (copy (set-lit id (mk-lit 0 (get-bit id vals)) copy)))
    (aignet-constprop-init-pis (1+ (lnfix n)) constmarks vals aignet copy aignet2))
  ///
  (defret nth-of-<fn>
    (equal (nth-lit k new-copy)
           (if (and (equal (id->type k aignet) (in-type))
                    (equal (id->regp k aignet) 0)
                    (<= (nfix n) (ci-id->ionum k aignet)))
               (if (eql 1 (nth k constmarks))
                       (mk-lit 0 (get-bit k vals))
                 (mk-lit (innum->id (ci-id->ionum k aignet) aignet2) 0))
             (nth-lit k copy)))
    :hints (("goal" :induct <call>
             :in-theory (enable* arith-equiv-forwarding))))

  (defret length-of-<fn>
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (verify-guards aignet-constprop-init-pis))

(define aignet-constprop-init-regs ((n natp :type (integer 0 *))
                                    constmarks
                                    vals
                                    aignet
                                    copy
                                    aignet2)
  :guard (and (eql (num-regs aignet) (num-regs aignet2))
              (<= n (num-regs aignet))
              (<= (num-fanins aignet) (bits-length constmarks))
              (<= (num-fanins aignet) (bits-length vals))
              (<= (num-fanins aignet) (lits-length copy)))
  :returns (new-copy)
  :verify-guards nil
  :measure (nfix (- (num-regs aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (int= n (num-regs aignet))))
        copy)
       (id (regnum->id n aignet))
       ((unless (int= (get-bit id constmarks) 1))
        (b* ((copy (set-lit id (mk-lit (regnum->id n aignet2) 0) copy)))
          (aignet-constprop-init-regs (1+ (lnfix n)) constmarks vals aignet copy aignet2)))
       (copy (set-lit id (mk-lit 0 (get-bit id vals)) copy)))
    (aignet-constprop-init-regs (1+ (lnfix n)) constmarks vals aignet copy aignet2))
  ///
  (defret nth-of-<fn>
    (equal (nth-lit k new-copy)
           (if (and (equal (id->type k aignet) (in-type))
                    (equal (id->regp k aignet) 1)
                    (<= (nfix n) (ci-id->ionum k aignet)))
               (if (eql 1 (nth k constmarks))
                       (mk-lit 0 (get-bit k vals))
                 (mk-lit (regnum->id (ci-id->ionum k aignet) aignet2) 0))
             (nth-lit k copy)))
    :hints (("goal" :induct <call>
             :in-theory (enable* arith-equiv-forwarding))))

  (defret length-of-<fn>
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (verify-guards aignet-constprop-init-regs))

(defthm aignet-input-copies-in-bounds-of-constprop-init
  (b* ((copy (aignet-constprop-init-pis 0 constmarks vals aignet copy aignet2))
       (copy (aignet-constprop-init-regs 0 constmarks vals aignet copy aignet2)))
    (implies (and (equal (num-ins aignet) (num-ins aignet2))
                  (equal (num-regs aignet) (num-regs aignet2)))
             (aignet-input-copies-in-bounds copy aignet aignet2)))
  :hints(("Goal" :in-theory (enable aignet-input-copies-in-bounds))))
       



                        


(define aignet-constprop-conjoin-pi-values ((n natp :type (integer 0 *))
                                            (lit litp)
                                            constmarks
                                            vals
                                            aignet
                                            (gatesimp gatesimp-p)
                                            strash
                                            aignet2)
  :guard (and (eql (num-ins aignet) (num-ins aignet2))
              (fanin-litp lit aignet2)
              (<= n (num-ins aignet))
              (<= (num-fanins aignet) (bits-length constmarks))
              (<= (num-fanins aignet) (bits-length vals)))
  :returns (mv (new-lit litp :rule-classes :type-prescription)
               new-strash new-aignet2)
  :verify-guards nil
  :measure (nfix (- (num-ins aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-ins aignet) (nfix n)))
                   :exec (int= n (num-ins aignet))))
        (b* ((aignet2 (aignet-fix aignet2)))
          (mv (lit-fix lit) strash aignet2)))
       (id (innum->id n aignet))
       ((unless (int= (get-bit id constmarks) 1))
        (aignet-constprop-conjoin-pi-values (1+ (lnfix n)) lit constmarks vals aignet gatesimp strash aignet2))
       ((mv new-lit strash aignet2) (aignet-hash-and
                                     lit
                                     (mk-lit (innum->id n aignet2)
                                             (b-not (get-bit id vals)))
                                     gatesimp strash aignet2)))
    (aignet-constprop-conjoin-pi-values (1+ (lnfix n)) new-lit constmarks vals aignet gatesimp strash aignet2))
  ///
  (def-aignet-preservation-thms aignet-constprop-conjoin-pi-values :stobjname aignet2)

  (verify-guards aignet-constprop-conjoin-pi-values
    :hints((and stable-under-simplificationp
                '(:in-theory (enable aignet-litp)))))

  (defret stypes-preserved-of-<fn>
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (local (defthm lit-eval-of-make-lit
           (equal (lit-eval (make-lit id neg) invals regvals aignet)
                  (b-xor neg (id-eval id  invals regvals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval)))))

  (local (defthm not-<-n-n
           (not (< n n))))

  (local (defthm b-xor-b-not-equal-1
           (equal (equal (b-xor x (b-not y)) 1)
                  (equal (bfix x) (bfix y)))
           :hints(("Goal" :in-theory (enable b-xor b-not)))))

  (defret eval-of-<fn>
    (implies (equal (num-ins aignet) (num-ins aignet2))
             (equal (lit-eval new-lit invals regvals new-aignet2)
                    (b-and (bool->bit (constprop-marked-pis-true n constmarks vals aignet invals regvals))
                           (lit-eval lit invals regvals aignet2))))
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 '(:in-theory (enable bool->bit)))))

  (defret aignet-litp-of-<fn>
    (implies (aignet-litp lit aignet2)
             (aignet-litp new-lit new-aignet2)))

  (defret stype-count-of-<fn>
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (def-aignet-preservation-thms aignet-constprop-conjoin-pi-values :stobjname aignet2))


(define aignet-constprop-conjoin-reg-values ((n natp :type (integer 0 *))
                                             (lit litp)
                                             constmarks
                                             vals
                                             aignet
                                             (gatesimp gatesimp-p)
                                             strash
                                             aignet2)
  :guard (and (eql (num-regs aignet) (num-regs aignet2))
              (fanin-litp lit aignet2)
              (<= n (num-regs aignet))
              (<= (num-fanins aignet) (bits-length constmarks))
              (<= (num-fanins aignet) (bits-length vals)))
  :returns (mv (new-lit litp :rule-classes :type-prescription)
               new-strash new-aignet2)
  :verify-guards nil
  :measure (nfix (- (num-regs aignet) (nfix n)))
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (int= n (num-regs aignet))))
        (b* ((aignet2 (aignet-fix aignet2)))
          (mv (lit-fix lit) strash aignet2)))
       (id (regnum->id n aignet))
       ((unless (int= (get-bit id constmarks) 1))
        (aignet-constprop-conjoin-reg-values (1+ (lnfix n)) lit constmarks vals aignet gatesimp strash aignet2))
       ((mv new-lit strash aignet2) (aignet-hash-and
                                     lit
                                     (mk-lit (regnum->id n aignet2)
                                             (b-not (get-bit id vals)))
                                     gatesimp strash aignet2)))
    (aignet-constprop-conjoin-reg-values (1+ (lnfix n)) new-lit constmarks vals aignet gatesimp strash aignet2))
  ///
  (def-aignet-preservation-thms aignet-constprop-conjoin-reg-values :stobjname aignet2)

  (verify-guards aignet-constprop-conjoin-reg-values
    :hints((and stable-under-simplificationp
                '(:in-theory (enable aignet-litp)))))

  (defret stypes-preserved-of-aignet2
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (local (defthm lit-eval-of-make-lit
           (equal (lit-eval (make-lit id neg) invals regvals aignet)
                  (b-xor neg (id-eval id  invals regvals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval)))))

  (local (defthm not-<-n-n
           (not (< n n))))

  (local (defthm b-xor-b-not-equal-1
           (equal (equal (b-xor x (b-not y)) 1)
                  (equal (bfix x) (bfix y)))
           :hints(("Goal" :in-theory (enable b-xor b-not)))))

  (defret eval-of-<fn>
    (implies (equal (num-regs aignet) (num-regs aignet2))
             (equal (lit-eval new-lit invals regvals new-aignet2)
                    (b-and (bool->bit (constprop-marked-regs-true n constmarks vals aignet invals regvals))
                           (lit-eval lit invals regvals aignet2))))
    :hints (("goal" :induct <call>)
            (and stable-under-simplificationp
                 '(:in-theory (enable bool->bit)))))

  (defret aignet-litp-of-<fn>
    (implies (aignet-litp lit aignet2)
             (aignet-litp new-lit new-aignet2)))

  (defret stype-count-of-<fn>
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (def-aignet-preservation-thms aignet-constprop-conjoin-reg-values :stobjname aignet2))



(define aignet-lit-constprop ((lit litp :type (integer 0 *))
                              aignet
                              (gatesimp gatesimp-p)
                              strash
                              aignet2)
  :guard (and (fanin-litp lit aignet)
              (eql (num-ins aignet) (num-ins aignet2))
              (eql (num-regs aignet) (num-regs aignet2)))
  :split-types t
  :returns (mv (new-lit litp) new-strash new-aignet2)
  :verify-guards nil
  (b* (((acl2::local-stobjs mark constmarks vals copy)
        (mv new-lit strash aignet2 mark constmarks vals copy))
       (mark (resize-bits (num-fanins aignet) mark))
       (vals (resize-bits (num-fanins aignet) vals))
       (copy (resize-lits (num-fanins aignet) copy))
       (constmarks (resize-bits (num-fanins aignet) constmarks))
       
       ((mv constmarks vals)
        (aignet-mark-const-nodes-rec
         (lit-abs lit) aignet constmarks vals))

       (copy (aignet-constprop-init-pis 0 constmarks vals aignet copy aignet2))
       (copy (aignet-constprop-init-regs 0 constmarks vals aignet copy aignet2))

       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-rec (lit->var lit) aignet mark copy strash gatesimp aignet2))
       (new-lit (lit-copy (lit-abs lit) copy))
       ((mv new-lit strash aignet2)
        (aignet-constprop-conjoin-pi-values 0 new-lit constmarks vals aignet gatesimp strash aignet2))
       ((mv new-lit strash aignet2)
        (aignet-constprop-conjoin-reg-values 0 new-lit constmarks vals aignet gatesimp strash aignet2)))
    (mv (lit-negate-cond new-lit (lit->neg lit))
        strash aignet2 mark constmarks vals copy))

  ///
  (verify-guards aignet-lit-constprop
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp)))))

  (local (acl2::use-trivial-ancestors-check))

  (defret stype-count-of-aignet-lit-constprop
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (def-aignet-preservation-thms aignet-lit-constprop :stobjname aignet2)

  (defret aignet-litp-of-aignet-lit-constprop
    (implies (and (aignet-litp lit aignet)
                  (equal (num-ins aignet) (num-ins aignet2))
                  (equal (num-regs aignet) (num-regs aignet2)))
             (aignet-litp new-lit new-aignet2)))

  (local (defthm lit-eval-of-lit-abs
           (equal (lit-eval (make-lit (lit->var lit) 0) invals regvals aignet)
                  (b-xor (lit->neg lit)
                         (lit-eval lit invals regvals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval)))))

  (local (defthm b-xor-equals-1
           (equal (equal (b-xor a b) 1)
                  (not (equal (bfix a) (bfix b))))
           :hints(("Goal" :in-theory (enable b-xor)))))

  (defthm constprop-marked-regs-true-of-resize-empty
    (constprop-marked-regs-true n (resize-list nil sz 0) vals aignet invals regvals)
    :hints(("Goal" :in-theory (enable constprop-marked-regs-true))))

  (defthm constprop-marked-pis-true-of-resize-empty
    (constprop-marked-pis-true n (resize-list nil sz 0) vals aignet invals regvals)
    :hints(("Goal" :in-theory (enable constprop-marked-pis-true))))

  (defthm marked-nodes-invar-of-resize-nil
    (marked-nodes-invar (resize-list nil sz 0) vals invals regvals aignet)
    :hints(("Goal" :in-theory (enable marked-nodes-invar))))
                         

  (local (defthm nth-of-take
           (equal (nth i (take n l))
                  (and (< (nfix i) (nfix n))
                       (nth i l)))))

  (local (defthm lit-eval-of-make-lit
           (equal (lit-eval (make-lit id neg) invals regvals aignet)
                  (b-xor neg (id-eval id  invals regvals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval)))))

  (defthm input-copy-values-of-constprop-init-regs
    (bits-equiv (input-copy-values n invals regvals aignet
                                  (aignet-constprop-init-regs k constmarks vals aignet copy aignet2)
                                  aignet2)
               (input-copy-values n invals regvals aignet copy aignet2))
    :hints(("Goal" :in-theory (enable bits-equiv))
           (acl2::use-termhint
            (b* ((new-copy (aignet-constprop-init-regs k constmarks vals aignet copy aignet2))
                 (a (input-copy-values n invals regvals aignet new-copy aignet2))
                 (b (input-copy-values n invals regvals aignet copy aignet2))
                 (witness (acl2::bits-equiv-witness a b)))
              `'(:cases ((< (+ (nfix n) (nfix ,(acl2::hq witness))) (num-ins aignet))))))))

  (defthm input-copy-values-of-constprop-init-pis
    (implies (and (constprop-marked-pis-true 0 constmarks vals aignet invals regvals)
                  (equal (num-ins aignet) (num-ins aignet2)))
             (bits-equiv (input-copy-values 0 invals regvals aignet
                                            (aignet-constprop-init-pis 0 constmarks vals aignet copy aignet2)
                                            aignet2)
                         (take (num-ins aignet) invals)))
    :hints(("Goal" :in-theory (e/d (bits-equiv) (acl2::nth-of-take)))
           (acl2::use-termhint
            (b* ((new-copy (aignet-constprop-init-pis 0 constmarks vals aignet copy aignet2))
                 (a (input-copy-values 0 invals regvals aignet new-copy aignet2))
                 (b (take (num-ins aignet) invals))
                 (witness (acl2::bits-equiv-witness a b)))
              `'(:cases ((< (nfix ,(acl2::hq witness)) (num-ins aignet2))))))))

  (defthm reg-copy-values-of-constprop-init-pis
    (bits-equiv (reg-copy-values n invals regvals aignet
                                  (aignet-constprop-init-pis k constmarks vals aignet copy aignet2)
                                  aignet2)
               (reg-copy-values n invals regvals aignet copy aignet2))
    :hints(("Goal" :in-theory (enable bits-equiv))
           (acl2::use-termhint
            (b* ((new-copy (aignet-constprop-init-pis k constmarks vals aignet copy aignet2))
                 (a (reg-copy-values n invals regvals aignet new-copy aignet2))
                 (b (reg-copy-values n invals regvals aignet copy aignet2))
                 (witness (acl2::bits-equiv-witness a b)))
              `'(:cases ((< (+ (nfix n) (nfix ,(acl2::hq witness))) (num-regs aignet))))))))

  (defthm reg-copy-values-of-constprop-init-regs
    (implies (and (constprop-marked-regs-true 0 constmarks vals aignet invals regvals)
                  (equal (num-regs aignet) (num-regs aignet2)))
             (bits-equiv (reg-copy-values 0 invals regvals aignet
                                            (aignet-constprop-init-regs 0 constmarks vals aignet copy aignet2)
                                            aignet2)
                         (take (num-regs aignet) regvals)))
    :hints(("Goal" :in-theory (e/d (bits-equiv) (acl2::nth-of-take)))
           (acl2::use-termhint
            (b* ((new-copy (aignet-constprop-init-regs 0 constmarks vals aignet copy aignet2))
                 (a (reg-copy-values 0 invals regvals aignet new-copy aignet2))
                 (b (take (num-regs aignet) regvals))
                 (witness (acl2::bits-equiv-witness a b)))
              `'(:cases ((< (nfix ,(acl2::hq witness)) (num-regs aignet2))))))))

  (local (in-theory (disable lit-eval-of-make-lit)))

  (defret aignet-lit-constprop-correct
    (implies (and (equal (num-ins aignet) (num-ins aignet2))
                  (equal (num-regs aignet) (num-regs aignet2))
                  (aignet-litp lit aignet))
             (equal (lit-eval new-lit invals regvals new-aignet2)
                    (lit-eval lit invals regvals aignet)))
    :hints (("goal" :in-theory (enable bool->bit)
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((lit-eval lit invals regvals aignet))
                   :in-theory (enable lit-copy))))
    :otf-flg t))

(fty::defprod constprop-config
  ((gatesimp gatesimp-p :default (default-gatesimp)
             "Gate simplification parameters")
   (iterations posp :default 1
               "Number of times to repeat the transform."))
  :parents (constprop comb-transform)
  :short "Configuration object for the @(see constprop) aignet transform."
  :tag :constprop-config)

(define constprop-once ((aignet "Input aignet")
                        (gatesimp gatesimp-p)
                        (aignet2 "New aignet -- will be emptied"))
  :returns (new-aignet2)
  ;; Note: this currently only runs aignet-constprop-lit on a single output
  ;; literal, so it only works (i.e. preserves combinational equivalence) if
  ;; the aignet has exactly one output and no regs.  It might suffice to
  ;; require that the number of nextstates is 0 instead of the number of regs.
  :guard (and (equal (num-outs aignet) 1)
              (equal (num-regs aignet) 0))
  (b* (((acl2::local-stobjs strash)
        (mv strash aignet2))
       (aignet2 (aignet-init 1 (num-regs aignet) (num-ins aignet) (num-fanins aignet) aignet2))
       (aignet2 (aignet-add-ins (num-ins aignet) aignet2))
       (aignet2 (aignet-add-regs (num-regs aignet) aignet2))
       ((mv out-lit strash aignet2)
        (aignet-lit-constprop (outnum->fanin 0 aignet)
                              aignet gatesimp strash aignet2))
       (aignet2 (aignet-add-out out-lit aignet2)))
    (mv strash aignet2))
  ///
  (defret stype-count-of-<fn>
    (and (equal (stype-count :pi new-aignet2)
                (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2)
                (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2) 1)
         (equal (stype-count :nxst new-aignet2) 0)
         (equal (stype-count :const new-aignet2) 0)))

  (defret <fn>-preserves-comb-equiv
    (implies (and (equal (stype-count :po aignet) 1)
                  (equal (stype-count :reg aignet) 0))
             (comb-equiv new-aignet2 aignet))
    :hints(("Goal" :in-theory (e/d (comb-equiv outs-comb-equiv nxsts-comb-equiv output-eval nxst-eval)
                                   (acl2::zp-open))
            :expand ((:free (a b) (lookup-stype 0 :po (cons a b))))
            :cases ((zp (mv-nth 0 (outs-comb-equiv-witness new-aignet2 aignet)))))))

  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (let ((aignet2 nil)) <call>)))))

(define constprop-iter ((iters posp)
                        (aignet "input aignet")
                        (gatesimp gatesimp-p)
                        (aignet2 "New aignet -- will be emptied"))
  :returns (new-aignet2)
  :guard (and (equal (num-outs aignet) 1)
              (equal (num-regs aignet) 0))
  :measure (lposfix iters)
  :verify-guards nil
  (b* (((when (eql (lposfix iters) 1))
        (time$ (constprop-once aignet gatesimp aignet2)
               :msg "   - constprop-once: ~st seconds, ~sa bytes.~%"))
       ((acl2::local-stobjs aignet-tmp)
        (mv aignet-tmp aignet2))
       ;; Doing it this way is awkward, but makes it so that we don't keep
       ;; around a stack of completed aignets, just a stack of empty ones:
       ;; each call of constprop-iter only populates its input
       ;; aignet2 as its last step, and all the previous transforms are done
       ;; in a recursive call that writes to an empty local aignet.
       (aignet-tmp (constprop-iter (1- (lposfix iters)) aignet gatesimp aignet-tmp))
       (- (cw "Constprop iteration ~x0:" (1- (lposfix iters)))
          (print-aignet-stats "" aignet-tmp))
       (aignet2 (time$ (constprop-once aignet-tmp gatesimp aignet2)
                       :msg "   - constprop-once: ~st seconds, ~sa bytes.~%")))
    (mv aignet-tmp aignet2))
  ///
  (defret stype-count-of-<fn>
    (and (equal (stype-count :pi new-aignet2)
                (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2)
                (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2) 1)
         (equal (stype-count :nxst new-aignet2) 0)
         (equal (stype-count :const new-aignet2) 0)))

  (defret <fn>-preserves-comb-equiv
    (implies (and (equal (stype-count :po aignet) 1)
                  (equal (stype-count :reg aignet) 0))
             (comb-equiv new-aignet2 aignet)))

  (verify-guards constprop-iter)

  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (let ((aignet2 nil)) <call>)))))

(define constprop-core (aignet
                        aignet2
                        (config constprop-config-p))
  :returns (new-aignet2)
  (b* (((unless (and (eql (num-outs aignet) 1)
                     (eql (num-regs aignet) 0)))
        (b* ((aignet2 (aignet-raw-copy aignet aignet2)))
          (aignet-fix aignet2)))
       ((constprop-config config)))
    (constprop-iter config.iterations aignet config.gatesimp aignet2))
  
  ///
  (defret stype-count-of-<fn>
    (and (equal (stype-count :pi new-aignet2)
                (stype-count :pi aignet))
         (equal (stype-count :reg new-aignet2)
                (stype-count :reg aignet))
         (equal (stype-count :po new-aignet2)
                (stype-count :po aignet))))

  (defret <fn>-preserves-comb-equiv
    (comb-equiv new-aignet2 aignet))

  (defret normalize-inputs-of-<fn>
    (implies (syntaxp (not (equal aignet2 ''nil)))
             (equal <call>
                    (let ((aignet2 nil)) <call>)))))



(define constprop ((aignet  "Input aignet")
                   (aignet2 "New aignet -- will be emptied")
                   (config constprop-config-p
                           "Settings for the transform"))
  :parents (aignet-comb-transforms)
  :short "Simplify a single-output aignet by assuming inputs from a top-level conjunction
          to be true."
  :long "<p>Note: This should only be run on a single-output combinational
aignet.  In the current implementation it will return a copy of the original
aignet otherwise; if we did attempt to apply the transform to each
combinational output in a network having more than one, we might increase the
size of the network.</p>

<p>This transform searches the top-level AND or OR gate nest of the output
formula for conjuncts/disjuncts that are simply combinational inputs or their
negations.  It then rephrases the formula as follows.  Suppose F is the
top-level formula and C is the conjunction of all the inputs/negations.  Let
@('F\C') denote the substitution into F of the required values of all the
inputs in C, that is, if an input A appears non-negated in C, then it is
replaced by 1, and if it appears negated it is replaced by 0.  Then F is
equivalent to @('F\C & C').  This sometimes decreases the size of the formula
because the conjuncts within C may have other occurrences not in the top-level
conjunction of F.</p>"
  :guard-debug t
  :returns new-aignet2
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet2 aignet-tmp))
       (aignet-tmp (constprop-core aignet aignet-tmp config))
       (aignet2 (aignet-prune-comb aignet-tmp aignet2 (constprop-config->gatesimp config))))
    (mv aignet2 aignet-tmp))
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
                    (let ((aignet2 nil)) <call>)))))


(define constprop! ((aignet  "Input aignet -- will be replaced with transformation result")
                    (config constprop-config-p))
  :guard-debug t
  :returns new-aignet
  :parents (constprop)
  :short "Like @(see constprop), but overwrites the original network instead of returning a new one."
  (b* (((acl2::local-stobjs aignet-tmp)
        (mv aignet aignet-tmp))
       (aignet-tmp (constprop-core aignet aignet-tmp config))
       (aignet (aignet-prune-comb aignet-tmp aignet (constprop-config->gatesimp config))))
    (mv aignet aignet-tmp))
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
    (comb-equiv new-aignet aignet)))
    
