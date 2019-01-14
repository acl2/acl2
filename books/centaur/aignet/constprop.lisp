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
(include-book "sweep")

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

(define aignet-constprop-sweep-invar ((n natp)
                                      invals regvals
                                      aignet
                                      copy
                                      aignet2)
  :guard (and (<= n (num-fanins aignet))
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-ins aignet2) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals))
              (<= (num-regs aignet2) (bits-length regvals))
              (<= n (lits-length copy))
              (aignet-copies-in-bounds copy aignet2))
  :guard-hints (("goal" :in-theory (enable aignet-idp)))
  (if (zp n)
      t
    (let ((n (1- n)))
      (and (equal (id-eval n invals regvals aignet)
                  (lit-eval (get-lit n copy) invals regvals aignet2))
           (aignet-constprop-sweep-invar n invals regvals aignet copy aignet2))))
  ///
  (defthm aignet-constprop-sweep-invar-implies
    (implies (and (aignet-constprop-sweep-invar n invals regvals aignet copy aignet2)
                  (< (nfix m) (nfix n)))
             (equal (lit-eval (nth-lit m copy) invals regvals aignet2)
                    (id-eval m invals regvals aignet))))

  (defthm aignet-constprop-sweep-invar-implies-lit-eval-copy
    (implies (and (aignet-constprop-sweep-invar n invals regvals aignet copy aignet2)
                  (< (lit->var m) (nfix n)))
             (equal (lit-eval (lit-copy m copy) invals regvals aignet2)
                    (lit-eval m invals regvals aignet)))
    :hints(("Goal" :in-theory (enable lit-copy lit-eval))))

  (defthm aignet-constprop-sweep-invar-of-aignet-extension
    (implies (and (aignet-extension-binding)
                  (aignet-constprop-sweep-invar n invals regvals aignet copy orig)
                  (aignet-copies-in-bounds copy orig))
             (aignet-constprop-sweep-invar n invals regvals aignet copy new)))

  (defthm aignet-constprop-sweep-invar-of-update-later
    (implies (and (aignet-constprop-sweep-invar n invals regvals aignet copy aignet2)
                  (<= (nfix n) (nfix m)))
             (aignet-constprop-sweep-invar n invals regvals aignet
                                           (update-nth-lit m lit copy) aignet2)))

  (defthm aignet-constprop-sweep-invar-1
    (implies (equal 0 (nth-lit 0 copy))
             (aignet-constprop-sweep-invar 1 invals regvals aignet copy aignet2))
    :hints (("goal" :expand ((aignet-constprop-sweep-invar 1 invals regvals aignet copy aignet2)))))

  (defthm aignet-constprop-sweep-invar-when-greater
    (implies (and (aignet-constprop-sweep-invar n invals regvals aignet copy aignet2)
                  (<= (nfix m) (nfix n)))
             (aignet-constprop-sweep-invar m invals regvals aignet copy aignet2))))


(define aignet-constprop-sweep ((n posp :type (unsigned-byte 29))
                                constmarks
                                litclasses
                                aignet
                                (constr-lit litp)
                                copy
                                (gatesimp gatesimp-p :type (unsigned-byte 6))
                                strash
                                aignet2)
  :split-types t
  ;; All copy entries below N are valid.
  :measure (nfix (- (num-fanins aignet) (pos-fix n)))
  :guard (and (<= n (num-fanins aignet))
              (<= (num-fanins aignet) (bits-length constmarks))
              (<= (num-fanins aignet) (lits-length litclasses))
              (<= (num-fanins aignet) (lits-length copy))
              (equal (num-regs aignet) (num-regs aignet2))
              (equal (num-ins aignet) (num-ins aignet2))
              (fanin-litp constr-lit aignet2)
              (aignet-copies-in-bounds copy aignet2)
              (ec-call (litclasses-orderedp litclasses)))
  :returns (mv new-copy
               (new-constr-lit litp)
               new-strash new-aignet2)
  :prepwork ((local (in-theory (disable lookup-stype-out-of-bounds
                                        default-car default-cdr
                                        acl2::posp-redefinition
                                        aignet-extension-simplify-lookup-stype-when-counts-same
                                        not))))
  ;; :prepwork ((local (in-theory (disable acl2::zp-open not))))
  ;; :guard-debug t
  (b* ((n (lposfix n))
       ((when (mbe :logic (zp (- (num-fanins aignet) n))
                   :exec (eql (num-fanins aignet) n)))
        (mbe :logic (non-exec (mv copy (lit-fix constr-lit) strash (node-list-fix aignet2)))
             :exec (mv copy constr-lit strash aignet2)))
       (type (id->type n aignet))
       ((when (eql type (gate-type)))
        ;; Recreate the gate
        (b* ((fanin0 (lit-copy (gate-id->fanin0 n aignet) copy))
             (fanin1 (lit-copy (gate-id->fanin1 n aignet) copy))
             ((mv lit strash aignet2)
              (if (eql (id->regp n aignet) 1)
                  (aignet-hash-xor fanin0 fanin1 gatesimp strash aignet2)
                (aignet-hash-and fanin0 fanin1 gatesimp strash aignet2)))
             (copy (set-lit n lit copy))
             ((acl2::hintcontext :gate)))
          (aignet-constprop-sweep (1+ n) constmarks litclasses aignet constr-lit copy gatesimp strash aignet2)))
       ((unless (eql type (in-type)))
        ;; const
        (b* ((copy (set-lit n 0 copy))
             ((acl2::hintcontext :const)))
          (aignet-constprop-sweep (1+ n) constmarks litclasses aignet constr-lit copy gatesimp strash aignet2)))
       
       ;; Input or reg.  Get the normal form...
       (norm-lit (id-normal-form n constmarks litclasses))
       (corresp-lit (make-lit (if (eql 1 (id->regp n aignet))
                                  (regnum->id (ci-id->ionum n aignet) aignet2)
                                (innum->id (ci-id->ionum n aignet) aignet2))
                              0))
       ((when (eql (lit->var norm-lit) n))
        ;; Set the copy to the corresponding input/reg and go on.
        (b* ((copy (set-lit n corresp-lit copy))
             ((acl2::hintcontext :no-replace-in)))
          (aignet-constprop-sweep (1+ n) constmarks litclasses aignet constr-lit copy gatesimp strash aignet2)))

       (norm-copy (lit-copy norm-lit copy))
       (copy (set-lit n norm-copy copy))
       ((mv unequal-lit strash aignet2) (aignet-hash-xor corresp-lit norm-copy gatesimp strash aignet2))
       ((mv next-constr-lit strash aignet2) (aignet-hash-and constr-lit (lit-negate unequal-lit) gatesimp strash aignet2))
       ((acl2::hintcontext :replace-in)))
    (aignet-constprop-sweep (1+ n) constmarks litclasses aignet next-constr-lit copy gatesimp strash aignet2))
  ///
  (local (in-theory (disable (:d aignet-constprop-sweep))))
  
  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))

  (def-aignet-preservation-thms aignet-constprop-sweep :stobjname aignet2)

  (defret <fn>-preserves-copy-length
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy)))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret <fn>-preserves-copies-in-bounds
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy new-aignet2))
    :hints (("goal" :induct <call> :expand (<call>))))

  

  (local (defthm lit-eval-of-lookup-input
           (implies (< (nfix n) (num-ins aignet))
                    (equal (lit-eval (make-lit (fanin-count (lookup-stype n :pi aignet)) 0)
                                     invals regvals aignet)
                           (bfix (nth n invals))))
           :hints(("Goal" :in-theory (enable lit-eval id-eval)))))

  (local (defthm lit-eval-of-lookup-reg
           (implies (< (nfix n) (num-regs aignet))
                    (equal (lit-eval (make-lit (fanin-count (lookup-stype n :reg aignet)) 0)
                                     invals regvals aignet)
                           (bfix (nth n regvals))))
           :hints(("Goal" :in-theory (enable lit-eval id-eval)))))

  (defret stype-count-of-<fn>
    (implies (and (not (equal (stype-fix stype) :and))
                  (not (equal (stype-fix stype) :xor)))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2)))
    :hints (("goal" :induct <call> :expand (<call>))))
  
  (set-ignore-ok t)

  ;; (defret aignet-constprop-sweep-invar-when-litclasses-invar-of-<fn>
  ;;   (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
  ;;                 (aignet-constprop-sweep-invar (pos-fix n) invals regvals aignet copy aignet2)
  ;;                 (aignet-copies-in-bounds copy aignet2)
  ;;                 (equal (num-ins aignet2) (num-ins aignet))
  ;;                 (equal (num-regs aignet2) (num-regs aignet)))
  ;;            (aignet-constprop-sweep-invar (+ 1 (fanin-count aignet)) invals regvals aignet new-copy new-aignet2))
  ;;   :hints(("Goal" :induct <call>
  ;;           :expand ((:free (copy aignet2)
  ;;                     (aignet-constprop-sweep-invar (+ 1 (pos-fix n)) invals regvals aignet copy aignet2))
  ;;                    (id-eval (pos-fix n) invals regvals aignet)
  ;;                    <call>)
  ;;           :in-theory (enable eval-and-of-lits eval-xor-of-lits))))

  (defret aignet-litp-constr-lit-of-<fn>
    (implies (and (aignet-litp constr-lit aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (aignet-litp new-constr-lit new-aignet2))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret <fn>-constr-lit-ok-implies-previous
    (implies (And (equal 0 (lit-eval constr-lit invals regvals aignet2))
                  (aignet-litp constr-lit aignet2)
                  (aignet-copies-in-bounds copy aignet2))
             (equal (lit-eval new-constr-lit invals regvals new-aignet2) 0))
    :hints (("goal" :induct <call> :expand (<call>))))

  (defret aignet-constprop-sweep-invar-when-constr-of-<fn>
    (implies (and (equal (lit-eval new-constr-lit invals regvals new-aignet2) 1)
                  (aignet-constprop-sweep-invar (pos-fix n) invals regvals aignet copy aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (equal (num-ins aignet2) (num-ins aignet))
                  (equal (num-regs aignet2) (num-regs aignet)))
             (aignet-constprop-sweep-invar (+ 1 (fanin-count aignet)) invals regvals aignet new-copy new-aignet2))
    :hints(("Goal" :induct <call>
            :expand ((:free (copy aignet2)
                      (aignet-constprop-sweep-invar (+ 1 (pos-fix n)) invals regvals aignet copy aignet2))
                     (id-eval (pos-fix n) invals regvals aignet)
                     <call>)
            :in-theory (enable eval-and-of-lits eval-xor-of-lits))
           (acl2::function-termhint
            aignet-constprop-sweep
            (:replace-in
             ;; instantiate constr-lit-ok-implies-previous for the recursive call so we get the constraint on the lits
             `(:use ((:instance aignet-constprop-sweep-constr-lit-ok-implies-previous
                      (constr-lit ,(acl2::hq next-constr-lit))
                      (copy ,(acl2::hq copy))
                      (strash ,(acl2::hq strash))
                      (aignet2 ,(acl2::hq aignet2))
                      (n ,(acl2::hq (1+ n)))))
               :in-theory (disable aignet-constprop-sweep-constr-lit-ok-implies-previous)
               :do-not '(generalize fertilize)
               :do-not-induct t))
            )))

  (defret litclasses-invar-implies-constraint-satisfied-of-<fn>
    (implies (and (litclasses-invar invals regvals constmarks litclasses aignet)
                  (aignet-constprop-sweep-invar (pos-fix n) invals regvals aignet copy aignet2)
                  (equal (lit-eval constr-lit invals regvals aignet2) 1)
                  (aignet-litp constr-lit aignet2)
                  (aignet-copies-in-bounds copy aignet2)
                  (equal (num-ins aignet2) (num-ins aignet))
                  (equal (num-regs aignet2) (num-regs aignet)))
             (equal (lit-eval new-constr-lit invals regvals new-aignet2) 1))
    :hints(("Goal" :induct <call>
            :expand ((:free (copy aignet2)
                      (aignet-constprop-sweep-invar (+ 1 (pos-fix n)) invals regvals aignet copy aignet2))
                     (id-eval (pos-fix n) invals regvals aignet)
                     <call>)
            :in-theory (enable eval-and-of-lits eval-xor-of-lits xor)
            )))

  (defret <fn>-preserves-past-copy-lits
    (implies (< (nfix m) (pos-fix n))
             (equal (nth-lit m new-copy)
                    (nth-lit m copy)))
    :hints (("goal" :induct <call> :expand (<call>)))))


        



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
  (b* (((acl2::local-stobjs constmarks litclasses copy)
        (mv new-lit strash aignet2 constmarks litclasses copy))
       (copy (resize-lits (num-fanins aignet) copy))

       ((acl2::hintcontext-bind ((orig-constmarks constmarks)
                                 (orig-litclasses litclasses))))
       
       ((mv contra constmarks litclasses)
        (aignet-mark-const-nodes-top
         (lit-abs lit) aignet constmarks litclasses))

       ((when contra)
        (b* ((ans (make-lit 0 (lit->neg lit)))
             (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2))
             ((acl2::hintcontext :contra)))
          ;; (lit-abs lit) is constant false.  That means just return the aignet2
          ;; without any nodes and with the constant lit based on (lit->neg lit).
          (mv ans strash aignet2 constmarks litclasses copy)))

       ((acl2::hintcontext-bind ((orig-copy copy)
                                 (orig-strash strash)
                                 (orig-aignet2 aignet2))))

       ((mv copy constr-lit strash aignet2)
        (aignet-constprop-sweep 1 ;; start iteration at 1, skipping constant node
                                constmarks litclasses aignet
                                1 ;; constant-true lit, initial constraint
                                copy gatesimp strash aignet2))

       ;; For a given evaluation environment:
       ;; If (lit-abs lit) evaluates to 1:
       ;;   - this implies litclasses-invar
       ;;   - litclasses-invar implies constraint true
       ;;   - constraint true implies aignet-constprop-sweep-invar
       ;;   - aignet-constprop-sweep-invar implies copy of (lit-abs lit) is 1
       ;;   - constraint & copy of (lit-abs lit) = 1
       ;; If (lit-abs lit) evaluates to 0:
       ;;   - if constraint true, this implies aignet-constprop-sweep-invar
       ;;     - so copy of (lit-abs lit) is 0)
       ;;     - so constraint & copy of (lit-abs lit) = 0
       ;;   - if constraint false, then constraint & copy of (lit-abs lit) = 0.
       ((mv conj strash aignet2)
        (aignet-hash-and constr-lit (lit-copy (lit-abs lit) copy) gatesimp strash aignet2))

       (result-lit (lit-negate-cond conj (lit->neg lit)))
       ((acl2::hintcontext :no-contra)))
    (mv result-lit
        strash aignet2 constmarks litclasses copy))

  ///
  (verify-guards aignet-lit-constprop
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable aignet-idp))))
    :guard-debug t)

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

  ;; (defthm constprop-marked-regs-true-of-resize-empty
  ;;   (constprop-marked-regs-true n (resize-list nil sz 0) vals aignet invals regvals)
  ;;   :hints(("Goal" :in-theory (enable constprop-marked-regs-true))))

  ;; (defthm constprop-marked-pis-true-of-resize-empty
  ;;   (constprop-marked-pis-true n (resize-list nil sz 0) vals aignet invals regvals)
  ;;   :hints(("Goal" :in-theory (enable constprop-marked-pis-true))))

  ;; (defthm marked-nodes-invar-of-resize-nil
  ;;   (marked-nodes-invar (resize-list nil sz 0) vals invals regvals aignet)
  ;;   :hints(("Goal" :in-theory (enable marked-nodes-invar))))
  

  ;; (local (defthm nth-of-take
  ;;          (equal (nth i (take n l))
  ;;                 (and (< (nfix i) (nfix n))
  ;;                      (nth i l)))))

  ;; (local (defthm lit-eval-of-make-lit
  ;;          (equal (lit-eval (make-lit id neg) invals regvals aignet)
  ;;                 (b-xor neg (id-eval id  invals regvals aignet)))
  ;;          :hints(("Goal" :in-theory (enable lit-eval)))))

  ;; (defthm input-copy-values-of-constprop-init-regs
  ;;   (bits-equiv (input-copy-values n invals regvals aignet
  ;;                                 (aignet-constprop-init-regs k constmarks vals aignet copy aignet2)
  ;;                                 aignet2)
  ;;              (input-copy-values n invals regvals aignet copy aignet2))
  ;;   :hints(("Goal" :in-theory (enable bits-equiv))
  ;;          (acl2::use-termhint
  ;;           (b* ((new-copy (aignet-constprop-init-regs k constmarks vals aignet copy aignet2))
  ;;                (a (input-copy-values n invals regvals aignet new-copy aignet2))
  ;;                (b (input-copy-values n invals regvals aignet copy aignet2))
  ;;                (witness (acl2::bits-equiv-witness a b)))
  ;;             `'(:cases ((< (+ (nfix n) (nfix ,(acl2::hq witness))) (num-ins aignet))))))))

  ;; (defthm input-copy-values-of-constprop-init-pis
  ;;   (implies (and (constprop-marked-pis-true 0 constmarks vals aignet invals regvals)
  ;;                 (equal (num-ins aignet) (num-ins aignet2)))
  ;;            (bits-equiv (input-copy-values 0 invals regvals aignet
  ;;                                           (aignet-constprop-init-pis 0 constmarks vals aignet copy aignet2)
  ;;                                           aignet2)
  ;;                        (take (num-ins aignet) invals)))
  ;;   :hints(("Goal" :in-theory (e/d (bits-equiv) (acl2::nth-of-take)))
  ;;          (acl2::use-termhint
  ;;           (b* ((new-copy (aignet-constprop-init-pis 0 constmarks vals aignet copy aignet2))
  ;;                (a (input-copy-values 0 invals regvals aignet new-copy aignet2))
  ;;                (b (take (num-ins aignet) invals))
  ;;                (witness (acl2::bits-equiv-witness a b)))
  ;;             `'(:cases ((< (nfix ,(acl2::hq witness)) (num-ins aignet2))))))))

  ;; (defthm reg-copy-values-of-constprop-init-pis
  ;;   (bits-equiv (reg-copy-values n invals regvals aignet
  ;;                                 (aignet-constprop-init-pis k constmarks vals aignet copy aignet2)
  ;;                                 aignet2)
  ;;              (reg-copy-values n invals regvals aignet copy aignet2))
  ;;   :hints(("Goal" :in-theory (enable bits-equiv))
  ;;          (acl2::use-termhint
  ;;           (b* ((new-copy (aignet-constprop-init-pis k constmarks vals aignet copy aignet2))
  ;;                (a (reg-copy-values n invals regvals aignet new-copy aignet2))
  ;;                (b (reg-copy-values n invals regvals aignet copy aignet2))
  ;;                (witness (acl2::bits-equiv-witness a b)))
  ;;             `'(:cases ((< (+ (nfix n) (nfix ,(acl2::hq witness))) (num-regs aignet))))))))

  ;; (defthm reg-copy-values-of-constprop-init-regs
  ;;   (implies (and (constprop-marked-regs-true 0 constmarks vals aignet invals regvals)
  ;;                 (equal (num-regs aignet) (num-regs aignet2)))
  ;;            (bits-equiv (reg-copy-values 0 invals regvals aignet
  ;;                                           (aignet-constprop-init-regs 0 constmarks vals aignet copy aignet2)
  ;;                                           aignet2)
  ;;                        (take (num-regs aignet) regvals)))
  ;;   :hints(("Goal" :in-theory (e/d (bits-equiv) (acl2::nth-of-take)))
  ;;          (acl2::use-termhint
  ;;           (b* ((new-copy (aignet-constprop-init-regs 0 constmarks vals aignet copy aignet2))
  ;;                (a (reg-copy-values 0 invals regvals aignet new-copy aignet2))
  ;;                (b (take (num-regs aignet) regvals))
  ;;                (witness (acl2::bits-equiv-witness a b)))
  ;;             `'(:cases ((< (nfix ,(acl2::hq witness)) (num-regs aignet2))))))))

  ;; (local (in-theory (disable lit-eval-of-make-lit)))

  (set-ignore-ok t)

  (local (defthm lit-eval-of-const-lit
           (equal (lit-eval (make-lit 0 neg) invals regvals aignet)
                  (bfix neg))
           :hints(("Goal" :in-theory (enable lit-eval id-eval)))))

  (local (defthm lit-copy-of-lit-abs
           (equal (lit-copy (make-lit (lit->var lit) 0) copy)
                  (lit-negate-cond (lit-copy lit copy) (lit->neg lit)))
           :hints(("Goal" :in-theory (enable lit-copy lit-negate-cond)))))

  (defret aignet-lit-constprop-correct
    (implies (and (equal (num-ins aignet) (num-ins aignet2))
                  (equal (num-regs aignet) (num-regs aignet2))
                  (aignet-litp lit aignet))
             (equal (lit-eval new-lit invals regvals new-aignet2)
                    (lit-eval lit invals regvals aignet)))
    :hints ((acl2::function-termhint
             aignet-lit-constprop
             (:contra `(:use ((:instance aignet-mark-const-nodes-top-contra-correct
                               (lit ,(acl2::hq (lit-abs lit)))
                               (constmarks ,(acl2::hq orig-constmarks))
                               (litclasses ,(acl2::hq orig-litclasses)))
                              (:instance acl2::mark-clause-is-true
                               (x :contra)))
                        :in-theory (disable aignet-mark-const-nodes-top-contra-correct)))
             (:no-contra
              (if (equal (lit-eval (lit-abs lit) invals regvals aignet) 1)
                  `(:use ((:instance litclasses-invar-implies-constraint-satisfied-of-aignet-constprop-sweep
                           (constmarks ,(acl2::hq constmarks))
                           (litclasses ,(acl2::hq litclasses))
                           (aignet2 ,(acl2::hq orig-aignet2))
                           (strash ,(acl2::hq orig-strash))
                           (copy ,(acl2::hq orig-copy))
                           (n 1)
                           (constr-lit 1))
                          (:instance aignet-constprop-sweep-invar-when-constr-of-aignet-constprop-sweep
                           (constmarks ,(acl2::hq constmarks))
                           (litclasses ,(acl2::hq litclasses))
                           (aignet2 ,(acl2::hq orig-aignet2))
                           (strash ,(acl2::hq orig-strash))
                           (copy ,(acl2::hq orig-copy))
                           (n 1)
                           (constr-lit 1))
                          (:instance acl2::mark-clause-is-true
                           (x :no-contra-lit-true)))
                    :in-theory (e/d (b-and aignet-idp)
                                    (litclasses-invar-implies-constraint-satisfied-of-aignet-constprop-sweep
                                     aignet-constprop-sweep-invar-when-constr-of-aignet-constprop-sweep)))
                `(:use ((:instance aignet-constprop-sweep-invar-when-constr-of-aignet-constprop-sweep
                         (constmarks ,(acl2::hq constmarks))
                         (litclasses ,(acl2::hq litclasses))
                         (aignet2 ,(acl2::hq orig-aignet2))
                         (strash ,(acl2::hq orig-strash))
                         (copy ,(acl2::hq orig-copy))
                         (n 1)
                         (constr-lit 1))
                        
                        (:instance acl2::mark-clause-is-true
                         (x :no-contra-lit-false)))
                  :in-theory (e/d (b-and aignet-idp)
                                  (aignet-constprop-sweep-invar-when-constr-of-aignet-constprop-sweep)))))))
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
    
