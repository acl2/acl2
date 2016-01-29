; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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
(include-book "arrays")
(include-book "construction")
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable set::double-containment)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           set::double-containment
                           set::sets-are-true-lists
                           make-list-ac)))

(local (acl2::use-trivial-ancestors-check))

(local (in-theory (disable id-eval
                           true-listp
                           set::double-containment
                           acl2::nfix-when-not-natp
                           acl2::natp-when-integerp)))

(defstobj-clone copy litarr :prefix "COPY")

(defsection aignet-copies-ok

  ;; Copies:
  (defund aignet-copies-ok (n copy aignet)
    (declare (type (integer 0 *) n)
             (xargs :stobjs (copy aignet)
                    :guard (<= n (lits-length copy))
                    :guard-debug t))
    (if (zp n)
        t
      (and (fanin-litp (get-lit (1- n) copy) aignet)
           (aignet-copies-ok (1- n) copy aignet))))

  (local (in-theory (enable aignet-copies-ok)))

  (defthm aignet-copies-ok-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-extension-p new orig)
                  (aignet-copies-ok n copy orig))
             (aignet-copies-ok n copy new)))

  (defcong nat-equiv equal (aignet-copies-ok n copy aignet) 1)
  (defcong nth-equiv equal (nth-lit i x) 2 :hints(("Goal" :in-theory (enable nth-lit))))
  (defcong nth-equiv equal (aignet-copies-ok n copy aignet) 2)
  (defcong list-equiv equal (aignet-copies-ok n copy aignet) 3)

  (defthm aignet-copies-ok-of-update
    (implies (and (aignet-copies-ok n copy aignet)
                  (aignet-litp v aignet))
             (aignet-copies-ok
              n
              (update-nth-lit m v copy)
              aignet))
    :hints (("goal" :induct
             (aignet-copies-ok n copy aignet))))

  (defthm aignet-copies-ok-implies
    (implies (and (aignet-copies-ok n copy aignet)
                  (< (nfix k) (nfix n)))
             (aignet-litp (nth-lit k copy) aignet))
    :hints (("goal" :induct (aignet-copies-ok n copy aignet))))

  (defthm aignet-copies-ok-implies-special
    (implies (and (aignet-copies-ok (+ 1 (node-count aignet1)) copy aignet)
                  (aignet-idp k aignet1))
             (aignet-litp (nth-lit k copy) aignet))
    :hints (("goal" :in-theory (e/d (aignet-idp)
                                    (aignet-copies-ok)))))

  (local (defthm nth-lit-of-resize-list-split
           (equal (nth-lit n (resize-list x sz default))
                  (if (< (nfix n) (nfix sz))
                      (if (< (nfix n) (len x))
                          (nth-lit n x)
                        (lit-fix default))
                    0))
           :hints(("Goal" :in-theory (enable nth-lit resize-list)))))

  (defthm aignet-copies-ok-of-resize-list
    (implies (aignet-copies-ok n copy aignet)
             (aignet-copies-ok n (resize-list copy sz 0) aignet)))

  (local (defthm nth-lit-of-nil
           (equal (nth-lit n nil) 0)
           :hints(("Goal" :in-theory (enable nth-lit)))))

  (defthm aignet-copies-ok-of-nil
    (aignet-copies-ok n nil aignet)))

(defsection aignet-copy-comb

  (defmacro lit-copy (lit aignet-copyv)
    `(let ((lit-copy-lit ,lit))
       (lit-negate-cond (get-lit (lit-id lit-copy-lit) ,aignet-copyv)
                        (lit-neg lit-copy-lit))))

  (defiteration aignet-copy-comb (aignet copy gatesimp strash aignet2)
    (declare (type (integer 0 *) gatesimp)
             (xargs :stobjs (aignet copy strash aignet2)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-ok (num-nodes aignet) copy aignet2))
                    :guard-hints (("goal" :do-not-induct t
                                   :in-theory (enable aignet-idp)))))
    (b* ((n (lnfix n))
         (nid n)
         (slot0 (id->slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate (b* ((lit0 (snode->fanin slot0))
                  (lit1 (gate-id->fanin1 nid aignet))
                  ((mv lit strash aignet2)
                   (aignet-hash-and
                    (lit-copy lit0 copy)
                    (lit-copy lit1 copy)
                    gatesimp strash aignet2))
                  (copy (set-lit nid lit copy)))
               (mv copy strash aignet2))
       :in ;; assume already set up
       (mv copy strash aignet2)
       :out ;; -- output -- update copy numbers as fanins but don't add nodes
       (b* ((lit0 (snode->fanin slot0))
            (copy (set-lit nid (lit-copy lit0 copy) copy)))
         (mv copy strash aignet2))
       :const (b* ((copy (set-lit nid (to-lit 0) copy)))
                (mv copy strash aignet2))))
    :returns (mv copy strash aignet2)
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (in-theory (disable aignet-copy-comb))
  (local (in-theory (enable aignet-copy-comb)))

  (def-aignet-preservation-thms aignet-copy-comb-iter :stobjname aignet2)
  (def-aignet-preservation-thms aignet-copy-comb :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-comb-iter
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype (mv-nth 2 (aignet-copy-comb-iter
                                                  n aignet copy gatesimp strash
                                                  aignet2)))
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy gatesimp strash
                                    aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-comb
    (implies (not (equal (stype-fix stype) (gate-stype)))
             (equal (stype-count stype (mv-nth 2 (aignet-copy-comb
                                                  aignet copy gatesimp strash
                                                  aignet2)))
                    (stype-count stype aignet2))))


  (defthmd nth-in-aignet-copy-comb-iter-preserved
    (implies (and (< (nfix m) (nfix n))
                  (equal nm (1+ (nfix m)))
                  (syntaxp (not (equal n nm))))
             (equal (nth-lit m (mv-nth 0 (aignet-copy-comb-iter
                                          n aignet copy
                                          gatesimp strash aignet2)))
                    (nth-lit m (mv-nth 0 (aignet-copy-comb-iter
                                          nm aignet copy
                                          gatesimp strash aignet2)))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy gatesimp strash
                                    aignet2))
            '(:in-theory (disable b-xor b-and
                                  (:definition aignet-copy-comb-iter)))
            (and stable-under-simplificationp
                 '(:expand ((:free (m)
                             (aignet-copy-comb-iter
                             (+ 1 m)
                             aignet copy gatesimp strash aignet2))
                            (aignet-copy-comb-iter
                             n aignet copy gatesimp strash aignet2))))))


  (defthm aignet-copies-ok-of-aignet-copy-comb-iter
    (b* (((mv aignet-copy1 & aignet21)
          (aignet-copy-comb-iter
           n aignet copy gatesimp strash aignet2)))
      (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                    (<= (nfix n) (num-nodes aignet)))
               (aignet-copies-ok (+ 1 (node-count aignet)) aignet-copy1 aignet21)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy
                                    gatesimp strash aignet2))))

  (defthm aignet-copies-ok-of-aignet-copy-comb
    (b* (((mv aignet-copy1 & aignet21)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (implies (aignet-copies-ok (num-nodes aignet) copy aignet2)
               (aignet-copies-ok (+ 1 (node-count aignet)) aignet-copy1 aignet21)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy
                                    gatesimp strash aignet2))))

  (defthm aignet-copies-ok-of-aignet-copy-comb-litp
    (b* (((mv aignet-copy1 & aignet21)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                    (aignet-idp id aignet))
               (aignet-litp (nth-lit id aignet-copy1) aignet21)))
    :hints (("goal" :use ((:instance aignet-copies-ok-of-aignet-copy-comb))
             :in-theory (disable aignet-copies-ok-of-aignet-copy-comb
                                 aignet-copy-comb))))

  (defthm aignet-copy-comb-nth-previous
    (implies (<= (nfix n) (nfix m))
             (equal (nth-lit m (mv-nth 0 (aignet-copy-comb-iter
                                          n aignet copy
                                          gatesimp strash aignet2)))
                    (nth-lit m copy)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy
                                    gatesimp strash aignet2))))

  (defthm aignet-copy-sized-of-aignet-copy-comb-iter
    (implies (<= (num-nodes aignet) (lits-length copy))
             (< (node-count aignet)
                (len (mv-nth 0 (aignet-copy-comb-iter
                                n aignet copy gatesimp strash
                                aignet2)))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy
                                    gatesimp strash aignet2)))
    :rule-classes :linear)

  (defthm aignet-copy-sized-of-aignet-copy-comb
    (implies (<= (num-nodes aignet) (lits-length copy))
             (< (node-count aignet)
                (len (mv-nth 0 (aignet-copy-comb
                                aignet copy gatesimp strash
                                aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copy-comb-iter-inputs-preserved
    (b* (((mv aignet-copy1 & &)
          (aignet-copy-comb-iter
           n aignet copy gatesimp strash aignet2)))
      (implies (and (equal (id->type m aignet) (in-type)))
               (equal (nth-lit m aignet-copy1)
                      (nth-lit m copy))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy
                                    gatesimp strash aignet2))))

  (defthm aignet-copy-comb-inputs-preserved
    (b* (((mv aignet-copy1 & &)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (implies (and (equal (id->type m aignet) (in-type)))
               (equal (nth-lit m aignet-copy1)
                      (nth-lit m copy)))))

  (local (in-theory (disable aignet-copies-ok))))




(defsection aignet-copy-comb-in-vals
  (def-list-constructor aignet-copy-comb-in-vals
    (aignet-invals aignet-regvals aignet2 copy aignet)
    (declare (xargs :stobjs (aignet2 copy aignet aignet-invals aignet-regvals)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-ok (num-nodes aignet)
                                                  copy aignet2)
                                (<= (num-ins aignet2) (bits-length aignet-invals))
                                (<= (num-regs aignet2) (bits-length aignet-regvals)))))
    (b* ((in-id (innum->id n aignet))
         (copy-lit (get-lit in-id copy)))
      (lit-eval copy-lit aignet-invals aignet-regvals aignet2))
    :length (num-ins aignet))

  (local (set-default-hints
          '((and stable-under-simplificationp
                 (acl2::equal-by-nths-hint)))))

  (defthm aignet-copy-in-vals-of-extension
    (implies (and (aignet-extension-binding :new new2
                                            :orig aignet2)
                  (aignet-copies-ok (num-nodes aignet)
                                    copy aignet2))
             (equal (aignet-copy-comb-in-vals
                     aignet-invals aignet-regvals new2 copy aignet)
                    (aignet-copy-comb-in-vals
                     aignet-invals aignet-regvals aignet2 copy aignet))))

  ;; This holds because aignet-copy-comb doesn't touch the copy pointers of
  ;; CI nodes
  (defthm aignet-copy-in-vals-after-copy-comb-copy
    (b* (((mv aignet-copy2 & &)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (equal (aignet-copy-comb-in-vals
              aignet-invals aignet-regvals aignet22 aignet-copy2 aignet)
             (aignet-copy-comb-in-vals
              aignet-invals aignet-regvals aignet22 copy aignet)))))


(defsection aignet-copy-comb-reg-vals
  (def-list-constructor aignet-copy-comb-reg-vals
    (aignet-invals aignet-regvals aignet2 copy aignet)
    (declare (xargs :stobjs (aignet2 copy aignet aignet-invals aignet-regvals)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-ok (num-nodes aignet)
                                                  copy aignet2)
                                (<= (num-ins aignet2) (bits-length aignet-invals))
                                (<= (num-regs aignet2) (bits-length aignet-regvals)))))
    (b* ((reg-id (regnum->id n aignet))
         (copy-lit (get-lit reg-id copy)))
      (lit-eval copy-lit aignet-invals aignet-regvals aignet2))
    :length (num-regs aignet))


  (local (set-default-hints
          '((and stable-under-simplificationp
                 (acl2::equal-by-nths-hint)))))

  (defthm aignet-copy-reg-vals-of-extension
    (implies (and (aignet-extension-binding :new new2
                                            :orig aignet2)
                  (aignet-copies-ok (num-nodes aignet)
                                    copy aignet2))
             (equal (aignet-copy-comb-reg-vals
                         aignet-invals aignet-regvals new2 copy aignet)
                        (aignet-copy-comb-reg-vals
                         aignet-invals aignet-regvals aignet2 copy aignet))))

  (defthm aignet-copy-reg-vals-after-copy-comb-copy
    (b* (((mv aignet-copy2 & &)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (equal (aignet-copy-comb-reg-vals
              aignet-invals aignet-regvals aignet22 aignet-copy2 aignet)
             (aignet-copy-comb-reg-vals
              aignet-invals aignet-regvals aignet22 copy aignet)))))


(defsection aignet-copy-comb-correct

  (local
   (defun-sk eval-of-aignet-copy-comb-invariant
     (n aignet-invals aignet-regvals aignet-copy1 aignet21 aignet2 copy aignet)
     (forall m
             (implies (< (nfix m) (nfix n))
                      (equal (lit-eval (nth-lit m aignet-copy1)
                                       aignet-invals aignet-regvals aignet21)
                             (id-eval m
                                      (aignet-copy-comb-in-vals
                                       aignet-invals aignet-regvals aignet2 copy aignet)
                                      (aignet-copy-comb-reg-vals
                                       aignet-invals aignet-regvals aignet2 copy aignet)
                                      aignet))))
     :rewrite :direct))

  (local (in-theory (disable eval-of-aignet-copy-comb-invariant)))

  (local (defthm lit-eval-of-mk-lit
           (equal (lit-eval (mk-lit (lit-id lit) neg) aignet-invals aignet-regvals aignet)
                  (b-xor (b-xor neg (lit-neg lit))
                         (lit-eval lit aignet-invals aignet-regvals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval)))))


  (defthm aignet-litp-of-aignet-copy-comb-iter
    (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (< (nfix m) (num-nodes aignet))
                  (<= (nfix n) (num-nodes aignet)))
             (b* (((mv copy & aignet2)
                   (aignet-copy-comb-iter
                    n aignet copy
                    gatesimp strash aignet2)))
               (aignet-litp (nth-lit m copy) aignet2)))
    :hints (("goal" :use ((:instance aignet-copies-ok-of-aignet-copy-comb-iter))
             :in-theory (disable aignet-copies-ok-of-aignet-copy-comb-iter))))

  (local
   (defthm eval-of-aignet-copy-comb-lemma
     (implies (and (<= (nfix n) (num-nodes aignet))
                   (aignet-copies-ok (num-nodes aignet) copy aignet2))
              (b* (((mv aignet-copy1 & aignet21)
                    (aignet-copy-comb-iter
                     n aignet copy gatesimp strash aignet2)))
                (eval-of-aignet-copy-comb-invariant
                 n aignet-invals aignet-regvals aignet-copy1 aignet21 aignet2 copy aignet)))
     :hints (("goal" :induct (aignet-copy-comb-iter
                              n aignet copy gatesimp strash aignet2)
              :expand ((aignet-copy-comb-iter
                        n aignet copy gatesimp strash aignet2)))
             (and stable-under-simplificationp
                  `(:expand (,(car (last clause)))))
             (and stable-under-simplificationp
                  (let ((witness (acl2::find-call-lst
                                  'eval-of-aignet-copy-comb-invariant-witness
                                  clause)))
                    `(:clause-processor
                      (acl2::simple-generalize-cp
                       clause '((,witness . witness)))
                      :in-theory (enable eval-and-of-lits))))
             (and stable-under-simplificationp
                  '(:cases ((< (nfix witness) (nfix (+ -1 n))))))
             (and stable-under-simplificationp
                  '(:expand ((:free (aignet-invals aignet-regvals)
                              (id-eval witness aignet-invals
                                       aignet-regvals
                                       aignet))
                             (:free (aignet-invals aignet-regvals)
                              (id-eval (+ -1 n) aignet-invals
                                       aignet-regvals
                                       aignet))
                             (:free (lit invals regvals)
                              (lit-eval lit invals regvals aignet))))))))

  (defthm eval-of-aignet-copy-comb-iter
    (implies (and (<= (nfix n) (num-nodes aignet))
                  (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (< (nfix m) (nfix n)))
             (b* (((mv aignet-copy1 & aignet21)
                   (aignet-copy-comb-iter
                    n aignet copy gatesimp strash aignet2)))
               (equal (lit-eval (nth-lit m aignet-copy1)
                                aignet-invals aignet-regvals aignet21)
                      (id-eval m
                               (aignet-copy-comb-in-vals
                                aignet-invals aignet-regvals aignet2 copy aignet)
                               (aignet-copy-comb-reg-vals
                                aignet-invals aignet-regvals aignet2 copy aignet)
                               aignet))))
    :hints (("goal" :use ((:instance eval-of-aignet-copy-comb-lemma))
             :in-theory (disable eval-of-aignet-copy-comb-lemma))))

  (defthm eval-of-aignet-copy-comb
    (implies (and (aignet-copies-ok (num-nodes aignet) copy aignet2)
                  (< (nfix m) (num-nodes aignet)))
             (b* (((mv aignet-copy1 & aignet21)
                   (aignet-copy-comb aignet copy gatesimp strash aignet2)))
               (equal (lit-eval (nth-lit m aignet-copy1)
                                aignet-invals aignet-regvals aignet21)
                      (id-eval m
                               (aignet-copy-comb-in-vals
                                aignet-invals aignet-regvals aignet2 copy aignet)
                               (aignet-copy-comb-reg-vals
                                aignet-invals aignet-regvals aignet2 copy aignet)
                               aignet))))
    :hints(("Goal" :in-theory (enable aignet-copy-comb))))

)


(local (in-theory (disable acl2::nfix-when-not-natp
                           acl2::natp-when-integerp)))

  ;; Utilities for copying IOs

(defsection aignet-copy-ins


  ;; Adds a aignet2 PI for every PI of aignet, and sets the copy
  (defiteration aignet-copy-ins (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (<= (num-nodes aignet) (lits-length copy))))
    (b* ((inid (innum->id n aignet))
         (inlit (mk-lit (num-nodes aignet2) 0))
         (aignet2 (aignet-add-in aignet2))
         (copy (set-lit inid inlit copy)))
      (mv copy aignet2))
    :returns (mv copy aignet2)
    :last (num-ins aignet)
    :index n
    :package aignet::bla)

  (in-theory (disable aignet-copy-ins))
  (local (in-theory (enable (:induction aignet-copy-ins-iter)
                            aignet-copy-ins)))

  (def-aignet-preservation-thms aignet-copy-ins-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-ins-iter n aignet copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-ins-iter n aignet copy aignet2))
              (:free (copy) (aignet-copy-ins-iter n aignet copy aignet2))
              (:free (aignet2) (aignet-copy-ins-iter n aignet copy
                                                     aignet2))))
            '(:do-not-induct t))))

  (defthm stype-counts-preserved-of-aignet-copy-ins-iter
    (implies (not (equal (stype-fix stype) (pi-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-ins-iter
                                                  n aigne copy aignet2)))
                    (stype-count stype aignet2))))

  (defthm aignet-copy-size-of-aignet-copy-ins-iter
    (implies (<= (num-nodes aignet) (lits-length copy))
             (< (node-count aignet)
                (len (mv-nth 0 (aignet-copy-ins-iter
                                n aignet copy aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copies-ok-of-aignet-copy-ins-iter
    (implies (aignet-copies-ok (num-nodes aignet) copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-ins-iter n aignet copy aignet2)
               (aignet-copies-ok
                (+ 1 (node-count aignet))
                copy aignet2))))

  (local (defthm nfix-diff-zero
           (implies (<= a b)
                    (equal (nfix (+ (- b) a))
                           0))
           :hints(("Goal" :in-theory (enable nfix)))))

  (defthm num-ins-of-aignet-copy-ins-iter
    (equal (stype-count (pi-stype)
                        (mv-nth 1 (aignet-copy-ins-iter
                                   n aignet copy aignet2)))
           (+ (nfix n)
              (stype-count (pi-stype) aignet2))))

; (local (in-theory (enable* aignet-nodes-ok-strong-rules)))
  (defthm lookup-copy-of-aignet-copy-ins-iter
    (implies (and (aignet-idp id aignet)
                  (<= (nfix n) (num-ins aignet)))
             (b* (((mv aignet-copy-new aignet2-new)
                   (aignet-copy-ins-iter n aignet copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (equal (io-id->regp id aignet) 1)
                              (<= (nfix n) (io-id->ionum id aignet)))
                          (get-lit id copy)
                        (mk-lit
                         (node-count (lookup-stype (+ (io-id->ionum id aignet)
                                                      (num-ins aignet2))
                                                   (pi-stype) aignet2-new))
                         0)))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable equal-of-mk-lit
                                      lookup-stype-in-bounds)
                   :expand ((:free (n stype a b)
                             (lookup-stype n stype (cons a b))))))))

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-ins :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-ins
    (implies (not (equal (stype-fix stype) (pi-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-ins
                                                  aigne copy aignet2)))
                    (stype-count stype aignet2))))

  (defthm aignet-copy-size-of-aignet-copy-ins
    (implies (<= (num-nodes aignet) (lits-length copy))
             (< (node-count aignet)
                (len (mv-nth 0 (aignet-copy-ins aignet copy aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copies-ok-of-aignet-copy-ins
    (implies (aignet-copies-ok (num-nodes aignet) copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-ins aignet copy aignet2)
               (aignet-copies-ok
                (+ 1 (node-count aignet))
                copy aignet2))))

  (defthm num-ins-of-aignet-copy-ins
    (equal (stype-count (pi-stype) (mv-nth 1 (aignet-copy-ins
                                              aignet copy aignet2)))
           (+ (nfix (stype-count (pi-stype) aignet))
              (stype-count (pi-stype) aignet2))))


  (defthm lookup-copy-of-aignet-copy-ins
    (implies (and (aignet-idp id aignet))
             (b* (((mv aignet-copy-new aignet2-new)
                   (aignet-copy-ins aignet copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                                (equal (io-id->regp id aignet) 1))
                            (get-lit id copy)
                          (mk-lit
                           (node-count (lookup-stype (+ (nfix (io-id->ionum id aignet))
                                                        (num-ins aignet2))
                                                     (pi-stype) aignet2-new))
                           0))))))


  (defthm aignet-copy-comb-in-vals-of-aignet-copy-ins-nth
    (b* (((mv copy1 aignet21)
          (aignet-copy-ins aignet copy aignet2)))
      (implies (equal (num-ins aignet2) 0)
               (bit-equiv (nth n (aignet-copy-comb-in-vals
                                  invals regvals aignet21 copy1 aignet))
                          (and (< (nfix n) (num-ins aignet))
                               (nth n invals)))))
    :hints(("Goal" :in-theory (enable lit-eval id-eval))))

  (defthm aignet-copy-comb-in-vals-of-aignet-copy-ins
    (b* (((mv copy1 aignet21)
          (aignet-copy-ins aignet copy aignet2)))
      (implies (equal (num-ins aignet2) 0)
               (bits-equiv (aignet-copy-comb-in-vals
                            invals regvals aignet21 copy1 aignet)
                           (take (num-ins aignet) invals))))
    :hints (("goal" :in-theory (disable aignet-copy-comb-in-vals
                                        aignet-copy-ins))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-copy-comb-reg-vals-of-aignet-copy-ins-nth
    (b* (((mv copy1 aignet21)
          (aignet-copy-ins aignet copy aignet2)))
      (implies (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
               (bit-equiv (nth n (aignet-copy-comb-reg-vals
                                  invals regvals aignet21 copy1 aignet))
                          (nth n (aignet-copy-comb-reg-vals
                                  invals regvals aignet2 copy aignet)))))
    :hints(("Goal" :expand ((:free (n copy aignet)
                             (lit-eval (nth-lit n copy)
                                       invals regvals aignet))
                            (:free (n copy aignet)
                             (id-eval (lit-id (nth-lit n copy))
                                       invals regvals aignet)))
            :in-theory (enable nth-of-aignet-copy-comb-reg-vals-split))))

  (defthm aignet-copy-comb-reg-vals-of-aignet-copy-ins
    (b* (((mv copy1 aignet21)
          (aignet-copy-ins aignet copy aignet2)))
      (implies (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
               (bits-equiv (aignet-copy-comb-reg-vals
                            invals regvals aignet21 copy1 aignet)
                           (aignet-copy-comb-reg-vals
                            invals regvals aignet2 copy aignet))))
    :hints (("goal" :in-theory (disable aignet-copy-comb-reg-vals
                                        aignet-copy-ins))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(defsection aignet-copy-regs

  ;; Adds a aignet2 reg for every reg of aignet, and sets the copy
  (defiteration aignet-copy-regs (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (and (<= (num-nodes aignet) (lits-length copy)))))
    (b* ((ro (regnum->id n aignet))
         (reglit (mk-lit (num-nodes aignet2) 0))
         (aignet2 (aignet-add-reg aignet2))
         (copy (set-lit ro reglit copy)))
      (mv copy aignet2))
    :returns (mv copy aignet2)
    :last (num-regs aignet)
    :index n
    :package aignet::bla)


  (in-theory (disable aignet-copy-regs))
  (local (in-theory (enable (:induction aignet-copy-regs-iter)
                            aignet-copy-regs)))

  (def-aignet-preservation-thms aignet-copy-regs-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-regs-iter n aignet copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-regs-iter n aignet copy aignet2))
              (:free (copy) (aignet-copy-regs-iter n aignet copy aignet2))
              (:free (aignet2) (aignet-copy-regs-iter n aignet copy
                                                      aignet2))))
            '(:do-not-induct t))))

  (defthm stype-counts-preserved-of-aignet-copy-regs-iter
    (implies (not (equal (stype-fix stype) (reg-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-regs-iter
                                                  n aigne copy aignet2)))
                    (stype-count stype aignet2))))

  (defthm aignet-copy-size-of-aignet-copy-regs-iter
    (implies (<= (num-nodes aignet) (lits-length copy))
             (< (node-count aignet)
                (len (mv-nth 0 (aignet-copy-regs-iter n aignet copy
                                                      aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copies-ok-of-aignet-copy-regs-iter
    (implies (aignet-copies-ok (num-nodes aignet) copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-regs-iter n aignet copy aignet2)
               (aignet-copies-ok
                (+ 1 (node-count aignet))
                copy aignet2))))

  (local (defthmd dumb-num-regs-lemma
           (implies (<= n (stype-count (reg-stype) aignet))
                    (< (+ -1 n) (stype-count (reg-stype) aignet)))))

  (defthm num-regs-of-aignet-copy-regs-iter
    (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-regs-iter
                                               n aignet copy aignet2)))
           (+ (nfix n)
              (stype-count (reg-stype) aignet2))))

  (defthm lookup-copy-of-aignet-copy-regs-iter
    (implies (and (aignet-idp id aignet)
                  (<= (nfix n) (num-regs aignet)))
             (b* (((mv aignet-copy-new aignet2-new)
                   (aignet-copy-regs-iter n aignet copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (not (equal (io-id->regp id aignet) 1))
                              (<= (nfix n) (io-id->ionum id aignet)))
                          (get-lit id copy)
                        (mk-lit
                         (regnum->id (+ (nfix (io-id->ionum id aignet))
                                        (num-regs aignet2))
                                     aignet2-new)
                         0)))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable equal-of-mk-lit
                                      lookup-stype-in-bounds)
                   :expand ((:free (n stype a b)
                             (lookup-stype n stype (cons a b))))))))

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-regs :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-regs
    (implies (not (equal (stype-fix stype) (reg-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-regs
                                                  aigne copy aignet2)))
                    (stype-count stype aignet2))))

  (defthm aignet-copy-size-of-aignet-copy-regs
    (implies (<= (num-nodes aignet) (lits-length copy))
             (< (node-count aignet)
                (len (mv-nth 0 (aignet-copy-regs aignet copy
                                                 aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copies-ok-of-aignet-copy-regs
    (implies (aignet-copies-ok (num-nodes aignet) copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-regs aignet copy aignet2)
               (aignet-copies-ok
                (+ 1 (node-count aignet))
                copy aignet2))))

  (defthm num-regs-of-aignet-copy-regs
    (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-regs
                                               aignet copy aignet2)))
           (+ (nfix (num-regs aignet))
              (stype-count (reg-stype) aignet2))))

  (defthm lookup-copy-of-aignet-copy-regs
    (implies (and (aignet-idp id aignet))
             (b* (((mv aignet-copy-new aignet2-new)
                   (aignet-copy-regs aignet copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (not (equal (io-id->regp id aignet) 1)))
                          (get-lit id copy)
                        (mk-lit
                         (regnum->id (+ (nfix (io-id->ionum id aignet))
                                        (num-regs aignet2))
                                     aignet2-new)
                         0))))))

  (defthm aignet-copy-comb-reg-vals-of-aignet-copy-regs-nth
    (b* (((mv copy1 aignet21)
          (aignet-copy-regs aignet copy aignet2)))
      (implies (equal (num-regs aignet2) 0)
               (bit-equiv (nth n (aignet-copy-comb-reg-vals
                                  invals regvals aignet21 copy1 aignet))
                          (and (< (nfix n) (num-regs aignet))
                               (nth n regvals)))))
    :hints(("Goal" :in-theory (enable lit-eval id-eval))))

  (defthm aignet-copy-comb-reg-vals-of-aignet-copy-regs
    (b* (((mv copy1 aignet21)
          (aignet-copy-regs aignet copy aignet2)))
      (implies (equal (num-regs aignet2) 0)
               (bits-equiv (aignet-copy-comb-reg-vals
                            invals regvals aignet21 copy1 aignet)
                           (take (num-regs aignet) regvals))))
    :hints (("goal" :in-theory (disable aignet-copy-comb-reg-vals
                                        aignet-copy-regs))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-copy-comb-in-vals-of-aignet-copy-regs-nth
    (b* (((mv copy1 aignet21)
          (aignet-copy-regs aignet copy aignet2)))
      (implies (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
               (bit-equiv (nth n (aignet-copy-comb-in-vals
                                  invals regvals aignet21 copy1 aignet))
                          (nth n (aignet-copy-comb-in-vals
                                  invals regvals aignet2 copy aignet)))))
    :hints(("Goal" :expand ((:free (n copy aignet)
                             (lit-eval (nth-lit n copy)
                                       invals regvals aignet))
                            (:free (n copy aignet)
                             (id-eval (lit-id (nth-lit n copy))
                                      invals regvals aignet)))
            :in-theory (enable nth-of-aignet-copy-comb-in-vals-split))))

  (defthm aignet-copy-comb-in-vals-of-aignet-copy-regs
    (b* (((mv copy1 aignet21)
          (aignet-copy-regs aignet copy aignet2)))
      (implies (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
               (bits-equiv (aignet-copy-comb-in-vals
                            invals regvals aignet21 copy1 aignet)
                           (aignet-copy-comb-in-vals
                            invals regvals aignet2 copy aignet))))
    :hints (("goal" :in-theory (disable aignet-copy-comb-in-vals
                                        aignet-copy-regs))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))



(defsection aignet-copy-outs

  ;; Adds a aignet2 output for every output of aignet, using the stored copy
  ;; assumes the copy of each output ID is set to the fanin lit,
  ;; does not change this to the new node
  (defiteration aignet-copy-outs (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-ok (num-nodes aignet)
                                                  copy aignet2))))
    (b* ((outid (outnum->id n aignet))
         (fanin (get-lit outid copy)))
      (aignet-add-out fanin aignet2))
    :returns aignet2
    :last (num-outs aignet)
    :index n
    :package aignet::bla)

  (in-theory (disable aignet-copy-outs))
  (local (in-theory (enable (:induction aignet-copy-outs-iter)
                            aignet-copy-outs)))

  (def-aignet-preservation-thms aignet-copy-outs-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-outs-iter n aignet copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-outs-iter n aignet copy aignet2))
              (:free (copy) (aignet-copy-outs-iter n aignet copy aignet2))
              (:free (aignet2) (aignet-copy-outs-iter n aignet copy
                                                     aignet2))))
            '(:do-not-induct t))))

  (defthm stype-counts-preserved-of-aignet-copy-outs-iter
    (implies (not (equal (stype-fix stype) (po-stype)))
             (equal (stype-count stype
                                 (aignet-copy-outs-iter n aignet copy aignet2))
                    (stype-count stype aignet2))))

  (defthm num-outs-of-aignet-copy-outs-iter
    (equal (stype-count (po-stype)
                        (aignet-copy-outs-iter n aignet copy aignet2))
           (+ (nfix n)
              (stype-count (po-stype) aignet2))))

  (defthm lookup-output-of-aignet-copy-outs-iter
    (implies (and (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
                  (equal 0 (num-outs aignet2))
                  (< (nfix m) (nfix n))
                  (<= (nfix n) (num-outs aignet)))
             (b* ((aignet21 (aignet-copy-outs-iter n aignet copy aignet2))
                  (mth-out-look (lookup-stype m (po-stype) aignet21))
                  (fanin (nth-lit (node-count (lookup-stype m (po-stype) aignet))
                                  copy)))
               (and (consp mth-out-look)
                    (equal (car mth-out-look)
                           (po-node fanin))
                    (aignet-litp fanin (cdr mth-out-look)))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (n stype a b)
                             (lookup-stype n stype (cons a b))))))
            (and stable-under-simplificationp
                 '(:in-theory (enable lookup-stype-in-bounds)))))

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-outs :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-outs
    (implies (not (equal (stype-fix stype) (po-stype)))
             (equal (stype-count stype
                                 (aignet-copy-outs aignet copy aignet2))
                    (stype-count stype aignet2))))

  (defthm num-outs-of-aignet-copy-outs
    (equal (stype-count (po-stype)
                        (aignet-copy-outs aignet copy aignet2))
           (+ (stype-count (po-stype) aignet)
              (stype-count (po-stype) aignet2))))

  (defthm lookup-output-of-aignet-copy-outs
    (implies (and (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
                  (equal 0 (num-outs aignet2))
                  (< (nfix m) (num-outs aignet)))
             (b* ((aignet21 (aignet-copy-outs aignet copy aignet2))
                  (mth-out-look (lookup-stype m (po-stype) aignet21))
                  (fanin (nth-lit (node-count (lookup-stype m (po-stype) aignet))
                                  copy)))
               (and (consp mth-out-look)
                    (equal (car mth-out-look)
                           (po-node fanin))
                    (aignet-litp fanin (cdr mth-out-look)))))))


(defsection aignet-copy-nxsts


  ;; Adds a aignet2 regin for every register of aignet.
  ;; assumes the copy of each regin ID is set to the fanin lit,
  ;; does not change this to the new node.
  ;; Connects the regin to the corresponding reg in aignet2.  Therefore, we must
  ;; assume there are at least as many regs in aignet2 as in aignet.
  (defiteration aignet-copy-nxsts (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (<= (num-regs aignet) (num-regs aignet2))
                                (aignet-copies-ok (num-nodes aignet)
                                                  copy aignet2))))
    (b* ((nxst (reg-id->nxst (regnum->id n aignet) aignet))
         (fanin-copy (get-lit nxst copy))
         (ro-copy (regnum->id n aignet2)))
      (aignet-set-nxst fanin-copy ro-copy aignet2))
    :returns aignet2
    :last (num-regs aignet)
    :index n
    :package aignet::bla)

  (in-theory (disable aignet-copy-nxsts))
  (local (in-theory (enable (:induction aignet-copy-nxsts-iter)
                            aignet-copy-nxsts)))

  (def-aignet-preservation-thms aignet-copy-nxsts-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-nxsts-iter n aignet copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-nxsts-iter n aignet copy aignet2))
              (:free (copy) (aignet-copy-nxsts-iter n aignet copy aignet2))
              (:free (aignet2) (aignet-copy-nxsts-iter n aignet copy
                                                     aignet2))))
            '(:do-not-induct t))))

  (defthm stype-counts-preserved-of-aignet-copy-nxsts-iter
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype
                                 (aignet-copy-nxsts-iter n aignet copy aignet2))
                    (stype-count stype aignet2))))

  (local (in-theory (enable aignet-extension-implies-node-count-gte
                            lookup-stype-in-bounds)))

  (defthm lookup-nxst-of-aignet-copy-nxsts-iter
    (implies (and (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
                  (<= (nfix n) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2-orig))
                  (< (nfix m) (nfix n))
                  (aignet-extension-p aignet2 aignet2-orig))
             (b* ((aignet21 (aignet-copy-nxsts-iter n aignet copy aignet2))
                  (regid (node-count (lookup-stype m (reg-stype) aignet2-orig)))
                  (mth-nxst-look2 (lookup-reg->nxst regid aignet21))
                  (mth-nxst-look (lookup-reg->nxst
                                  (node-count (lookup-stype m (reg-stype) aignet))
                                  aignet))
                  (fanin (nth-lit (node-count mth-nxst-look)
                                  copy)))
               (and (consp mth-nxst-look2)
                    (equal (car mth-nxst-look2)
                           (nxst-node fanin regid))
                    (aignet-litp fanin (cdr mth-nxst-look2))
                    (aignet-idp regid (cdr mth-nxst-look2)))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (n stype a b)
                             (lookup-stype n stype (cons a b)))
                            (:free (n a b)
                             (lookup-reg->nxst n (cons a b))))))))

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-nxsts :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-nxsts
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype
                                 (aignet-copy-nxsts aignet copy aignet2))
                    (stype-count stype aignet2))))

  (defthm lookup-nxst-of-aignet-copy-nxsts
    (implies (and (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
                  (< (nfix m) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2-orig))
                  (aignet-extension-p aignet2 aignet2-orig))
             (b* ((aignet21 (aignet-copy-nxsts aignet copy aignet2))
                  (regid (node-count (lookup-stype m (reg-stype) aignet2-orig)))
                  (mth-nxst-look2 (lookup-reg->nxst regid aignet21))
                  (mth-nxst-look (lookup-reg->nxst
                                  (node-count (lookup-stype m (reg-stype) aignet))
                                  aignet))
                  (fanin (nth-lit (node-count mth-nxst-look)
                                  copy)))
               (and (consp mth-nxst-look2)
                    (equal (car mth-nxst-look2)
                           (nxst-node fanin regid))
                    (aignet-litp fanin (cdr mth-nxst-look2))
                    (aignet-idp regid (cdr mth-nxst-look2)))))))





(defsection out-of-bounds-lookup-lemmas
  (defthmd node-count-lookup-stype-when-out-of-bounds
    (implies (<= (stype-count stype aignet) (nfix n))
             (equal (node-count (lookup-stype n stype aignet))
                    0))
    :hints(("Goal" :in-theory (enable lookup-stype node-count stype-count))))

  (defthmd node-count-of-lookup-reg->nxst-0
    (equal (node-count (lookup-reg->nxst 0 aignet))
           0)
    :hints(("Goal" :in-theory (enable lookup-reg->nxst)))))


(defsection aignet-complete-copy

  (local (in-theory (enable lookup-stype-in-bounds)))
  (local (defthm resize-list-0
           (equal (resize-list lst 0 default)
                  nil)
           :hints(("Goal" :in-theory (enable resize-list)))))

  (define aignet-complete-copy-aux (aignet copy (gatesimp natp) strash aignet2)
    :returns (mv copy strash aignet2)
    :prepwork ((local (defthm strash-lemma
                        (implies (and (true-listp strash)
                                      (equal (len strash) 1))
                                 (equal (update-nth 0 nil strash)
                                        '(nil)))
                        :hints (("goal" :in-theory (enable update-nth))))))
    (b* ((aignet2 (aignet-init
                   (num-outs aignet)
                   (num-regs aignet)
                   (num-ins aignet)
                   (num-nodes aignet)
                   aignet2))
         (copy (resize-lits 0 copy))
         (strash (mbe :logic (non-exec '(nil))
                      :exec (strashtab-init (num-gates aignet) nil nil strash)))
         (copy (resize-lits (num-nodes aignet) copy))
         ((mv copy aignet2)
          (aignet-copy-ins aignet copy aignet2))
         ((mv copy aignet2)
          (aignet-copy-regs aignet copy aignet2))
         ((mv copy strash aignet2)
          (aignet-copy-comb aignet copy gatesimp strash aignet2))
         (aignet2 (aignet-copy-outs aignet copy aignet2))
         (aignet2 (aignet-copy-nxsts aignet copy aignet2)))
      (mv copy strash aignet2))
    ///

    (defthm normalize-aignet-complete-copy-aux
      (implies (syntaxp (not (and (equal copy ''nil)
                                  (equal strash ''(nil))
                                  (equal aignet2 ''nil))))
               (equal (aignet-complete-copy-aux aignet copy gatesimp strash
                                                aignet2)
                      (aignet-complete-copy-aux aignet nil gatesimp '(nil)
                                                nil))))

    (local (defthm id-eval-of-co-node
             (implies (equal (id->type id aignet) (out-type))
                      (equal (id-eval id invals regvals aignet)
                             (lit-eval (co-id->fanin id aignet)
                                       invals regvals aignet)))
             :hints(("Goal" :in-theory (enable id-eval)))))

    (local (in-theory (enable co-node->fanin)))

    (defthm id-eval-of-take-num-ins
      (equal (id-eval id (take (stype-count :pi aignet) invals)
                      regvals aignet)
             (id-eval id invals regvals aignet))
      :hints (("goal" :induct (id-eval-ind id aignet)
               :expand ((:free (invals regvals)
                         (id-eval id invals regvals aignet)))
               :in-theory (enable lit-eval eval-and-of-lits))))

    (defthm id-eval-of-take-num-regs
      (equal (id-eval id invals
                      (take (stype-count :reg aignet) regvals)
                      aignet)
             (id-eval id invals regvals aignet))
      :hints (("goal" :induct (id-eval-ind id aignet)
               :expand ((:free (invals regvals)
                         (id-eval id invals regvals aignet)))
               :in-theory (enable lit-eval eval-and-of-lits))))

    (defthm lit-eval-of-take-num-ins
      (equal (lit-eval lit (take (stype-count :pi aignet) invals)
                       regvals aignet)
             (lit-eval lit invals regvals aignet))
      :hints(("Goal"
              :expand ((:free (invals regvals)
                        (lit-eval lit invals regvals aignet))))))

    (defthm lit-eval-of-take-num-regs
      (equal (lit-eval lit invals
                       (take (stype-count :reg aignet) regvals)
                       aignet)
             (lit-eval lit invals regvals aignet))
      :hints(("Goal"
              :expand ((:free (invals regvals)
                        (lit-eval lit invals regvals aignet))))))

    (defthm eval-output-of-aignet-complete-copy-aux
      (b* (((mv & & aignet2) (aignet-complete-copy-aux aignet copy gatesimp
                                                       strash aignet2)))
        (equal (id-eval
                (node-count (lookup-stype n (po-stype) aignet2))
                invals regvals aignet2)
               (id-eval
                (node-count (lookup-stype n (po-stype) aignet))
                invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-outs aignet)))
               :in-theory (enable node-count-lookup-stype-when-out-of-bounds))))

    (defthm eval-nxst-of-aignet-complete-copy-aux
      (b* (((mv & & aignet2)
            (aignet-complete-copy-aux aignet copy gatesimp strash aignet2)))
        (equal (id-eval
                (node-count
                 (lookup-reg->nxst
                  (node-count (lookup-stype n (reg-stype)
                                            aignet2))
                  aignet2))
                invals regvals aignet2)
               (id-eval
                (node-count
                 (lookup-reg->nxst
                  (node-count (lookup-stype n (reg-stype)
                                            aignet))
                  aignet))
                invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-regs aignet)))
               :in-theory (enable node-count-lookup-stype-when-out-of-bounds
                                  node-count-of-lookup-reg->nxst-0))))

    (defthm num-outs-of-aignet-complete-copy-aux
      (equal (stype-count :po (mv-nth 2 (aignet-complete-copy-aux
                                         aignet copy gatesimp strash aignet2)))
             (stype-count :po aignet)))

    (defthm num-regs-of-aignet-complete-copy-aux
      (equal (stype-count :reg (mv-nth 2 (aignet-complete-copy-aux
                                         aignet copy gatesimp strash aignet2)))
             (stype-count :reg aignet)))

    (defthm comb-equiv-of-aignet-complete-copy-aux
      (comb-equiv (mv-nth 2 (aignet-complete-copy-aux
                            aignet copy gatesimp strash aignet2))
                  aignet)
      :hints(("Goal" :in-theory (e/d (comb-equiv)
                                     (aignet-complete-copy-aux))))))

  (define aignet-complete-copy (aignet &key
                                       ((gatesimp natp) '9)
                                       (aignet2 'aignet2))
    :returns aignet2
    :parents (aignet)
    :short "Copy an aignet, \"normalizing\" the order of nodes"
    :long "<p>Copies aignet into aignet2, in the following order:</p>
<ul><li>Primary inputs
</li><li>Registers
</li><li>Gates
</li><li>Primary outputs
</li><li>Next states
</li>
</ul>

<p>Every node in the original aignet has a copy in aignet2, so no particular
pruning is done.  However, if strashing or a higher level of simplification is
used than was used when constructing the original aignet, there may be fewer
nodes.</p>"
    (b* (((local-stobjs copy strash)
          (mv copy strash aignet2)))
      (aignet-complete-copy-aux aignet copy gatesimp strash aignet2))
    ///

    (defthm normalize-aignet-complete-copy
      (implies (syntaxp (equal aignet2 ''nil))
               (equal (aignet-complete-copy aignet :gatesimp gatesimp
                                            :aignet2 aignet2)
                      (aignet-complete-copy aignet :gatesimp gatesimp
                                            :aignet2 nil))))

    (defthm eval-output-of-aignet-complete-copy
      (b* ((aignet2 (aignet-complete-copy aignet :gatesimp gatesimp)))
        (equal (id-eval
                (node-count (lookup-stype n (po-stype) aignet2))
                invals regvals aignet2)
               (id-eval
                (node-count (lookup-stype n (po-stype) aignet))
                invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-outs aignet)))
               :in-theory (enable node-count-lookup-stype-when-out-of-bounds))))

    (defthm eval-nxst-of-aignet-complete-copy
      (b* ((aignet2 (aignet-complete-copy aignet :gatesimp gatesimp)))
        (equal (id-eval
                (node-count
                 (lookup-reg->nxst
                  (node-count (lookup-stype n (reg-stype)
                                            aignet2))
                  aignet2))
                invals regvals aignet2)
               (id-eval
                (node-count
                 (lookup-reg->nxst
                  (node-count (lookup-stype n (reg-stype)
                                            aignet))
                  aignet))
                invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-regs aignet)))
               :in-theory (enable node-count-lookup-stype-when-out-of-bounds
                                  node-count-of-lookup-reg->nxst-0))))

    (defthm num-outs-of-aignet-complete-copy
      (equal (stype-count :po (aignet-complete-copy aignet :gatesimp gatesimp))
             (stype-count :po aignet)))

    (defthm num-regs-of-aignet-complete-copy
      (equal (stype-count :reg (aignet-complete-copy aignet :gatesimp gatesimp))
             (stype-count :reg aignet)))

    (defthm comb-equiv-of-aignet-complete-copy
      (comb-equiv (aignet-complete-copy aignet :gatesimp gatesimp)
                  aignet))))




(defsection aignet-copy-regs-init

  ;; Adds a aignet2 reg for every reg of aignet, and sets the copy
  (defiteration aignet-copy-regs-init (aignet initsts copy aignet2)
    (declare (xargs :stobjs (aignet copy initsts aignet2)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (<= (num-regs aignet) (bits-length initsts)))))
    (b* ((ro (regnum->id n aignet))
         (inv (get-bit n initsts))
         (reglit (mk-lit (num-nodes aignet2) inv))
         (aignet2 (aignet-add-reg aignet2))
         (copy (set-lit ro reglit copy)))
      (mv copy aignet2))
    :returns (mv copy aignet2)
    :last (num-regs aignet)
    :index n
    :package aignet::bla)


  (in-theory (disable aignet-copy-regs-init))
  (local (in-theory (enable (:induction aignet-copy-regs-init-iter)
                            aignet-copy-regs-init)))

  (def-aignet-preservation-thms aignet-copy-regs-init-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-regs-init-iter n aignet initsts copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-regs-init-iter n aignet initsts copy aignet2))
              (:free (copy) (aignet-copy-regs-init-iter n aignet initsts copy aignet2))
              (:free (aignet2) (aignet-copy-regs-init-iter n aignet initsts copy
                                                      aignet2))))
            '(:do-not-induct t))))

  (defthm stype-counts-preserved-of-aignet-copy-regs-init-iter
    (implies (not (equal (stype-fix stype) (reg-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-regs-init-iter
                                                  n aignet initsts copy aignet2)))
                    (stype-count stype aignet2))))

  (defthm aignet-copy-size-of-aignet-copy-regs-init-iter
    (implies (<= (num-nodes aignet) (lits-length copy))
             (< (node-count aignet)
                (len (mv-nth 0 (aignet-copy-regs-init-iter n aignet initsts copy
                                                      aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copies-ok-of-aignet-copy-regs-init-iter
    (implies (aignet-copies-ok (num-nodes aignet) copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-regs-init-iter n aignet initsts copy aignet2)
               (aignet-copies-ok
                (+ 1 (node-count aignet))
                copy aignet2))))

  (local (defthmd dumb-num-regs-lemma
           (implies (<= n (stype-count (reg-stype) aignet))
                    (< (+ -1 n) (stype-count (reg-stype) aignet)))))

  (defthm num-regs-of-aignet-copy-regs-init-iter
    (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-regs-init-iter
                                               n aignet initsts copy aignet2)))
           (+ (nfix n)
              (stype-count (reg-stype) aignet2))))

  (defthm lookup-copy-of-aignet-copy-regs-init-iter
    (implies (and (aignet-idp id aignet)
                  (<= (nfix n) (num-regs aignet)))
             (b* (((mv aignet-copy-new aignet2-new)
                   (aignet-copy-regs-init-iter n aignet initsts copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (not (equal (io-id->regp id aignet) 1))
                              (<= (nfix n) (io-id->ionum id aignet)))
                          (get-lit id copy)
                        (mk-lit
                         (regnum->id (+ (nfix (io-id->ionum id aignet))
                                        (num-regs aignet2))
                                     aignet2-new)
                         (get-bit (io-id->ionum id aignet) initsts))))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable equal-of-mk-lit
                                      lookup-stype-in-bounds)
                   :expand ((:free (n stype a b)
                             (lookup-stype n stype (cons a b))))))))

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-regs-init :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-regs-init
    (implies (not (equal (stype-fix stype) (reg-stype)))
             (equal (stype-count stype (mv-nth 1 (aignet-copy-regs-init
                                                  aignet initsts copy aignet2)))
                    (stype-count stype aignet2))))

  (defthm aignet-copy-size-of-aignet-copy-regs-init
    (implies (<= (num-nodes aignet) (lits-length copy))
             (< (node-count aignet)
                (len (mv-nth 0 (aignet-copy-regs-init aignet initsts copy
                                                 aignet2)))))
    :rule-classes :linear)

  (defthm aignet-copies-ok-of-aignet-copy-regs-init
    (implies (aignet-copies-ok (num-nodes aignet) copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-regs-init aignet initsts copy aignet2)
               (aignet-copies-ok
                (+ 1 (node-count aignet))
                copy aignet2))))

  (defthm num-regs-of-aignet-copy-regs-init
    (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-regs-init
                                               aignet initsts copy aignet2)))
           (+ (nfix (num-regs aignet))
              (stype-count (reg-stype) aignet2))))

  (defthm lookup-copy-of-aignet-copy-regs-init
    (implies (and (aignet-idp id aignet))
             (b* (((mv aignet-copy-new aignet2-new)
                   (aignet-copy-regs-init aignet initsts copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (not (equal (io-id->regp id aignet) 1)))
                          (get-lit id copy)
                        (mk-lit
                         (regnum->id (+ (nfix (io-id->ionum id aignet))
                                        (num-regs aignet2))
                                     aignet2-new)
                         (get-bit (io-id->ionum id aignet) initsts)))))))

  (defthm aignet-copy-comb-reg-vals-of-aignet-copy-regs-init-nth
    (b* (((mv copy1 aignet21)
          (aignet-copy-regs-init aignet initsts copy aignet2)))
      (implies (equal (num-regs aignet2) 0)
               (bit-equiv (nth n (aignet-copy-comb-reg-vals
                                  invals regvals aignet21 copy1 aignet))
                          (and (< (nfix n) (num-regs aignet))
                               (b-xor (get-bit n initsts)
                                      (nth n regvals))))))
    :hints(("Goal" :in-theory (enable lit-eval id-eval))))

  ;; BOZO move somewhere else
  (defun b-xor-lst (a b)
    (cond ((atom a) b)
          ((atom b) a)
          (t (cons (b-xor (car a) (car b))
                   (b-xor-lst (cdr a) (cdr b))))))

  (defthm nth-of-b-xor-lst
    (bit-equiv (nth n (b-xor-lst a b))
               (b-xor (nth n a) (nth n b)))
    :hints(("Goal" :in-theory (e/d (nth) (bit-equiv)))
           (and stable-under-simplificationp
                '(:in-theory (enable b-xor)))))

  (defthm len-of-b-xor-lst
    (equal (len (b-xor-lst a b))
           (max (len a) (len b))))

  ;; (defthm len-of-b-xor-lst-1
  ;;   (<= (len a) (len (b-xor-lst a b)))
  ;;   :rule-classes :linear)
  ;; (defthm len-of-b-xor-lst-2
  ;;   (<= (len b) (len (b-xor-lst a b)))
  ;;   :rule-classes :linear)

  (defthm aignet-copy-comb-reg-vals-of-aignet-copy-regs-init
    (b* (((mv copy1 aignet21)
          (aignet-copy-regs-init aignet initsts copy aignet2)))
      (implies (equal (num-regs aignet2) 0)
               (bits-equiv (aignet-copy-comb-reg-vals
                            invals regvals aignet21 copy1 aignet)
                           (take (num-regs aignet)
                                 (b-xor-lst initsts regvals)))))
    :hints (("goal" :in-theory (disable aignet-copy-comb-reg-vals
                                        aignet-copy-regs-init))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-copy-comb-in-vals-of-aignet-copy-regs-init-nth
    (b* (((mv copy1 aignet21)
          (aignet-copy-regs-init aignet initsts copy aignet2)))
      (implies (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
               (bit-equiv (nth n (aignet-copy-comb-in-vals
                                  invals regvals aignet21 copy1 aignet))
                          (nth n (aignet-copy-comb-in-vals
                                  invals regvals aignet2 copy aignet)))))
    :hints(("Goal" :expand ((:free (n copy aignet)
                             (lit-eval (nth-lit n copy)
                                       invals regvals aignet))
                            (:free (n copy aignet)
                             (id-eval (lit-id (nth-lit n copy))
                                      invals regvals aignet)))
            :in-theory (enable nth-of-aignet-copy-comb-in-vals-split))))

  (defthm aignet-copy-comb-in-vals-of-aignet-copy-regs-init
    (b* (((mv copy1 aignet21)
          (aignet-copy-regs-init aignet initsts copy aignet2)))
      (implies (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
               (bits-equiv (aignet-copy-comb-in-vals
                            invals regvals aignet21 copy1 aignet)
                           (aignet-copy-comb-in-vals
                            invals regvals aignet2 copy aignet))))
    :hints (("goal" :in-theory (disable aignet-copy-comb-in-vals
                                        aignet-copy-regs-init))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(defsection aignet-copy-nxsts-init


  ;; Adds a aignet2 regin for every register of aignet.
  ;; assumes the copy of each regin ID is set to the fanin lit,
  ;; does not change this to the new node.
  ;; Connects the regin to the corresponding reg in aignet2.  Therefore, we must
  ;; assume there are at least as many regs in aignet2 as in aignet.
  (defiteration aignet-copy-nxsts-init (aignet initsts copy aignet2)
    (declare (xargs :stobjs (aignet initsts copy aignet2)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (<= (num-regs aignet) (num-regs aignet2))
                                (<= (num-regs aignet) (bits-length initsts))
                                (aignet-copies-ok (num-nodes aignet)
                                                  copy aignet2))))
    (b* ((nxst (reg-id->nxst (regnum->id n aignet) aignet))
         (inv (get-bit n initsts))
         (fanin-copy (lit-negate-cond (get-lit nxst copy) inv))
         (ro-copy (regnum->id n aignet2)))
      (aignet-set-nxst fanin-copy ro-copy aignet2))
    :returns aignet2
    :last (num-regs aignet)
    :index n
    :package aignet::bla)

  (in-theory (disable aignet-copy-nxsts-init))
  (local (in-theory (enable (:induction aignet-copy-nxsts-init-iter)
                            aignet-copy-nxsts-init)))

  (def-aignet-preservation-thms aignet-copy-nxsts-init-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-nxsts-init-iter n aignet initsts copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-nxsts-init-iter n aignet initsts copy aignet2))
              (:free (copy) (aignet-copy-nxsts-init-iter n aignet initsts copy aignet2))
              (:free (aignet2) (aignet-copy-nxsts-init-iter n aignet initsts copy
                                                     aignet2))))
            '(:do-not-induct t))))

  (defthm stype-counts-preserved-of-aignet-copy-nxsts-init-iter
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype
                                 (aignet-copy-nxsts-init-iter n aignet initsts copy aignet2))
                    (stype-count stype aignet2))))

  (local (in-theory (enable aignet-extension-implies-node-count-gte
                            lookup-stype-in-bounds)))

  (defthm lookup-nxst-of-aignet-copy-nxsts-init-iter
    (implies (and (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
                  (<= (nfix n) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2-orig))
                  (< (nfix m) (nfix n))
                  (aignet-extension-p aignet2 aignet2-orig))
             (b* ((aignet21 (aignet-copy-nxsts-init-iter n aignet initsts copy aignet2))
                  (regid (node-count (lookup-stype m (reg-stype) aignet2-orig)))
                  (mth-nxst-look2 (lookup-reg->nxst regid aignet21))
                  (mth-nxst-look (lookup-reg->nxst
                                  (node-count (lookup-stype m (reg-stype) aignet))
                                  aignet))
                  (fanin (nth-lit (node-count mth-nxst-look)
                                  copy)))
               (and (consp mth-nxst-look2)
                    (equal (car mth-nxst-look2)
                           (nxst-node
                            (lit-negate-cond fanin (get-bit m initsts))
                            regid))
                    (aignet-litp fanin (cdr mth-nxst-look2))
                    (aignet-idp regid (cdr mth-nxst-look2)))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (n stype a b)
                             (lookup-stype n stype (cons a b)))
                            (:free (n a b)
                             (lookup-reg->nxst n (cons a b))))))))

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-nxsts-init :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-nxsts-init
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype
                                 (aignet-copy-nxsts-init aignet initsts copy aignet2))
                    (stype-count stype aignet2))))

  (defthm lookup-nxst-of-aignet-copy-nxsts-init
    (implies (and (aignet-copies-ok (+ 1 (node-count aignet)) copy aignet2)
                  (< (nfix m) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2-orig))
                  (aignet-extension-p aignet2 aignet2-orig))
             (b* ((aignet21 (aignet-copy-nxsts-init aignet initsts copy aignet2))
                  (regid (node-count (lookup-stype m (reg-stype) aignet2-orig)))
                  (mth-nxst-look2 (lookup-reg->nxst regid aignet21))
                  (mth-nxst-look (lookup-reg->nxst
                                  (node-count (lookup-stype m (reg-stype) aignet))
                                  aignet))
                  (fanin (nth-lit (node-count mth-nxst-look)
                                  copy)))
               (and (consp mth-nxst-look2)
                    (equal (car mth-nxst-look2)
                           (nxst-node
                            (lit-negate-cond fanin (get-bit m initsts))
                            regid))
                    (aignet-litp fanin (cdr mth-nxst-look2))
                    (aignet-idp regid (cdr mth-nxst-look2)))))))

(defsection aignet-copy-init
  :parents (aignet-logic)
  :short "Set the initial state of an FSM to the all-0 convention."

  :long "<p>Some algorithms assume that an FSM's initial state is the one where
all registers are 0.  This normalizes an FSM that does not follow this
convention into one that does.  Given the aignet and an initial state vector,
this produces a new aignet that has registers toggled so that when its initial
value is 0, its sequential simulations produce the same values as the input
aignet when its initial value is the specified vector:</p>

@(def id-eval-seq-of-aignet-copy-init)

<p>This operation is similar to @(see aignet-complete-copy).</p>"

  (local (in-theory (enable lookup-stype-in-bounds)))
  (local (defthm resize-list-0
           (equal (resize-list lst 0 default)
                  nil)
           :hints(("Goal" :in-theory (enable resize-list)))))

  (define aignet-copy-init-aux (aignet initsts copy (gatesimp natp) strash aignet2)
    :guard (<= (num-regs aignet) (bits-length initsts))
    :returns (mv copy strash aignet2)
    :prepwork ((local (defthm strash-lemma
                        (implies (and (true-listp strash)
                                      (equal (len strash) 1))
                                 (equal (update-nth 0 nil strash)
                                        '(nil)))
                        :hints (("goal" :in-theory (enable update-nth))))))
    (b* ((aignet2 (aignet-init
                   (num-outs aignet)
                   (num-regs aignet)
                   (num-ins aignet)
                   (num-nodes aignet)
                   aignet2))
         (copy (resize-lits 0 copy))
         (strash (mbe :logic (non-exec '(nil))
                      :exec (strashtab-init (num-gates aignet) nil nil strash)))
         (copy (resize-lits (num-nodes aignet) copy))
         ((mv copy aignet2)
          (aignet-copy-ins aignet copy aignet2))
         ((mv copy aignet2)
          (aignet-copy-regs-init aignet initsts copy aignet2))
         ((mv copy strash aignet2)
          (aignet-copy-comb aignet copy gatesimp strash aignet2))
         (aignet2 (aignet-copy-outs aignet copy aignet2))
         (aignet2 (aignet-copy-nxsts-init aignet initsts copy aignet2)))
      (mv copy strash aignet2))
    ///

    (defthm normalize-aignet-copy-inits-aux
      (implies (syntaxp (not (and (equal copy ''nil)
                                  (equal strash ''(nil))
                                  (equal aignet2 ''nil))))
               (equal (aignet-copy-init-aux aignet initsts copy gatesimp strash
                                            aignet2)
                      (aignet-copy-init-aux aignet initsts nil gatesimp '(nil) nil))))

    (defthm num-outs-of-aignet-copy-init-aux
      (equal (stype-count :po (mv-nth 2 (aignet-copy-init-aux aignet initsts copy
                                                              gatesimp strash aignet2)))
             (stype-count :po aignet)))

    (defthm num-regs-of-aignet-copy-init-aux
      (equal (stype-count :reg (mv-nth 2 (aignet-copy-init-aux aignet initsts copy
                                                               gatesimp strash aignet2)))
             (stype-count :reg aignet)))

    (local (defthm id-eval-of-co-node
             (implies (equal (id->type id aignet) (out-type))
                      (equal (id-eval id invals regvals aignet)
                             (lit-eval (co-id->fanin id aignet)
                                       invals regvals aignet)))
             :hints(("Goal" :in-theory (enable id-eval)))))

    (local (in-theory (enable co-node->fanin)))

    (defthm id-eval-of-take-num-ins
      (equal (id-eval id (take (stype-count :pi aignet) invals)
                      regvals aignet)
             (id-eval id invals regvals aignet))
      :hints (("goal" :induct (id-eval-ind id aignet)
               :expand ((:free (invals regvals)
                         (id-eval id invals regvals aignet)))
               :in-theory (enable lit-eval eval-and-of-lits))))

    (defthm id-eval-of-take-num-regs
      (equal (id-eval id invals
                      (take (stype-count :reg aignet) regvals)
                      aignet)
             (id-eval id invals regvals aignet))
      :hints (("goal" :induct (id-eval-ind id aignet)
               :expand ((:free (invals regvals)
                         (id-eval id invals regvals aignet)))
               :in-theory (enable lit-eval eval-and-of-lits))))

    (defthm lit-eval-of-take-num-ins
      (equal (lit-eval lit (take (stype-count :pi aignet) invals)
                       regvals aignet)
             (lit-eval lit invals regvals aignet))
      :hints(("Goal"
              :expand ((:free (invals regvals)
                        (lit-eval lit invals regvals aignet))))))

    (defthm lit-eval-of-take-num-regs
      (equal (lit-eval lit invals
                       (take (stype-count :reg aignet) regvals)
                       aignet)
             (lit-eval lit invals regvals aignet))
      :hints(("Goal"
              :expand ((:free (invals regvals)
                        (lit-eval lit invals regvals aignet))))))

    (defthm eval-output-of-aignet-copy-init-aux
      (implies (< (nfix n) (num-outs aignet))
               (b* (((mv & & aignet2) (aignet-copy-init-aux aignet initsts copy gatesimp
                                                                strash aignet2)))
                 (equal (id-eval
                         (node-count (lookup-stype n (po-stype) aignet2))
                         invals regvals aignet2)
                        (id-eval
                         (node-count (lookup-stype n (po-stype) aignet))
                         invals
                         (b-xor-lst initsts regvals) aignet)))))

    (defthm eval-nxst-of-aignet-copy-init-aux
      (implies (< (nfix n) (num-regs aignet))
               (b* (((mv & & aignet2)
                     (aignet-copy-init-aux aignet initsts copy gatesimp strash aignet2)))
                 (equal (id-eval
                         (node-count
                          (lookup-reg->nxst
                           (node-count (lookup-stype n (reg-stype)
                                                     aignet2))
                           aignet2))
                         invals regvals aignet2)
                        (b-xor (get-bit n initsts)
                               (id-eval
                                (reg-id->nxst
                                 (node-count (lookup-stype n (reg-stype)
                                                           aignet))
                                 aignet)
                                invals
                                (b-xor-lst initsts regvals) aignet)))))))

  (define aignet-copy-init (aignet initsts &key
                                       ((gatesimp natp) '9)
                                       (aignet2 'aignet2))
    :parents nil
    :guard (<= (num-regs aignet) (bits-length initsts))
    :returns aignet2
    (b* (((local-stobjs copy strash)
          (mv copy strash aignet2)))
      (aignet-copy-init-aux aignet initsts copy gatesimp strash aignet2))
    ///

    (defthm normalize-aignet-copy-init
      (implies (syntaxp (not (equal aignet2 ''nil)))
               (equal (aignet-copy-init aignet initsts :gatesimp gatesimp
                                        :aignet2 aignet2)
                      (aignet-copy-init aignet initsts
                                        :gatesimp gatesimp
                                        :aignet2 nil))))
    (defthm num-outs-of-aignet-copy-init
      (equal (stype-count :po (aignet-copy-init aignet initsts :gatesimp
                                                gatesimp))
             (stype-count :po aignet)))

    (defthm num-regs-of-aignet-copy-init
      (equal (stype-count :reg (aignet-copy-init aignet initsts :gatesimp
                                                gatesimp))
             (stype-count :reg aignet)))

    (defthm eval-output-of-aignet-copy-init
      (implies (< (nfix n) (num-outs aignet))
               (b* ((aignet2 (aignet-copy-init aignet initsts :gatesimp gatesimp)))
                 (equal (id-eval
                         (node-count (lookup-stype n (po-stype) aignet2))
                         invals regvals aignet2)
                        (id-eval
                         (node-count (lookup-stype n (po-stype) aignet))
                         invals (b-xor-lst initsts regvals) aignet)))))

    (defthm eval-nxst-of-aignet-copy-init
      (implies (< (nfix n) (num-regs aignet))
               (b* ((aignet2 (aignet-copy-init aignet initsts :gatesimp gatesimp)))
                 (equal (id-eval
                         (node-count
                          (lookup-reg->nxst
                           (node-count (lookup-stype n (reg-stype)
                                                     aignet2))
                           aignet2))
                         invals regvals aignet2)
                        (b-xor
                         (get-bit n initsts)
                         (id-eval
                          (reg-id->nxst
                           (node-count (lookup-stype n (reg-stype)
                                                     aignet))
                           aignet)
                          invals
                          (b-xor-lst initsts regvals)
                          aignet)))))))

  (local (defun count-down (k)
           (if (zp k)
               k
             (count-down (1- k)))))

  (local (defmacro generalize-bitsequiv ()
           '(and stable-under-simplificationp
                 (let ((witness (acl2::find-call-lst
                                 'acl2::bits-equiv-witness
                                 clause)))
                   `(:clause-processor
                     (acl2::simple-generalize-cp
                      clause '((,witness . n))))))))



  (defcong bits-equiv bits-equiv (b-xor-lst a b) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))
  (defcong bits-equiv bits-equiv (b-xor-lst a b) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm list-fix-under-nth-equiv
    (nth-equiv (acl2::list-fix x) x)
    :hints(("Goal" :in-theory (enable nth-equiv))))

  (defthm b-xor-lst-twice
    (bits-equiv (b-xor-lst x (b-xor-lst x y))
                y)
    :hints(("Goal" :in-theory (enable bits-equiv))))

  (local (in-theory (disable acl2::take-when-atom)))

  (defthm take-of-b-xor-lst
    (bits-equiv (take n (b-xor-lst a (take n b)))
                (take n (b-xor-lst a b)))
    :hints(("Goal" :in-theory (enable bits-equiv))))

  (defcong bits-equiv bits-equiv (take n x) 2)

  (local (defthm id-eval-b-xor-lst-take-subst
           (equal (id-eval id ins
                           (b-xor-lst x (take (stype-count :reg aignet) y))
                           aignet)
                  (id-eval id ins
                           (b-xor-lst x y) aignet))
           :hints (("goal" :use ((:instance id-eval-of-take-num-regs
                                  (invals ins)
                                  (regvals
                                   (b-xor-lst x (take (stype-count :reg aignet) y)))))))))


  (defthm frame-regvals-of-aignet-copy-init
    (bits-equiv
     (frame-regvals k frames nil (aignet-copy-init
                                  aignet initsts :gatesimp
                                  gatesimp))
     (take (num-regs aignet)
           (b-xor-lst
            initsts
            (frame-regvals k frames initsts aignet))))
    :hints(("Goal" :induct (count-down k))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))
                  :in-theory (enable id-eval-seq-in-terms-of-id-eval
                                     nth-of-frame-regvals-split)
                  :do-not-induct t))
           (and stable-under-simplificationp
                (let ((witness (acl2::find-call-lst
                                'acl2::bits-equiv-witness
                                clause)))
                  `(:clause-processor
                    (acl2::simple-generalize-cp
                     clause '((,witness . n))))))))

  (defthm id-eval-seq-of-aignet-copy-init
    (b* ((aignet2 (aignet-copy-init aignet initsts :gatesimp gatesimp)))
      (equal (id-eval-seq k (node-count (lookup-stype n :po aignet2))
                          frames nil aignet2)
             (id-eval-seq k (node-count (lookup-stype n :po aignet))
                          frames initsts aignet)))
    :hints(("Goal" :in-theory (enable id-eval-seq-in-terms-of-id-eval)
            :cases ((< (nfix n) (num-outs aignet))))))

  (defthm seq-equiv-init-of-aignet-copy-init
    (seq-equiv-init (aignet-copy-init aignet initsts :gatesimp gatesimp)
                    nil
                    aignet initsts)
    :hints(("Goal" :in-theory (e/d (seq-equiv-init) (aignet-copy-init)))))

  (defthm seq-equiv-init-is-seq-equiv-of-aignet-copy-init
    (equal (seq-equiv-init aignet initsts aignet2 initsts2)
           (seq-equiv (aignet-copy-init aignet initsts :aignet2 nil)
                      (aignet-copy-init aignet2 initsts2 :aignet2 nil)))
    :hints (("goal" :cases ((seq-equiv-init aignet initsts aignet2 initsts2))
             :in-theory (enable seq-equiv-necc seq-equiv-init-necc))
            (and stable-under-simplificationp
                 (if (eq (caar clause) 'not)
                     `(:expand (,(car (last clause))))
                   `(:expand (,(car clause)))))
            (and stable-under-simplificationp
                  (let ((witness (acl2::find-call-lst
                                  'seq-equiv-init-witness
                                  clause)))
                    `(:clause-processor
                      (acl2::simple-generalize-cp
                       clause '(((mv-nth '0 ,witness) . k)
                                ((mv-nth '1 ,witness) . n)
                                ((mv-nth '2 ,witness) . inframes))))))
            (and stable-under-simplificationp
                 '(:use ((:instance seq-equiv-necc
                          (aignet (aignet-copy-init-fn aignet initsts 9
                                                       nil))
                          (aignet2 (aignet-copy-init-fn aignet2 initsts2 9 nil))))
                   :in-theory (disable seq-equiv-necc))))
    :otf-flg t))
