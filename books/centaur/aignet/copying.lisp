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
(include-book "mark-impls")
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/take" :dir :system))

;; (local (include-book "data-structures/list-defthms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           ;; acl2::resize-list-when-empty
                           ;; acl2::make-list-ac-redef
                           ;; set::double-containment
                           ;; set::sets-are-true-lists
                           make-list-ac)))

(local (acl2::use-trivial-ancestors-check))

(local (in-theory (disable id-eval
                           true-listp
                           acl2::nfix-when-not-natp
                           acl2::natp-when-integerp
                           acl2::resize-list-when-atom)))
(local (std::add-default-post-define-hook :fix))

(defstobj-clone copy litarr :prefix "COPY")

;; (defsection aignet-copies-ok

;;   ;; Copies:
;;   (defund aignet-copies-ok (n copy aignet)
;;     (declare (type (integer 0 *) n)
;;              (xargs :stobjs (copy aignet)
;;                     :guard (<= n (lits-length copy))
;;                     :guard-debug t))
;;     (if (zp n)
;;         t
;;       (and (fanin-litp (get-lit (1- n) copy) aignet)
;;            (aignet-copies-ok (1- n) copy aignet))))

;;   (local (in-theory (enable aignet-copies-ok)))

;;   (defthm aignet-copies-ok-of-extension
;;     (implies (and (aignet-extension-binding)
;;                   (aignet-extension-p new orig)
;;                   (aignet-copies-ok n copy orig))
;;              (aignet-copies-ok n copy new)))

;;   (defcong nat-equiv equal (aignet-copies-ok n copy aignet) 1)
;;   (defcong nth-equiv equal (nth-lit i x) 2 :hints(("Goal" :in-theory (enable nth-lit))))
;;   (defcong nth-equiv equal (aignet-copies-ok n copy aignet) 2)
;;   (defcong list-equiv equal (aignet-copies-ok n copy aignet) 3)

;;   (defthm aignet-copies-ok-of-update
;;     (implies (and (aignet-copies-ok n copy aignet)
;;                   (aignet-litp v aignet))
;;              (aignet-copies-ok
;;               n
;;               (update-nth-lit m v copy)
;;               aignet))
;;     :hints (("goal" :induct
;;              (aignet-copies-ok n copy aignet))))

;;   (defthm aignet-copies-ok-implies
;;     (implies (and (aignet-copies-ok n copy aignet)
;;                   (< (nfix k) (nfix n)))
;;              (aignet-litp (nth-lit k copy) aignet))
;;     :hints (("goal" :induct (aignet-copies-ok n copy aignet))))

;;   (defthm aignet-copies-ok-implies-special
;;     (implies (and (aignet-copies-ok (+ 1 (node-count aignet1)) copy aignet)
;;                   (aignet-idp k aignet1))
;;              (aignet-litp (nth-lit k copy) aignet))
;;     :hints (("goal" :in-theory (e/d (aignet-idp)
;;                                     (aignet-copies-ok)))))

;;   (local (defthm nth-lit-of-resize-list-split
;;            (equal (nth-lit n (resize-list x sz default))
;;                   (if (< (nfix n) (nfix sz))
;;                       (if (< (nfix n) (len x))
;;                           (nth-lit n x)
;;                         (lit-fix default))
;;                     0))
;;            :hints(("Goal" :in-theory (enable nth-lit resize-list)))))

;;   (defthm aignet-copies-ok-of-resize-list
;;     (implies (aignet-copies-ok n copy aignet)
;;              (aignet-copies-ok n (resize-list copy sz 0) aignet)))

;;   (local (defthm nth-lit-of-nil
;;            (equal (nth-lit n nil) 0)
;;            :hints(("Goal" :in-theory (enable nth-lit)))))

;;   (defthm aignet-copies-ok-of-nil
;;     (aignet-copies-ok n nil aignet)))


(defsection aignet-copies-in-bounds
  (defun-sk aignet-copies-in-bounds (copy aignet)
    (forall n
            (ec-call (aignet-litp (ec-call (nth-lit n copy)) aignet)))
    :rewrite :direct)

  (verify-guards aignet-copies-in-bounds)

  (in-theory (disable aignet-copies-in-bounds))

  (defthm aignet-copies-in-bounds-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-copies-in-bounds copy orig))
             (aignet-copies-in-bounds copy new))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-copies-in-bounds-of-update
    (implies (and (aignet-copies-in-bounds copy aignet)
                  (aignet-litp lit aignet))
             (aignet-copies-in-bounds (update-nth-lit n lit copy) aignet))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (local (defthm nth-lit-of-nil
           (equal (nth-lit n nil) 0)
           :hints(("Goal" :in-theory (enable nth-lit nth)))))

  (defthm aignet-copies-in-bounds-of-init
    (aignet-copies-in-bounds (resize-list nil n 0) aignet)
    :hints (("goal" :expand ((aignet-copies-in-bounds (resize-list nil n 0) aignet)))))

  ;; (defthm aignet-copies-in-bounds-implies-aignet-copies-ok
  ;;   (implies (aignet-copies-in-bounds copy aignet)
  ;;            (aignet-copies-ok n copy aignet))
  ;;   :hints(("Goal" :in-theory (enable aignet-copies-ok))))

  (fty::deffixequiv aignet-copies-in-bounds :args ((aignet aignet))
    :hints(("Goal" :in-theory (disable aignet-copies-in-bounds)
            :cases ((aignet-copies-in-bounds copy aignet)))
           (and stable-under-simplificationp
                (b* ((lit (assoc 'aignet-copies-in-bounds clause))
                     (other (cadr (assoc 'not clause))))
                  `(:expand (,lit)
                    :in-theory (disable aignet-copies-in-bounds-necc)
                    :use ((:instance aignet-copies-in-bounds-necc
                           (copy ,(cadr other))
                           (aignet ,(caddr other))
                           (n (aignet-copies-in-bounds-witness . ,(cdr lit))))))))))
  )


(defsection aignet-copy-comb

  (defmacro lit-copy (lit aignet-copyv)
    `(let ((lit-copy-lit ,lit))
       (lit-negate-cond (get-lit (lit-id lit-copy-lit) ,aignet-copyv)
                        (lit-neg lit-copy-lit))))

  (defiteration aignet-copy-comb (aignet copy gatesimp strash aignet2)
    (declare (xargs :stobjs (aignet copy strash aignet2)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-in-bounds copy aignet2)
                                (gatesimp-p gatesimp))
                    :guard-hints (("goal" :do-not-induct t
                                   :in-theory (enable aignet-idp)))))
    (b* ((n (lnfix n))
         (nid n)
         (slot0 (id->slot nid 0 aignet))
         (type (snode->type slot0)))
      (aignet-case
       type
       :gate (b* ((lit0 (snode->fanin slot0))
                  (slot1 (id->slot nid 1 aignet))
                  (lit1 (snode->fanin slot1))
                  (c0 (lit-copy lit0 copy))
                  (c1 (lit-copy lit1 copy))
                  ((mv lit strash aignet2)
                   (if (eql 1 (snode->regp slot1))
                       (aignet-hash-xor c0 c1 gatesimp strash aignet2)
                     (aignet-hash-and c0 c1 gatesimp strash aignet2)))
                  (copy (set-lit nid lit copy)))
               (mv copy strash aignet2))
       :in ;; assume already set up
       (mv copy strash aignet2)
       :out ;; -- output -- update copy numbers as fanins but don't add nodes
       (b* ((lit0 (snode->fanin slot0))
            (copy (set-lit nid (lit-copy lit0 copy) copy)))
         (mv copy strash aignet2))
       :const (b* ((copy (set-lit nid 0 copy)))
                (mv copy strash aignet2))))
    :returns (mv copy strash aignet2)
    :index n
    :last (num-nodes aignet)
    :package aignet::foo)

  (in-theory (disable aignet-copy-comb))
  (local (in-theory (enable aignet-copy-comb)))

  (def-aignet-preservation-thms aignet-copy-comb-iter :stobjname aignet2)
  (def-aignet-preservation-thms aignet-copy-comb :stobjname aignet2)

  (fty::deffixequiv aignet-copy-comb-iter :args ((gatesimp gatesimp-p)))
  (fty::deffixequiv acl2::aignet-copy-comb$inline :args ((gatesimp gatesimp-p)))

  (defthm stype-counts-preserved-of-aignet-copy-comb-iter
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype (mv-nth 2 (aignet-copy-comb-iter
                                                  n aignet copy gatesimp strash
                                                  aignet2)))
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy gatesimp strash
                                    aignet2))))

  (defthm stype-counts-preserved-of-aignet-copy-comb
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
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
      (implies (and (aignet-copies-in-bounds copy aignet2)
                    (<= (nfix n) (num-nodes aignet)))
               (aignet-copies-in-bounds aignet-copy1 aignet21)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy
                                    gatesimp strash aignet2))))

  (defthm aignet-copies-ok-of-aignet-copy-comb
    (b* (((mv aignet-copy1 & aignet21)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (implies (aignet-copies-in-bounds copy aignet2)
               (aignet-copies-in-bounds aignet-copy1 aignet21)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy
                                    gatesimp strash aignet2))))

  (defthm aignet-copies-ok-of-aignet-copy-comb-litp
    (b* (((mv aignet-copy1 & aignet21)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (implies (and (aignet-copies-in-bounds copy aignet2)
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

  (fty::deffixequiv aignet-copy-comb-iter :args ((aignet aignet)))
  (fty::deffixequiv acl2::aignet-copy-comb$inline :args ((aignet aignet)))

  ;; (local (in-theory (disable aignet-copies-ok)))
  )




(defsection aignet-copy-comb-in-vals
  (def-list-constructor aignet-copy-comb-in-vals
    (invals regvals aignet2 copy aignet)
    (declare (xargs :stobjs (aignet2 copy aignet invals regvals)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-in-bounds
                                          copy aignet2)
                                (<= (num-ins aignet2) (bits-length invals))
                                (<= (num-regs aignet2) (bits-length regvals)))))
    (b* ((in-id (innum->id n aignet))
         (copy-lit (get-lit in-id copy)))
      (lit-eval copy-lit invals regvals aignet2))
    :length (num-ins aignet))

  (local (set-default-hints
          '((and stable-under-simplificationp
                 (acl2::equal-by-nths-hint)))))

  (defthm aignet-copy-in-vals-of-extension
    (implies (and (aignet-extension-binding :new new2
                                            :orig aignet2)
                  (aignet-copies-in-bounds
                                    copy aignet2))
             (equal (aignet-copy-comb-in-vals
                     invals regvals new2 copy aignet)
                    (aignet-copy-comb-in-vals
                     invals regvals aignet2 copy aignet))))

  ;; This holds because aignet-copy-comb doesn't touch the copy pointers of
  ;; CI nodes
  (defthm aignet-copy-in-vals-after-copy-comb-copy
    (b* (((mv aignet-copy2 & &)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (equal (aignet-copy-comb-in-vals
              invals regvals aignet22 aignet-copy2 aignet)
             (aignet-copy-comb-in-vals
              invals regvals aignet22 copy aignet)))))


(defsection aignet-copy-comb-reg-vals
  (def-list-constructor aignet-copy-comb-reg-vals
    (invals regvals aignet2 copy aignet)
    (declare (xargs :stobjs (aignet2 copy aignet invals regvals)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-in-bounds copy aignet2)
                                (<= (num-ins aignet2) (bits-length invals))
                                (<= (num-regs aignet2) (bits-length regvals)))))
    (b* ((reg-id (regnum->id n aignet))
         (copy-lit (get-lit reg-id copy)))
      (lit-eval copy-lit invals regvals aignet2))
    :length (num-regs aignet))


  (local (set-default-hints
          '((and stable-under-simplificationp
                 (acl2::equal-by-nths-hint)))))

  (defthm aignet-copy-reg-vals-of-extension
    (implies (and (aignet-extension-binding :new new2
                                            :orig aignet2)
                  (aignet-copies-in-bounds
                                    copy aignet2))
             (equal (aignet-copy-comb-reg-vals
                         invals regvals new2 copy aignet)
                        (aignet-copy-comb-reg-vals
                         invals regvals aignet2 copy aignet))))

  (defthm aignet-copy-reg-vals-after-copy-comb-copy
    (b* (((mv aignet-copy2 & &)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (equal (aignet-copy-comb-reg-vals
              invals regvals aignet22 aignet-copy2 aignet)
             (aignet-copy-comb-reg-vals
              invals regvals aignet22 copy aignet)))))


(defsection aignet-copy-comb-correct

  (local
   (defun-sk eval-of-aignet-copy-comb-invariant
     (n invals regvals aignet-copy1 aignet21 aignet2 copy aignet)
     (forall m
             (implies (< (nfix m) (nfix n))
                      (equal (lit-eval (nth-lit m aignet-copy1)
                                       invals regvals aignet21)
                             (id-eval m
                                      (aignet-copy-comb-in-vals
                                       invals regvals aignet2 copy aignet)
                                      (aignet-copy-comb-reg-vals
                                       invals regvals aignet2 copy aignet)
                                      aignet))))
     :rewrite :direct))

  (local (in-theory (disable eval-of-aignet-copy-comb-invariant)))

  (local (defthm lit-eval-of-mk-lit
           (equal (lit-eval (mk-lit (lit-id lit) neg) invals regvals aignet)
                  (b-xor (b-xor neg (lit-neg lit))
                         (lit-eval lit invals regvals aignet)))
           :hints(("Goal" :in-theory (enable lit-eval)))))


  (defthm aignet-litp-of-aignet-copy-comb-iter
    (implies (and (aignet-copies-in-bounds copy aignet2)
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
                   (aignet-copies-in-bounds copy aignet2))
              (b* (((mv aignet-copy1 & aignet21)
                    (aignet-copy-comb-iter
                     n aignet copy gatesimp strash aignet2)))
                (eval-of-aignet-copy-comb-invariant
                 n invals regvals aignet-copy1 aignet21 aignet2 copy aignet)))
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
                      :in-theory (enable eval-and-of-lits eval-xor-of-lits))))
             (and stable-under-simplificationp
                  '(:cases ((< (nfix witness) (nfix (+ -1 n))))))
             (and stable-under-simplificationp
                  '(:expand ((:free (invals regvals)
                              (id-eval witness invals
                                       regvals
                                       aignet))
                             (:free (invals regvals)
                              (id-eval (+ -1 n) invals
                                       regvals
                                       aignet))
                             (:free (lit invals regvals)
                              (lit-eval lit invals regvals aignet))))))))

  (defthm eval-of-aignet-copy-comb-iter
    (implies (and (<= (nfix n) (num-nodes aignet))
                  (aignet-copies-in-bounds copy aignet2)
                  (< (nfix m) (nfix n)))
             (b* (((mv aignet-copy1 & aignet21)
                   (aignet-copy-comb-iter
                    n aignet copy gatesimp strash aignet2)))
               (equal (lit-eval (nth-lit m aignet-copy1)
                                invals regvals aignet21)
                      (id-eval m
                               (aignet-copy-comb-in-vals
                                invals regvals aignet2 copy aignet)
                               (aignet-copy-comb-reg-vals
                                invals regvals aignet2 copy aignet)
                               aignet))))
    :hints (("goal" :use ((:instance eval-of-aignet-copy-comb-lemma))
             :in-theory (disable eval-of-aignet-copy-comb-lemma))))

  (defthm eval-of-aignet-copy-comb
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (< (nfix m) (num-nodes aignet)))
             (b* (((mv aignet-copy1 & aignet21)
                   (aignet-copy-comb aignet copy gatesimp strash aignet2)))
               (equal (lit-eval (nth-lit m aignet-copy1)
                                invals regvals aignet21)
                      (id-eval m
                               (aignet-copy-comb-in-vals
                                invals regvals aignet2 copy aignet)
                               (aignet-copy-comb-reg-vals
                                invals regvals aignet2 copy aignet)
                               aignet))))
    :hints(("Goal" :in-theory (enable aignet-copy-comb))))

)


(local (in-theory (disable acl2::nfix-when-not-natp
                           acl2::natp-when-integerp)))

  ;; Utilities for copying IOs


(local (defthm len-of-update-nth-lit-preserved
         (implies (< (nfix n) (len x))
                  (equal (len (update-nth-lit n val x))
                         (len x)))
         :hints(("Goal" :in-theory (enable update-nth-lit)))))

(defsection aignet-copy-ins


  ;; Adds a aignet2 PI for every PI of aignet, and sets the copy
  (defiteration aignet-copy-ins (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (< (max-fanin aignet) (lits-length copy))))
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

  (defthm aignet-copy-size-of-aignet-copy-ins-iter-max-fanin
    (implies (and (< (max-fanin aignet) (lits-length copy))
                  (<= (nfix n) (stype-count :pi aignet)))
             (equal (len (mv-nth 0 (aignet-copy-ins-iter
                                    n aignet copy aignet2)))
                    (len copy)))
    :hints(("Goal" :in-theory (enable lookup-stype-in-bounds))))

  (defthm aignet-copies-ok-of-aignet-copy-ins-iter
    (implies (aignet-copies-in-bounds copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-ins-iter n aignet copy aignet2)
               (aignet-copies-in-bounds copy aignet2))))

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
    (implies (and (<= (nfix n) (num-ins aignet)))
             (b* (((mv aignet-copy-new aignet2-new)
                   (aignet-copy-ins-iter n aignet copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (equal (id->regp id aignet) 1)
                              (<= (nfix n) (io-id->ionum id aignet)))
                          (get-lit id copy)
                        (mk-lit
                         (node-count (lookup-stype (+ (io-id->ionum id aignet)
                                                      (num-ins aignet2))
                                                   (pi-stype) aignet2-new))
                         0)))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable satlink::equal-of-make-lit
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

  (defthm aignet-copy-size-of-aignet-copy-ins-max-fanin
    (implies (< (max-fanin aignet) (lits-length copy))
             (equal (len (mv-nth 0 (aignet-copy-ins aignet copy aignet2)))
                    (len copy))))

  (defthm aignet-copies-ok-of-aignet-copy-ins
    (implies (aignet-copies-in-bounds copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-ins aignet copy aignet2)
               (aignet-copies-in-bounds copy aignet2))))

  (defthm num-ins-of-aignet-copy-ins
    (equal (stype-count (pi-stype) (mv-nth 1 (aignet-copy-ins
                                              aignet copy aignet2)))
           (+ (nfix (stype-count (pi-stype) aignet))
              (stype-count (pi-stype) aignet2))))


  (defthm lookup-copy-of-aignet-copy-ins
    (b* (((mv aignet-copy-new aignet2-new)
          (aignet-copy-ins aignet copy aignet2)))
      (equal (nth-lit id aignet-copy-new)
             (if (or (not (equal (id->type id aignet) (in-type)))
                     (equal (id->regp id aignet) 1))
                 (get-lit id copy)
               (mk-lit
                (node-count (lookup-stype (+ (nfix (io-id->ionum id aignet))
                                             (num-ins aignet2))
                                          (pi-stype) aignet2-new))
                0)))))


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
      (implies (aignet-copies-in-bounds copy aignet2)
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
      (implies (aignet-copies-in-bounds copy aignet2)
               (bits-equiv (aignet-copy-comb-reg-vals
                            invals regvals aignet21 copy1 aignet)
                           (aignet-copy-comb-reg-vals
                            invals regvals aignet2 copy aignet))))
    :hints (("goal" :in-theory (disable aignet-copy-comb-reg-vals
                                        aignet-copy-ins))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (fty::deffixequiv aignet-copy-ins-iter :args ((aignet aignet)))
  (fty::deffixequiv acl2::aignet-copy-ins$inline :args ((aignet aignet))))


(defsection aignet-copy-regs

  ;; Adds a aignet2 reg for every reg of aignet, and sets the copy
  (defiteration aignet-copy-regs (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (and (< (max-fanin aignet) (lits-length copy)))))
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

  (defthm aignet-copy-size-of-aignet-copy-regs-iter-max-fanin
    (implies (and (< (max-fanin aignet) (lits-length copy))
                  (<= (nfix n) (stype-count :reg aignet)))
             (equal (len (mv-nth 0 (aignet-copy-regs-iter
                                    n aignet copy aignet2)))
                    (len copy)))
    :hints(("Goal" :in-theory (enable lookup-stype-in-bounds))))

  (defthm aignet-copies-ok-of-aignet-copy-regs-iter
    (implies (aignet-copies-in-bounds copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-regs-iter n aignet copy aignet2)
               (aignet-copies-in-bounds copy aignet2))))

  (local (defthmd dumb-num-regs-lemma
           (implies (<= n (stype-count (reg-stype) aignet))
                    (< (+ -1 n) (stype-count (reg-stype) aignet)))))

  (defthm num-regs-of-aignet-copy-regs-iter
    (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-regs-iter
                                               n aignet copy aignet2)))
           (+ (nfix n)
              (stype-count (reg-stype) aignet2))))

  (defthm lookup-copy-of-aignet-copy-regs-iter
    (implies (and (<= (nfix n) (num-regs aignet)))
             (b* (((mv aignet-copy-new aignet2-new)
                   (aignet-copy-regs-iter n aignet copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (not (equal (id->regp id aignet) 1))
                              (<= (nfix n) (io-id->ionum id aignet)))
                          (get-lit id copy)
                        (mk-lit
                         (regnum->id (+ (nfix (io-id->ionum id aignet))
                                        (num-regs aignet2))
                                     aignet2-new)
                         0)))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable satlink::equal-of-make-lit
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

  (defthm aignet-copy-size-of-aignet-copy-regs-max-fanin
    (implies (< (max-fanin aignet) (lits-length copy))
             (equal (len (mv-nth 0 (aignet-copy-regs aignet copy aignet2)))
                    (len copy))))

  (defthm aignet-copies-ok-of-aignet-copy-regs
    (implies (aignet-copies-in-bounds copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-regs aignet copy aignet2)
               (aignet-copies-in-bounds copy aignet2))))

  (defthm num-regs-of-aignet-copy-regs
    (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-regs
                                               aignet copy aignet2)))
           (+ (nfix (num-regs aignet))
              (stype-count (reg-stype) aignet2))))

  (defthm lookup-copy-of-aignet-copy-regs
    (b* (((mv aignet-copy-new aignet2-new)
          (aignet-copy-regs aignet copy aignet2)))
      (equal (nth-lit id aignet-copy-new)
             (if (or (not (equal (id->type id aignet) (in-type)))
                     (not (equal (id->regp id aignet) 1)))
                 (get-lit id copy)
               (mk-lit
                (regnum->id (+ (nfix (io-id->ionum id aignet))
                               (num-regs aignet2))
                            aignet2-new)
                0)))))

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
      (implies (aignet-copies-in-bounds copy aignet2)
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
      (implies (aignet-copies-in-bounds copy aignet2)
               (bits-equiv (aignet-copy-comb-in-vals
                            invals regvals aignet21 copy1 aignet)
                           (aignet-copy-comb-in-vals
                            invals regvals aignet2 copy aignet))))
    :hints (("goal" :in-theory (disable aignet-copy-comb-in-vals
                                        aignet-copy-regs))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (fty::deffixequiv aignet-copy-regs-iter :args ((aignet aignet)))
  (fty::deffixequiv acl2::aignet-copy-regs$inline :args ((aignet aignet))))



(defsection aignet-copy-outs

  ;; Adds a aignet2 output for every output of aignet, using the stored copy
  ;; assumes the copy of each output ID is set to the fanin lit,
  ;; does not change this to the new node
  (defiteration aignet-copy-outs (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (and (<= (num-nodes aignet) (lits-length copy))
                                (aignet-copies-in-bounds copy aignet2))))
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

  ;; (defthm lookup-output-of-aignet-copy-outs-iter
  ;;   (implies (and (aignet-copies-in-bounds copy aignet2)
  ;;                 (equal 0 (num-outs aignet2))
  ;;                 (< (nfix m) (nfix n))
  ;;                 (<= (nfix n) (num-outs aignet)))
  ;;            (b* ((aignet21 (aignet-copy-outs-iter n aignet copy aignet2))
  ;;                 (mth-out-look (lookup-stype m (po-stype) aignet21))
  ;;                 (fanin (nth-lit (node-count (lookup-stype m (po-stype) aignet))
  ;;                                 copy)))
  ;;              (and (consp mth-out-look)
  ;;                   (equal (car mth-out-look)
  ;;                          (po-node fanin))
  ;;                   (aignet-litp fanin (cdr mth-out-look)))))
  ;;   :hints ((and stable-under-simplificationp
  ;;                '(:expand ((:free (n stype a b)
  ;;                            (lookup-stype n stype (cons a b))))))
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable lookup-stype-in-bounds)))))

  (defthm lookup-output-of-aignet-copy-outs-iter
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (equal 0 (num-outs aignet2))
                  (< (nfix m) (nfix n))
                  (<= (nfix n) (num-outs aignet)))
             (b* ((aignet21 (aignet-copy-outs-iter n aignet copy aignet2))
                  (mth-out-look (lookup-stype m (po-stype) aignet21))
                  (fanin (nth-lit (node-count (lookup-stype m (po-stype) aignet))
                                  copy)))
               (and ;; (consp mth-out-look)
                    (equal (fanin :co mth-out-look) fanin)
                    ;; (equal (car mth-out-look)
                    ;;        (po-node fanin))
                    ;; (aignet-litp fanin (cdr mth-out-look))
                    )))
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
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (equal 0 (num-outs aignet2))
                  (< (nfix m) (num-outs aignet)))
             (b* ((aignet21 (aignet-copy-outs aignet copy aignet2))
                  (mth-out-look (lookup-stype m (po-stype) aignet21))
                  (fanin (nth-lit (node-count (lookup-stype m (po-stype) aignet))
                                  copy)))
               (and ;; (consp mth-out-look)
                    (equal (fanin :co mth-out-look) fanin)
                    ;; (equal (car mth-out-look)
                    ;;        (po-node fanin))
                    ;; (aignet-litp fanin (cdr mth-out-look))
                    ))))

  (fty::deffixequiv aignet-copy-outs-iter :args ((aignet aignet)))
  (fty::deffixequiv acl2::aignet-copy-outs$inline :args ((aignet aignet))))


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
                                (aignet-copies-in-bounds copy aignet2))))
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
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (<= (nfix n) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2))
                  (< (nfix m) (nfix n))
                  ;; (aignet-extension-p aignet2 aignet2-orig)
                  )
             (b* ((aignet21 (aignet-copy-nxsts-iter n aignet copy aignet2))
                  (mth-nxst-look2 (lookup-regnum->nxst m aignet21))
                  (mth-nxst-look (lookup-regnum->nxst m aignet))
                  (fanin (nth-lit (node-count mth-nxst-look)
                                  copy))
                  ;; (regid (node-count (lookup-stype m (reg-stype) aignet2)))
                  )
               (and ;; (consp mth-nxst-look2)
                (equal (fanin-if-co mth-nxst-look2) fanin)
                (equal (fanin :co mth-nxst-look2) fanin)
                    ;; (equal (car mth-nxst-look2)
                    ;;        (nxst-node fanin regid))
                    ;; (aignet-litp fanin (cdr mth-nxst-look2))
                    ;; (aignet-idp regid (cdr mth-nxst-look2))
                    )))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (n a b) (lookup-regnum->nxst n (Cons a b)))))))
    ;; :hints ((and stable-under-simplificationp
    ;;              '(:expand ((:free (n stype a b)
    ;;                          (lookup-stype n stype (cons a b)))
    ;;                         (:free (n a b)
    ;;                          (lookup-reg->nxst n (cons a b)))))))
    )

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-nxsts :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-nxsts
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype
                                 (aignet-copy-nxsts aignet copy aignet2))
                    (stype-count stype aignet2))))

  (defthm lookup-nxst-of-aignet-copy-nxsts
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (< (nfix m) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2))
                  ;; (aignet-extension-p aignet2 aignet2-orig)
                  )
             (b* ((aignet21 (aignet-copy-nxsts aignet copy aignet2))
                  ;; (regid (node-count (lookup-stype m (reg-stype) aignet2)))
                  (mth-nxst-look2 (lookup-regnum->nxst m aignet21))
                  (mth-nxst-look (lookup-regnum->nxst m aignet))
                  (fanin (nth-lit (node-count mth-nxst-look)
                                  copy)))
               (and ;; (consp mth-nxst-look2)
                    ;; (equal (fanin :co mth-nxst-look2) fanin)
                (equal (fanin-if-co mth-nxst-look2) fanin)
                (equal (fanin :co mth-nxst-look2) fanin)
                    ;; (equal (car mth-nxst-look2)
                    ;;        (nxst-node fanin regid))
                    ;; (aignet-litp fanin (cdr mth-nxst-look2))
                    ;; (aignet-idp regid (cdr mth-nxst-look2))
                    ))))

  (fty::deffixequiv aignet-copy-nxsts-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-copy-nxsts$inline :args ((aignet aignet))))

(defsection aignet-po-copies-in-bounds
  (defun-sk aignet-po-copies-in-bounds (copy aignet aignet2)
    (forall n
            (b* ((look (lookup-stype n :po aignet)))
              (implies (< (nfix n) (num-outs aignet))
                       (aignet-litp (nth-lit (lit-id (fanin :co look)) copy) aignet2))))
    :rewrite :direct)

  (defthm aignet-po-copies-in-bounds-when-aignet-copies-in-bounds
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-po-copies-in-bounds copy aignet aignet2))) 

  (in-theory (disable aignet-po-copies-in-bounds))

  ;; (defthm lookup-po-in-bounds-by-aignet-po-copies-in-bounds
  ;;   (implies (and (aignet-po-copies-in-bounds copy aignet aignet2)
  ;;                 (< (nfix out) (num-outs aignet)))
  ;;            (aignet-litp (nth-lit (lit-id (fanin :co (lookup-stype out :po aignet))) copy)
  ;;                         aignet2))
  ;;   :hints (("goal" :use ((:instance aignet-po-copies-in-bounds-necc
  ;;                          (n (node-count (lookup-stype out :po aignet)))))
  ;;            :in-theory (e/d (stype-of-lookup-stype-split)
  ;;                            (aignet-po-copies-in-bounds-necc)))))

  (defthm aignet-po-copies-in-bounds-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-po-copies-in-bounds copy aignet orig))
             (aignet-po-copies-in-bounds copy aignet new))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (fty::deffixequiv aignet-po-copies-in-bounds :args ((aignet aignet) (aignet2 aignet))
    :hints(("Goal" :in-theory (disable aignet-po-copies-in-bounds)
            :cases ((aignet-po-copies-in-bounds copy aignet aignet2)))
           (and stable-under-simplificationp
                (b* ((lit (assoc 'aignet-po-copies-in-bounds clause))
                     (other (cadr (assoc 'not clause))))
                  `(:expand (,lit)
                    :in-theory (disable aignet-po-copies-in-bounds-necc)
                    :use ((:instance aignet-po-copies-in-bounds-necc
                           (copy ,(cadr other))
                           (aignet ,(caddr other))
                           (aignet2 ,(cadddr other))
                           (n (aignet-po-copies-in-bounds-witness . ,(cdr lit)))))))))))

(defsection aignet-copy-outs-from-fanins
  (local (in-theory (enable lookup-stype-in-bounds)))

  ;; Adds a aignet2 output for every output of aignet.
  (defiteration aignet-copy-outs-from-fanins (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (and (< (max-fanin aignet) (lits-length copy))
                                (ec-call (aignet-po-copies-in-bounds copy aignet aignet2)))))
    (b* ((outid (outnum->id n aignet))
         (fanin-lit (co-id->fanin outid aignet))
         (fanin (lit-copy fanin-lit copy)))
      (aignet-add-out fanin aignet2))
    :returns aignet2
    :last (num-outs aignet)
    :index n
    :package aignet::bla)

  (in-theory (disable aignet-copy-outs-from-fanins))
  (local (in-theory (enable (:induction aignet-copy-outs-from-fanins-iter)
                            aignet-copy-outs-from-fanins)))

  (def-aignet-preservation-thms aignet-copy-outs-from-fanins-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-outs-from-fanins-iter n aignet copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-outs-from-fanins-iter n aignet copy aignet2))
              (:free (copy) (aignet-copy-outs-from-fanins-iter n aignet copy aignet2))
              (:free (aignet2) (aignet-copy-outs-from-fanins-iter n aignet copy
                                                     aignet2))))
            '(:do-not-induct t))))

  (defthm stype-counts-preserved-of-aignet-copy-outs-from-fanins-iter
    (implies (not (equal (stype-fix stype) (po-stype)))
             (equal (stype-count stype
                                 (aignet-copy-outs-from-fanins-iter n aignet copy aignet2))
                    (stype-count stype aignet2))))

  (defthm num-outs-of-aignet-copy-outs-from-fanins-iter
    (equal (stype-count (po-stype)
                        (aignet-copy-outs-from-fanins-iter n aignet copy aignet2))
           (+ (nfix n)
              (stype-count (po-stype) aignet2))))

  (encapsulate nil
    (local (set-default-hints nil))
    (defthm aignet-copy-outs-from-fanins-iter-of-nfix
      (equal (aignet-copy-outs-from-fanins-iter (nfix n) aignet copy aignet2)
             (aignet-copy-outs-from-fanins-iter n aignet copy aignet2))
      :hints(("Goal" :in-theory (enable aignet-copy-outs-from-fanins-iter))))

    (defcong nat-equiv equal (aignet-copy-outs-from-fanins-iter n aignet copy aignet2) 1
      :hints (("goal" :use ((:instance aignet-copy-outs-from-fanins-iter-of-nfix)
                            (:instance aignet-copy-outs-from-fanins-iter-of-nfix
                             (n acl2::n-equiv)))
               :in-theory (disable aignet-copy-outs-from-fanins-iter-of-nfix)))))

  (defthm lookup-output-of-aignet-copy-outs-from-fanins-iter
    (implies (and (aignet-po-copies-in-bounds copy aignet aignet2)
                  (equal 0 (num-outs aignet2))
                  (< (nfix m) (nfix n))
                  (<= (nfix n) (num-outs aignet)))
             (b* ((aignet21 (aignet-copy-outs-from-fanins-iter n aignet copy aignet2))
                  (mth-out-look (lookup-stype m (po-stype) aignet21))
                  (mth-out-look-orig (lookup-stype m (po-stype) aignet))
                  (fanin-lit (fanin :co mth-out-look-orig))
                  (fanin-copy (nth-lit (lit-id fanin-lit) copy))
                  (fanin (lit-negate-cond fanin-copy
                                          (lit-neg fanin-lit))))
               (and ;; (equal (car mth-out-look)
                    ;;        (cons (po-node fanin)
                    ;;              (node-list-fix (aignet-copy-outs-from-fanins-iter m aignet copy aignet2))))
                (equal (fanin :co mth-out-look) fanin)
                ;; (aignet-litp fanin-copy (aignet-copy-outs-from-fanins-iter m aignet copy aignet2))
                )))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (n stype a b)
                             (lookup-stype n stype (cons a b))))))
            (and stable-under-simplificationp
                 '(:in-theory (enable lookup-stype-in-bounds)))))



  ;; (defthm lookup-output-of-aignet-copy-outs-from-fanins-iter
  ;;   (implies (and (aignet-copies-in-bounds copy aignet2)
  ;;                 (equal 0 (num-outs aignet2))
  ;;                 (< (nfix m) (nfix n))
  ;;                 (<= (nfix n) (num-outs aignet)))
  ;;            (b* ((aignet21 (aignet-copy-outs-from-fanins-iter n aignet copy aignet2))
  ;;                 (mth-out-look (lookup-stype m (po-stype) aignet21))
  ;;                 (mth-out-look-orig (lookup-stype m (po-stype) aignet))
  ;;                 (fanin-lit (aignet-lit-fix (co-node->fanin (car mth-out-look-orig))
  ;;                                            (cdr mth-out-look-orig)))
  ;;                 (fanin-copy (nth-lit (lit-id fanin-lit) copy))
  ;;                 (fanin (lit-negate-cond fanin-copy
  ;;                                         (lit-neg fanin-lit))))
  ;;              (and (consp mth-out-look)
  ;;                   (equal (car mth-out-look)
  ;;                          (po-node fanin))
  ;;                   (aignet-litp fanin-copy (cdr mth-out-look)))))
  ;;   :hints ((and stable-under-simplificationp
  ;;                '(:expand ((:free (n stype a b)
  ;;                            (lookup-stype n stype (cons a b))))))
  ;;           (and stable-under-simplificationp
  ;;                '(:in-theory (enable lookup-stype-in-bounds)))))

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-outs-from-fanins :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-outs-from-fanins
    (implies (not (equal (stype-fix stype) (po-stype)))
             (equal (stype-count stype
                                 (aignet-copy-outs-from-fanins aignet copy aignet2))
                    (stype-count stype aignet2))))

  (defthm num-outs-of-aignet-copy-outs-from-fanins
    (equal (stype-count (po-stype)
                        (aignet-copy-outs-from-fanins aignet copy aignet2))
           (+ (stype-count (po-stype) aignet)
              (stype-count (po-stype) aignet2))))

  (defthm lookup-output-of-aignet-copy-outs-from-fanins
    (implies (and (aignet-po-copies-in-bounds copy aignet aignet2)
                  (equal 0 (num-outs aignet2))
                  (< (nfix m) (num-outs aignet)))
             (b* ((aignet21 (aignet-copy-outs-from-fanins aignet copy aignet2))
                  (mth-out-look (lookup-stype m (po-stype) aignet21))
                  (mth-out-look-orig (lookup-stype m (po-stype) aignet))
                  (fanin-lit (fanin :co mth-out-look-orig))
                  (fanin-copy (nth-lit (lit-id fanin-lit) copy))
                  (fanin (lit-negate-cond fanin-copy (lit-neg fanin-lit))))
               (equal (fanin :co mth-out-look)
                      fanin)
               ;; (and (equal mth-out-look
               ;;             (cons (po-node fanin)
               ;;                   (node-list-fix (aignet-copy-outs-from-fanins-iter m aignet copy aignet2))))
               ;;      (aignet-litp fanin-copy (aignet-copy-outs-from-fanins-iter m aignet copy aignet2)))
               )))

  (fty::deffixequiv aignet-copy-outs-from-fanins-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-copy-outs-from-fanins$inline :args ((aignet aignet))))

(defsection aignet-nxst-copies-in-bounds
  (defun-sk aignet-nxst-copies-in-bounds (copy aignet aignet2)
    (forall n
            (b* ((look (lookup-regnum->nxst n aignet)))
              (implies (< (nfix n) (num-regs aignet))
                       (aignet-litp (nth-lit (lit-id (fanin-if-co look)) copy) aignet2))))
    :rewrite :direct)

  (defthm aignet-nxst-copies-in-bounds-when-aignet-copies-in-bounds
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-nxst-copies-in-bounds copy aignet aignet2))) 

  (in-theory (disable aignet-nxst-copies-in-bounds))

  ;; (defthm lookup-nxst-in-bounds-by-aignet-nxst-copies-in-bounds
  ;;   (implies (and (aignet-nxst-copies-in-bounds copy aignet aignet2)
  ;;                 (< (nfix out) (num-outs aignet)))
  ;;            (aignet-litp (nth-lit (lit-id (fanin :co (lookup-stype out :nxst aignet))) copy)
  ;;                         aignet2))
  ;;   :hints (("goal" :use ((:instance aignet-nxst-copies-in-bounds-necc
  ;;                          (n (node-count (lookup-stype out :nxst aignet)))))
  ;;            :in-theory (e/d (stype-of-lookup-stype-split)
  ;;                            (aignet-nxst-copies-in-bounds-necc)))))

  (defthm aignet-nxst-copies-in-bounds-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-nxst-copies-in-bounds copy aignet orig))
             (aignet-nxst-copies-in-bounds copy aignet new))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (fty::deffixequiv aignet-nxst-copies-in-bounds :args ((aignet aignet) (aignet2 aignet))
    :hints(("Goal" :in-theory (disable aignet-nxst-copies-in-bounds)
            :cases ((aignet-nxst-copies-in-bounds copy aignet aignet2)))
           (and stable-under-simplificationp
                (b* ((lit (assoc 'aignet-nxst-copies-in-bounds clause))
                     (other (cadr (assoc 'not clause))))
                  `(:expand (,lit)
                    :in-theory (disable aignet-nxst-copies-in-bounds-necc)
                    :use ((:instance aignet-nxst-copies-in-bounds-necc
                           (copy ,(cadr other))
                           (aignet ,(caddr other))
                           (aignet2 ,(cadddr other))
                           (n (aignet-nxst-copies-in-bounds-witness . ,(cdr lit)))))))))))


(defsection aignet-copy-nxsts-from-fanins
  (local (in-theory (enable lookup-stype-in-bounds
                            reg-id->nxst-lit)))


  ;; Adds a aignet2 regin for every register of aignet.
  ;; assumes the copy of each regin ID is set to the fanin lit,
  ;; does not change this to the new node.
  ;; Connects the regin to the corresponding reg in aignet2.  Therefore, we must
  ;; assume there are at least as many regs in aignet2 as in aignet.
  (defiteration aignet-copy-nxsts-from-fanins (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (and (< (max-fanin aignet) (lits-length copy))
                                (<= (num-regs aignet) (num-regs aignet2))
                                (ec-call (aignet-nxst-copies-in-bounds copy aignet aignet2)))))
    (b* ((reg-id (regnum->id n aignet))
         (fanin (reg-id->nxst-lit reg-id aignet))
         (fanin-copy (lit-copy fanin copy))
         (ro-copy (regnum->id n aignet2)))
      (aignet-set-nxst fanin-copy ro-copy aignet2))
    :returns aignet2
    :last (num-regs aignet)
    :index n
    :package aignet::bla)

  (in-theory (disable aignet-copy-nxsts-from-fanins))
  (local (in-theory (enable (:induction aignet-copy-nxsts-from-fanins-iter)
                            aignet-copy-nxsts-from-fanins)))

  (def-aignet-preservation-thms aignet-copy-nxsts-from-fanins-iter :stobjname aignet2)

  (local (set-default-hints
          '((acl2::just-induct-and-expand
             (aignet-copy-nxsts-from-fanins-iter n aignet copy aignet2)
             :expand-others
             ((:free (aignet) (aignet-copy-nxsts-from-fanins-iter n aignet copy aignet2))
              (:free (copy) (aignet-copy-nxsts-from-fanins-iter n aignet copy aignet2))
              (:free (aignet2) (aignet-copy-nxsts-from-fanins-iter n aignet copy
                                                                   aignet2))))
            '(:do-not-induct t))))

  (defthm stype-counts-preserved-of-aignet-copy-nxsts-from-fanins-iter
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype
                                 (aignet-copy-nxsts-from-fanins-iter n aignet copy aignet2))
                    (stype-count stype aignet2))))

  (local (in-theory (enable aignet-extension-implies-node-count-gte
                            lookup-stype-in-bounds)))

  (encapsulate nil
    (local (set-default-hints nil))
    (defthm aignet-copy-nxsts-from-fanins-iter-of-nfix
      (equal (aignet-copy-nxsts-from-fanins-iter (nfix n) aignet copy aignet2)
             (aignet-copy-nxsts-from-fanins-iter n aignet copy aignet2))
      :hints(("Goal" :in-theory (enable aignet-copy-nxsts-from-fanins-iter))))

    (defcong nat-equiv equal (aignet-copy-nxsts-from-fanins-iter n aignet copy aignet2) 1
      :hints (("goal" :use ((:instance aignet-copy-nxsts-from-fanins-iter-of-nfix)
                            (:instance aignet-copy-nxsts-from-fanins-iter-of-nfix
                             (n acl2::n-equiv)))
               :in-theory (disable aignet-copy-nxsts-from-fanins-iter-of-nfix)))))

  (local (in-theory (enable reg-id->nxst-lit)))

  (defthm lookup-nxst-of-aignet-copy-nxsts-from-fanins-iter
    (implies (and (aignet-nxst-copies-in-bounds copy aignet aignet2)
                  (<= (nfix n) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2))
                  (< (nfix m) (nfix n)))
             (b* ((aignet21 (aignet-copy-nxsts-from-fanins-iter n aignet copy aignet2))
                  ;; (regid (node-count (lookup-stype m (reg-stype) aignet2)))
                  (mth-nxst-look2 (lookup-regnum->nxst m aignet21))
                  (mth-nxst-look (lookup-regnum->nxst m aignet))
                  ;; (reg-id->nxst-lit (node-count (lookup-stype m (reg-stype) aignet)) aignet)
                  ;;                ;; (lookup-reg->nxst
                  ;;                ;;  (node-count (lookup-stype m (reg-stype) aignet))
                  ;;                ;;  aignet)
                  ;;                )
                  
                  (fanin1 (fanin-if-co mth-nxst-look))
                  (fanin-copy (nth-lit (lit-id fanin1) copy))
                  (fanin (lit-negate-cond fanin-copy (lit-neg fanin1))))
               ;; (and (consp mth-nxst-look2)
               ;;      (equal (car mth-nxst-look2)
               ;;             (nxst-node fanin regid))
               ;;      (aignet-litp fanin-copy (cdr mth-nxst-look2))
               ;;      (aignet-idp regid (cdr mth-nxst-look2)))
               (and ;; (equal mth-nxst-look2
                    ;;        (cons (nxst-node fanin regid)
                    ;;              (node-list-fix (aignet-copy-nxsts-from-fanins-iter m aignet copy aignet2))))
                    ;; (aignet-litp fanin-copy (aignet-copy-nxsts-from-fanins-iter m aignet copy aignet2))
                    ;; (aignet-idp regid (aignet-copy-nxsts-from-fanins-iter m aignet copy aignet2))
                (equal (fanin :co mth-nxst-look2)
                       fanin)
                (equal (fanin-if-co mth-nxst-look2)
                       fanin)
                    )))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (n a b)
                             (lookup-regnum->nxst n (cons a b)))
                            ;; (aignet-copy-nxsts-from-fanins-iter m aignet copy aignet2)
                            )))))

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-nxsts-from-fanins :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-nxsts-from-fanins
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype
                                 (aignet-copy-nxsts-from-fanins aignet copy aignet2))
                    (stype-count stype aignet2))))

  (defthm lookup-nxst-of-aignet-copy-nxsts-from-fanins
    (implies (and (aignet-nxst-copies-in-bounds copy aignet aignet2)
                  (< (nfix m) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (b* ((aignet21 (aignet-copy-nxsts-from-fanins aignet copy aignet2))
                  ; (regid (node-count (lookup-stype m (reg-stype) aignet2)))
                  (mth-nxst-look2 (lookup-regnum->nxst m aignet21))
                  (mth-nxst-look (lookup-regnum->nxst m aignet))
                  (fanin1 (fanin-if-co mth-nxst-look))
                  (fanin-copy (nth-lit (lit-id fanin1) copy))
                  (fanin (lit-negate-cond fanin-copy
                                          (lit-neg fanin1))))
               (and (equal (fanin :co mth-nxst-look2)
                       fanin)
                (equal (fanin-if-co mth-nxst-look2)
                       fanin))
               ;; (and (equal mth-nxst-look2
               ;;             (cons (nxst-node fanin regid)
               ;;                   (node-list-fix
               ;;                    (aignet-copy-nxsts-from-fanins-iter m aignet copy aignet2))))
               ;;      ;; (consp mth-nxst-look2)
               ;;      ;; (equal (car mth-nxst-look2)
               ;;      ;;        (nxst-node fanin regid))
               ;;      (aignet-litp fanin-copy (aignet-copy-nxsts-from-fanins-iter m aignet copy aignet2))
               ;;      (aignet-idp regid (aignet-copy-nxsts-from-fanins-iter m aignet copy aignet2)))
               )))

  (fty::deffixequiv aignet-copy-nxsts-from-fanins-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-copy-nxsts-from-fanins$inline :args ((aignet aignet))))





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

  (local (in-theory (e/d (lookup-stype-in-bounds)
                         (acl2::resize-list-when-atom))))

  (local (defthm resize-list-0
           (equal (resize-list lst 0 default)
                  nil)
           :hints(("Goal" :in-theory (enable resize-list)))))

  (define aignet-complete-copy-aux (aignet copy (gatesimp gatesimp-p) strash aignet2)
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
               :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))))

    (defthm id-eval-of-take-num-regs
      (equal (id-eval id invals
                      (take (stype-count :reg aignet) regvals)
                      aignet)
             (id-eval id invals regvals aignet))
      :hints (("goal" :induct (id-eval-ind id aignet)
               :expand ((:free (invals regvals)
                         (id-eval id invals regvals aignet)))
               :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))))

    (defthm lit-eval-of-take-num-ins
      (equal (lit-eval lit (take (stype-count :pi aignet) invals)
                       regvals aignet)
             (lit-eval lit invals regvals aignet))
      :hints(("Goal"
              :expand ((:free (invals regvals)
                        (lit-eval lit invals regvals aignet))))))

    ;; (defthm lit-eval-of-take-num-regs
    ;;   (equal (lit-eval lit invals
    ;;                    (take (stype-count :reg aignet) regvals)
    ;;                    aignet)
    ;;          (lit-eval lit invals regvals aignet))
    ;;   :hints(("Goal"
    ;;           :expand ((:free (invals regvals)
    ;;                     (lit-eval lit invals regvals aignet))))))

    (defthm eval-output-of-aignet-complete-copy-aux
      (b* (((mv & & aignet2) (aignet-complete-copy-aux aignet copy gatesimp
                                                       strash aignet2)))
        (equal (lit-eval (fanin :co (lookup-stype n (po-stype) aignet2))
                         invals regvals aignet2)
               (lit-eval (fanin :co (lookup-stype n (po-stype) aignet))
                         invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-outs aignet)))
               :in-theory (enable node-count-lookup-stype-when-out-of-bounds))))

    (defthm eval-nxst-of-aignet-complete-copy-aux
      (b* (((mv & & aignet2)
            (aignet-complete-copy-aux aignet copy gatesimp strash aignet2)))
        (equal (lit-eval (fanin-if-co (lookup-regnum->nxst n aignet2))
                         invals regvals aignet2)
               (lit-eval (fanin-if-co (lookup-regnum->nxst n aignet))
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
      :hints(("Goal" :in-theory (e/d (comb-equiv
                                      outs-comb-equiv
                                      nxsts-comb-equiv
                                      nxst-eval output-eval)
                                     (aignet-complete-copy-aux)))
             (and stable-under-simplificationp
                  '(:in-theory (enable fanin-if-co))))))

  (define aignet-complete-copy (aignet &key
                                       ((gatesimp gatesimp-p) '(default-gatesimp))
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
        (equal (lit-eval (fanin :co (lookup-stype n (po-stype) aignet2))
                         invals regvals aignet2)
               (lit-eval (fanin :co (lookup-stype n (po-stype) aignet))
                         invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-outs aignet)))
               :in-theory (enable node-count-lookup-stype-when-out-of-bounds))))

    (defthm eval-nxst-of-aignet-complete-copy
      (b* ((aignet2 (aignet-complete-copy aignet :gatesimp gatesimp)))
        (equal (lit-eval (fanin-if-co (lookup-regnum->nxst n aignet2))
                         invals regvals aignet2)
               (lit-eval (fanin-if-co (lookup-regnum->nxst n aignet))
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
    (implies (aignet-copies-in-bounds copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-regs-init-iter n aignet initsts copy aignet2)
               (aignet-copies-in-bounds copy aignet2))))

  (local (defthmd dumb-num-regs-lemma
           (implies (<= n (stype-count (reg-stype) aignet))
                    (< (+ -1 n) (stype-count (reg-stype) aignet)))))

  (defthm num-regs-of-aignet-copy-regs-init-iter
    (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-regs-init-iter
                                               n aignet initsts copy aignet2)))
           (+ (nfix n)
              (stype-count (reg-stype) aignet2))))

  (defthm lookup-copy-of-aignet-copy-regs-init-iter
    (implies (and (<= (nfix n) (num-regs aignet)))
             (b* (((mv aignet-copy-new aignet2-new)
                   (aignet-copy-regs-init-iter n aignet initsts copy aignet2)))
               (equal (nth-lit id aignet-copy-new)
                      (if (or (not (equal (id->type id aignet) (in-type)))
                              (not (equal (id->regp id aignet) 1))
                              (<= (nfix n) (io-id->ionum id aignet)))
                          (get-lit id copy)
                        (mk-lit
                         (regnum->id (+ (nfix (io-id->ionum id aignet))
                                        (num-regs aignet2))
                                     aignet2-new)
                         (get-bit (io-id->ionum id aignet) initsts))))))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable satlink::equal-of-make-lit
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
    (implies (aignet-copies-in-bounds copy aignet2)
             (mv-let (copy aignet2)
               (aignet-copy-regs-init aignet initsts copy aignet2)
               (aignet-copies-in-bounds copy aignet2))))

  (defthm num-regs-of-aignet-copy-regs-init
    (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-regs-init
                                               aignet initsts copy aignet2)))
           (+ (nfix (num-regs aignet))
              (stype-count (reg-stype) aignet2))))

  (defthm lookup-copy-of-aignet-copy-regs-init
    (b* (((mv aignet-copy-new aignet2-new)
          (aignet-copy-regs-init aignet initsts copy aignet2)))
      (equal (nth-lit id aignet-copy-new)
             (if (or (not (equal (id->type id aignet) (in-type)))
                     (not (equal (id->regp id aignet) 1)))
                 (get-lit id copy)
               (mk-lit
                (regnum->id (+ (nfix (io-id->ionum id aignet))
                               (num-regs aignet2))
                            aignet2-new)
                (get-bit (io-id->ionum id aignet) initsts))))))

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
      (implies (aignet-copies-in-bounds copy aignet2)
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
      (implies (aignet-copies-in-bounds copy aignet2)
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
                                (aignet-copies-in-bounds copy aignet2))))
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
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (<= (nfix n) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2))
                  (< (nfix m) (nfix n)))
             (b* ((aignet21 (aignet-copy-nxsts-init-iter n aignet initsts copy aignet2))
                  ;; (regid (node-count (lookup-stype m (reg-stype) aignet2-orig)))
                  (mth-nxst-look2 (lookup-regnum->nxst m aignet21))
                  (mth-nxst-look (lookup-regnum->nxst m aignet))
                  (fanin (nth-lit (node-count mth-nxst-look)
                                  copy)))
               (equal (fanin-if-co mth-nxst-look2)
                      (lit-negate-cond fanin (get-bit m initsts)))
               ;; (and (consp mth-nxst-look2)
               ;;      (equal (car mth-nxst-look2)
               ;;             (nxst-node
               ;;              (lit-negate-cond fanin (get-bit m initsts))
               ;;              regid))
               ;;      (aignet-litp fanin (cdr mth-nxst-look2))
               ;;      (aignet-idp regid (cdr mth-nxst-look2)))
               ))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (n a b)
                             (lookup-regnum->nxst n (cons a b))))))))

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-nxsts-init :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-nxsts-init
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype
                                 (aignet-copy-nxsts-init aignet initsts copy aignet2))
                    (stype-count stype aignet2))))

  (defthm lookup-nxst-of-aignet-copy-nxsts-init
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (< (nfix m) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (b* ((aignet21 (aignet-copy-nxsts-init aignet initsts copy aignet2))
                  ;; (regid (node-count (lookup-stype m (reg-stype) aignet2-orig)))
                  (mth-nxst-look2 (lookup-regnum->nxst m aignet21))
                  (mth-nxst-look (lookup-regnum->nxst m aignet))
                  (fanin (nth-lit (node-count mth-nxst-look)
                                  copy)))
               (equal (fanin-if-co mth-nxst-look2)
                      (lit-negate-cond fanin (Get-bit m initsts)))
               ;; (and (consp mth-nxst-look2)
               ;;      (equal (car mth-nxst-look2)
               ;;             (nxst-node
               ;;              (lit-negate-cond fanin (get-bit m initsts))
               ;;              regid))
               ;;      (aignet-litp fanin (cdr mth-nxst-look2))
               ;;      (aignet-idp regid (cdr mth-nxst-look2)))
               ))))

(defsection aignet-copy-init
  :parents (aignet)
  :short "Set the initial state of an FSM to the all-0 convention."

  :long "<p>Some algorithms assume that an FSM's initial state is the one where
all registers are 0.  This normalizes an FSM that does not follow this
convention into one that does.  Given the aignet and an initial state vector,
this produces a new aignet that has registers toggled so that when its initial
value is 0, its sequential simulations produce the same values as the input
aignet when its initial value is the specified vector:</p>

@(def id-eval-seq-of-aignet-copy-init)

<p>This operation is similar to @(see aignet-complete-copy).</p>"

  (local (in-theory (e/d (lookup-stype-in-bounds)
                         (acl2::resize-list-when-atom))))
  (local (defthm resize-list-0
           (equal (resize-list lst 0 default)
                  nil)
           :hints(("Goal" :in-theory (enable resize-list)))))

  (define aignet-copy-init-aux (aignet initsts copy (gatesimp gatesimp-p) strash aignet2)
    :guard (<= (num-regs aignet) (bits-length initsts))
    :returns (mv copy strash aignet2)
    :hooks nil
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

    (defthm num-ins-of-aignet-copy-init-aux
      (equal (stype-count :pi (mv-nth 2 (aignet-copy-init-aux aignet initsts copy
                                                               gatesimp strash aignet2)))
             (stype-count :pi aignet)))

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
               :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))))

    (defthm id-eval-of-take-num-regs
      (equal (id-eval id invals
                      (take (stype-count :reg aignet) regvals)
                      aignet)
             (id-eval id invals regvals aignet))
      :hints (("goal" :induct (id-eval-ind id aignet)
               :expand ((:free (invals regvals)
                         (id-eval id invals regvals aignet)))
               :in-theory (enable lit-eval eval-and-of-lits eval-xor-of-lits))))

    (defthm lit-eval-of-take-num-ins
      (equal (lit-eval lit (take (stype-count :pi aignet) invals)
                       regvals aignet)
             (lit-eval lit invals regvals aignet))
      :hints(("Goal"
              :expand ((:free (invals regvals)
                        (lit-eval lit invals regvals aignet))))))


    (defthm eval-output-of-aignet-copy-init-aux
      (implies (< (nfix n) (num-outs aignet))
               (b* (((mv & & aignet2) (aignet-copy-init-aux aignet initsts copy gatesimp
                                                            strash aignet2)))
                 (equal (lit-eval (fanin :co (lookup-stype n (po-stype) aignet2))
                                  invals regvals aignet2)
                        (lit-eval (fanin :co (lookup-stype n (po-stype) aignet))
                                  invals
                                  (b-xor-lst initsts regvals)
                                  aignet))
                 ;; (equal (id-eval
                 ;;         (node-count (lookup-stype n (po-stype) aignet2))
                 ;;         invals regvals aignet2)
                 ;;        (id-eval
                 ;;         (node-count (lookup-stype n (po-stype) aignet))
                 ;;         invals
                 ;;         (b-xor-lst initsts regvals) aignet))
                 )))

    (defthm eval-nxst-of-aignet-copy-init-aux
      (implies (< (nfix n) (num-regs aignet))
               (b* (((mv & & aignet2)
                     (aignet-copy-init-aux aignet initsts copy gatesimp strash aignet2)))
                 (equal (lit-eval (fanin-if-co (lookup-regnum->nxst n aignet2))
                                  invals regvals aignet2)
                        (b-xor (nth n initsts)
                               (lit-eval (fanin-if-co (lookup-regnum->nxst n aignet))
                                         invals
                                         (b-xor-lst initsts regvals) aignet))))))

    (fty::deffixequiv aignet-copy-init-aux :args ((gatesimp gatesimp-p))))

  (define aignet-copy-init (aignet initsts &key
                                   ((gatesimp gatesimp-p) '(default-gatesimp))
                                   (aignet2 'aignet2))
    :parents nil
    :guard (<= (num-regs aignet) (bits-length initsts))
    :returns aignet2
    (b* (((local-stobjs copy strash)
          (mv copy strash aignet2)))
      (mbe :logic
           (non-exec (aignet-copy-init-aux (node-list-fix aignet) initsts copy gatesimp strash aignet2))
           :exec
           (aignet-copy-init-aux aignet initsts copy gatesimp strash aignet2)))
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

    (defthm num-ins-of-aignet-copy-init
      (equal (stype-count :pi (aignet-copy-init aignet initsts :gatesimp gatesimp))
             (stype-count :pi aignet)))

    (defthm eval-output-of-aignet-copy-init
      (implies (< (nfix n) (num-outs aignet))
               (b* ((aignet2 (aignet-copy-init aignet initsts :gatesimp gatesimp)))
                 (equal (lit-eval (fanin :co (lookup-stype n (po-stype) aignet2))
                                  invals regvals aignet2)
                        (lit-eval (fanin :co (lookup-stype n (po-stype) aignet))
                                  invals
                                  (b-xor-lst initsts regvals)
                                  aignet)))))

    (defthm eval-nxst-of-aignet-copy-init
      (implies (< (nfix n) (num-regs aignet))
               (b* ((aignet2 (aignet-copy-init aignet initsts :gatesimp gatesimp)))
                 (equal (lit-eval (fanin-if-co (lookup-regnum->nxst n aignet2))
                                  invals regvals aignet2)
                        (b-xor (nth n initsts)
                               (lit-eval (fanin-if-co (lookup-regnum->nxst n aignet))
                                         invals
                                         (b-xor-lst initsts regvals) aignet)))))))

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

  ;; (local (in-theory (disable acl2::take-when-atom)))

  (defthm take-of-b-xor-lst
    (bits-equiv (take n (b-xor-lst a (take n b)))
                (take n (b-xor-lst a b)))
    :hints(("Goal" :in-theory (enable bits-equiv))))

  (defcong bits-equiv bits-equiv (take n x) 2)

  (local (defthm lit-eval-b-xor-lst-take-subst
           (equal (lit-eval id ins
                           (b-xor-lst x (take (stype-count :reg aignet) y))
                           aignet)
                  (lit-eval id ins
                            (b-xor-lst x y) aignet))
           :hints (("goal" :use ((:instance lit-eval-of-take-num-regs
                                  (invals ins)
                                  (regvals
                                   (b-xor-lst x (take (stype-count :reg aignet) y)))))))))

  (local (defthm lit-eval-of-take-num-regs-strong
           (implies (equal nregs (stype-count :reg aignet))
                    (equal (lit-eval lit invals
                                     (take nregs regvals)
                                     aignet)
                           (lit-eval lit invals regvals aignet)))
           :hints(("Goal"
                   :expand ((:free (invals regvals)
                             (lit-eval lit invals regvals aignet)))))))



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
                                     nth-of-frame-regvals-split
                                     reg-eval-seq)
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

  (defthm lit-eval-seq-of-aignet-copy-init
    (b* ((aignet2 (aignet-copy-init aignet initsts :gatesimp gatesimp)))
      (equal (lit-eval-seq k (fanin :co (lookup-stype n :po aignet2))
                          frames nil aignet2)
             (lit-eval-seq k (fanin :co (lookup-stype n :po aignet))
                           frames initsts aignet)))
    :hints(("Goal" :use id-eval-seq-of-aignet-copy-init
            :in-theory (e/d (fanin-if-co)
                            (id-eval-seq-of-aignet-copy-init)))))

  (defthm output-eval-seq-of-aignet-copy-init
    (b* ((aignet2 (aignet-copy-init aignet initsts :gatesimp gatesimp)))
      (equal (output-eval-seq k n frames nil aignet2)
             (output-eval-seq k n frames initsts aignet)))
    :hints(("Goal" :in-theory (enable output-eval-seq))))

  (defthm seq-equiv-init-of-aignet-copy-init
    (seq-equiv-init (aignet-copy-init aignet initsts :gatesimp gatesimp)
                    nil
                    aignet initsts)
    :hints(("Goal" :in-theory (e/d (seq-equiv-init output-eval-seq) (aignet-copy-init)))))

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
                    (and witness
                         `(:clause-processor
                           (acl2::simple-generalize-cp
                            clause '(((mv-nth '0 ,witness) . k)
                                     ((mv-nth '1 ,witness) . n)
                                     ((mv-nth '2 ,witness) . inframes)))))))
            (and stable-under-simplificationp
                 '(:use ((:instance seq-equiv-necc
                          (aignet (aignet-copy-init-fn aignet initsts (default-gatesimp) nil))
                          (aignet2 (aignet-copy-init-fn aignet2 initsts2 (default-gatesimp) nil))))
                   :in-theory (e/d () (seq-equiv-necc)))))
    :otf-flg t))







(acl2::defstobj-clone mark bitarr :suffix "-MARK")

(defsection aignet-input-copies-in-bounds
  (defun-sk aignet-input-copies-in-bounds (copy aignet aignet2)
    (forall n
            (implies (equal (id->type n aignet) (in-type))
                     (aignet-litp (nth-lit n copy) aignet2)))
    :rewrite :direct)

  
  (in-theory (disable aignet-input-copies-in-bounds))

  (defthm aignet-input-copies-in-bounds-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-input-copies-in-bounds copy aignet orig))
             (aignet-input-copies-in-bounds copy aignet new))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-input-copies-in-bounds-of-update-copy
    (implies (and (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-litp lit aignet2))
             (aignet-input-copies-in-bounds (update-nth-lit n lit copy) aignet aignet2))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-input-copies-in-bounds-of-update-non-input
    (implies (and (aignet-input-copies-in-bounds copy aignet aignet2)
                  (not (equal (id->type n aignet) (in-type))))
             (aignet-input-copies-in-bounds (update-nth-lit n lit copy) aignet aignet2))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-copies-in-bounds-implies-aignet-input-copies-in-bounds
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-input-copies-in-bounds copy aignet aignet2))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (fty::deffixequiv aignet-input-copies-in-bounds :args ((aignet aignet) (aignet2 aignet))
    :hints(("Goal" :in-theory (disable aignet-input-copies-in-bounds)
            :cases ((aignet-input-copies-in-bounds copy aignet aignet2)))
           (and stable-under-simplificationp
                (b* ((lit (assoc 'aignet-input-copies-in-bounds clause))
                     (other (cadr (assoc 'not clause))))
                  `(:expand (,lit)
                    :in-theory (disable aignet-input-copies-in-bounds-necc)
                    :use ((:instance aignet-input-copies-in-bounds-necc
                           (copy ,(cadr other))
                           (aignet ,(caddr other))
                           (aignet2 ,(cadddr other))
                           (n (aignet-input-copies-in-bounds-witness . ,(cdr lit)))))))))))

(defsection aignet-marked-copies-in-bounds
  (defun-sk aignet-marked-copies-in-bounds (copy mark aignet2)
    (forall n
            (implies (bit->bool (nth n mark))
                     (aignet-litp (nth-lit n copy) aignet2)))
    :rewrite :direct)

  (in-theory (disable aignet-marked-copies-in-bounds))

  (defthm aignet-marked-copies-in-bounds-of-extension
    (implies (and (aignet-extension-binding)
                  (aignet-marked-copies-in-bounds copy mark orig))
             (aignet-marked-copies-in-bounds copy mark new))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-marked-copies-in-bounds-of-update-copy
    (implies (and (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-litp lit aignet2))
             (aignet-marked-copies-in-bounds (update-nth-lit n lit copy) mark aignet2))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm aignet-marked-copies-in-bounds-of-update-mark
    (implies (and (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-litp (nth-lit n copy) aignet2))
             (aignet-marked-copies-in-bounds copy
                                                (update-nth n 1 mark)
                                                aignet2))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable* acl2::arith-equiv-forwarding)))))


  (defthm aignet-copies-in-bounds-implies-aignet-marked-copies-in-bounds
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-marked-copies-in-bounds copy mark aignet2))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (fty::deffixequiv aignet-marked-copies-in-bounds :args ((aignet2 aignet))
    :hints(("Goal" :in-theory (disable aignet-marked-copies-in-bounds)
            :cases ((aignet-marked-copies-in-bounds copy mark aignet2)))
           (and stable-under-simplificationp
                (b* ((lit (assoc 'aignet-marked-copies-in-bounds clause))
                     (other (cadr (assoc 'not clause))))
                  `(:expand (,lit)
                    :in-theory (disable aignet-marked-copies-in-bounds-necc)
                    :use ((:instance aignet-marked-copies-in-bounds-necc
                           (copy ,(cadr other))
                           (mark ,(caddr other))
                           (aignet2 ,(cadddr other))
                           (n (aignet-marked-copies-in-bounds-witness . ,(cdr lit)))))))))))


;; (defsection aignet-in/marked-copies-in-bounds
;;   (defun-sk aignet-in/marked-copies-in-bounds (copy mark aignet aignet2)
;;     (forall n
;;             (implies (or (equal (id->type n aignet) (in-type))
;;                          (bit->bool (nth n mark)))
;;                      (aignet-litp (nth-lit n copy) aignet2)))
;;     :rewrite :direct)

;;   (in-theory (disable aignet-in/marked-copies-in-bounds))

;;   (defthm aignet-in/marked-copies-in-bounds-of-extension
;;     (implies (and (aignet-extension-binding)
;;                   (aignet-in/marked-copies-in-bounds copy mark aignet orig))
;;              (aignet-in/marked-copies-in-bounds copy mark aignet new))
;;     :hints ((and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))))

;;   (defthm aignet-in/marked-copies-in-bounds-of-update-copy
;;     (implies (and (aignet-in/marked-copies-in-bounds copy mark aignet aignet2)
;;                   (aignet-litp lit aignet2))
;;              (aignet-in/marked-copies-in-bounds (update-nth-lit n lit copy) mark aignet aignet2))
;;     :hints ((and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))))

;;   (defthm aignet-in/marked-copies-in-bounds-of-update-mark
;;     (implies (and (aignet-in/marked-copies-in-bounds copy mark aignet aignet2)
;;                   (aignet-litp (nth-lit n copy) aignet2))
;;              (aignet-in/marked-copies-in-bounds copy
;;                                                 (update-nth n 1 mark)
;;                                                 aignet aignet2))
;;     :hints ((and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))
;;                    :in-theory (enable* acl2::arith-equiv-forwarding)))))


;;   (defthm aignet-copies-in-bounds-implies-aignet-in/marked-copies-in-bounds
;;     (implies (aignet-copies-in-bounds copy aignet2)
;;              (aignet-in/marked-copies-in-bounds copy mark aignet aignet2))
;;     :hints ((and stable-under-simplificationp
;;                  `(:expand (,(car (last clause))))))))


(define aignet-copy-dfs-rec ((id natp :type (integer 0 *))
                             aignet
                             mark
                             copy
                             strash
                             (gatesimp gatesimp-p)
                             aignet2)
  :split-types t
  :guard (and (id-existsp id aignet)
              (< id (bits-length mark))
              (< id (lits-length copy))
              (ec-call (aignet-marked-copies-in-bounds copy mark aignet2))
              (ec-call (aignet-input-copies-in-bounds copy aignet aignet2)))
  :returns (mv new-mark
               new-copy
               new-strash
               new-aignet2)
  :verify-guards nil
  (b* (((when (int= (get-bit id mark) 1))
        (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv mark copy strash aignet2)))
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
             (copy (set-lit id 0 copy))
             (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv mark copy strash aignet2)))

       ((unless (int= type (gate-type)))
        (b* ((mark (set-bit id 1 mark))
             (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv mark copy strash aignet2)))

       ;; gate: recur on each fanin, then hash an AND of the two copies
       (f0 (snode->fanin slot0))
       (slot1 (id->slot id 1 aignet))
       (f1 (snode->fanin slot1))
       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-rec
         (lit-id f0) aignet mark copy strash gatesimp aignet2))
       (f0-copy (lit-copy f0 copy))
       (xor (snode->regp slot1))
       ((when (and (int= f0-copy 0) (eql xor 0)))
        ;; first branch was 0 so exit early
        (b* ((copy (set-lit id 0 copy))
             (mark (set-bit id 1 mark)))
          (mv mark copy strash aignet2)))
       ((mv mark copy strash aignet2)
        (aignet-copy-dfs-rec
         (lit-id f1) aignet mark copy strash gatesimp aignet2))
       (f1-copy (lit-copy f1 copy))
       ((mv id-copy strash aignet2)
        (if (eql xor 1)
            (aignet-hash-xor f0-copy f1-copy gatesimp strash aignet2)
          (aignet-hash-and f0-copy f1-copy gatesimp strash aignet2)))
       (copy (set-lit id id-copy copy))
       (mark (set-bit id 1 mark)))
    (mv mark copy strash aignet2))

  ///

  ;; (defthm litp-of-lit-negate-cond
  ;;   (litp (lit-negate-cond lit neg)))

  (local (in-theory (disable lit-negate-cond acl2::b-xor
                             (:d aignet-copy-dfs-rec)
                             ;; aignet-copies-ok
                             )))

  (def-aignet-preservation-thms aignet-copy-dfs-rec :stobjname aignet2)

  (defret mark-preserved-of-aignet-copy-dfs-rec
    (implies (equal 1 (nth n mark))
             (equal (nth n new-mark) 1))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret mark-set-of-aignet-copy-dfs-rec
    (equal (nth id new-mark) 1)
    :hints (("goal" :expand (<call>))))

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

  (defret copies-sized-of-aignet-copy-dfs-rec
    (<= (len copy)
        (len new-copy))
    :hints ((acl2::just-induct-and-expand <call>))
    :rule-classes :linear)

  (defret mark-sized-of-aignet-copy-dfs-rec
    (<= (len mark)
        (len new-mark))
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

  ;; (defthm aignet-copies-ok-implies-special-bind-free
  ;;   (implies (and (bind-free '((aignet1 . aignet)) (aignet1))
  ;;                 (aignet-copies-in-bounds copy aignet)
  ;;                 (aignet-idp k aignet1))
  ;;            (aignet-litp (nth-lit k copy) aignet)))

  (local (in-theory (enable lit-negate-cond)))

  (defret aignet-input-copies-in-bounds-of-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-input-copies-in-bounds new-copy aignet new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-marked-copies-in-bounds-of-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-marked-copies-in-bounds new-copy new-mark new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))


  (defret aignet-copies-in-bounds-of-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (aignet-copies-in-bounds copy aignet2))
             (aignet-copies-in-bounds new-copy new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-input-copies-in-bounds-of-aignet-copy-dfs-rec-rw
    (implies (and (aignet-idp id aignet)
                  (equal (id->type n aignet) (in-type))
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-litp (nth-lit n new-copy) new-aignet2))
    :hints (("goal" :use ((:instance aignet-input-copies-in-bounds-necc
                           (aignet2 new-aignet2)
                           (copy new-copy)
                           (n n)))
             :in-theory (e/d ()
                             (aignet-input-copies-in-bounds-necc
                              aignet-copy-dfs-rec)))))

  (defret aignet-marked-copies-in-bounds-of-aignet-copy-dfs-rec-rw
    (implies (and (aignet-idp id aignet)
                  (bit->bool (nth n new-mark))
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-litp (nth-lit n new-copy) new-aignet2))
    :hints (("goal" :use ((:instance aignet-marked-copies-in-bounds-necc
                           (aignet2 new-aignet2)
                           (copy new-copy)
                           (mark new-mark)
                           (n n)))
             :in-theory (e/d ()
                             (aignet-marked-copies-in-bounds-necc
                              aignet-copy-dfs-rec)))))

  (verify-guards aignet-copy-dfs-rec
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defret stype-counts-preserved-of-aignet-copy-dfs-rec
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand <call>))))

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
                  (aignet-input-copies-in-bounds copy aignet orig))
             (equal (input-copy-values n invals regvals aignet copy new)
                    (input-copy-values n invals regvals aignet copy orig))))

  (local (in-theory (enable (:i aignet-copy-dfs-rec))))

  (defthm input-copy-values-of-aignet-copy-dfs-rec
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
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
                  (aignet-input-copies-in-bounds copy aignet orig))
             (equal (reg-copy-values n invals regvals aignet copy new)
                    (reg-copy-values n invals regvals aignet copy orig))))

  (local (in-theory (enable (:i aignet-copy-dfs-rec))))

  (defthm reg-copy-values-of-aignet-copy-dfs-rec
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (b* (((mv ?new-mark ?new-copy ?new-strash ?new-aignet2)
                   (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))
               (equal (reg-copy-values n invals regvals aignet new-copy new-aignet2)
                      (reg-copy-values n invals regvals aignet copy aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2)))))


(defsection aignet-copy-dfs-rec
  (local (in-theory (enable (:i aignet-copy-dfs-rec))))

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

  (local (defthm make-lit-equal-0
           (equal (equal (make-lit var neg) 0)
                  (and (nat-equiv var 0)
                       (not (equal neg 1))))
           :hints(("Goal" :in-theory (enable satlink::equal-of-make-lit)))))

  (local (defthm dfs-copy-onto-invar-implies-id-eval
           (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                         (aignet-idp id aignet)
                         (equal 1 (get-bit id mark)))
                    (equal (id-eval (lit->var (nth-lit id copy)) invals regvals aignet2)
                           (b-xor (lit->neg (nth-lit id copy))
                                  (id-eval id
                                           (input-copy-values 0 invals regvals aignet copy aignet2)
                                           (reg-copy-values 0 invals regvals aignet copy aignet2)
                                           aignet))))
           :hints (("goal" :use dfs-copy-onto-invar-necc
                    :in-theory (e/d (lit-eval) (dfs-copy-onto-invar-necc))))))


  (defthm dfs-copy-onto-invar-holds-of-aignet-copy-dfs-rec
    (implies (and (aignet-idp id aignet)
                  (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
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
                 '(:in-theory (enable eval-and-of-lits eval-xor-of-lits
                                      lit-negate-cond)
                   :expand ((:free (in-vals reg-vals)
                             (id-eval id in-vals reg-vals aignet)))))
            (and stable-under-simplificationp
                 '(:in-theory (enable lit-eval)))
            (and stable-under-simplificationp
                 (member-equal '(NOT (EQUAL (stype$inline (car (lookup-id id aignet))) ':and))
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
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
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

(define aignet-copy-dfs-eba-rec ((id :type (integer 0 *))
                                 aignet
                                 eba
                                 copy
                                 strash
                                 (gatesimp gatesimp-p)
                                 aignet2)
  :guard (and (id-existsp id aignet)
              (< id (eba-length eba))
              (< id (lits-length copy))
              (ec-call (aignet-marked-copies-in-bounds copy eba aignet2))
              (ec-call (aignet-input-copies-in-bounds copy aignet aignet2)))
  :verify-guards nil
  :measure (nfix id)
  (b* (((when (int= (eba-get-bit id eba) 1))
        (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv eba copy strash aignet2)))
       (slot0 (id->slot id 0 aignet))
       (type (snode->type slot0))
       ((when (int= type (out-type)))
        ;; copy the fanin of the output and set the output ID's copy to be
        ;; that of the fanin lit
        (b* ((f (co-id->fanin id aignet))
             ((mv eba copy strash aignet2)
              (aignet-copy-dfs-eba-rec
               (lit-id f) aignet eba copy strash gatesimp
               aignet2))
             (f-copy (lit-copy f copy))
             (copy (set-lit id f-copy copy))
             (eba (eba-set-bit id eba)))
          (mv eba copy strash aignet2)))

       ((when (int= type (const-type)))
        (b* ((eba (eba-set-bit id eba))
             (copy (set-lit id 0 copy))
             (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv eba copy strash aignet2)))

       ((unless (int= type (gate-type)))
        (b* ((eba (eba-set-bit id eba))
             (aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                           :exec aignet2)))
          (mv eba copy strash aignet2)))

       ;; gate: recur on each fanin, then hash an AND of the two copies
       (f0 (snode->fanin slot0))
       (slot1 (id->slot id 1 aignet))
       (f1 (snode->fanin slot1))
       ((mv eba copy strash aignet2)
        (aignet-copy-dfs-eba-rec
         (lit-id f0) aignet eba copy strash gatesimp aignet2))
       (f0-copy (lit-copy f0 copy))
       (xor (snode->regp slot1))
       ((when (and (int= f0-copy 0) (eql xor 0)))
        ;; first branch was 0 so exit early
        (b* ((copy (set-lit id 0 copy))
             (eba (eba-set-bit id eba)))
          (mv eba copy strash aignet2)))
       ((mv eba copy strash aignet2)
        (aignet-copy-dfs-eba-rec
         (lit-id f1) aignet eba copy strash gatesimp aignet2))
       (f1-copy (lit-copy f1 copy))
       ((mv id-copy strash aignet2)
        (if (eql xor 1)
            (aignet-hash-xor f0-copy f1-copy gatesimp strash aignet2)
          (aignet-hash-and f0-copy f1-copy gatesimp strash aignet2)))
       (copy (set-lit id id-copy copy))
       (eba (eba-set-bit id eba)))
    (mv eba copy strash aignet2))
  ///
  (defthm aignet-copy-dfs-eba-rec-is-aignet-copy-dfs-rec
    (equal (aignet-copy-dfs-eba-rec id aignet eba copy strash gatesimp aignet2)
           (aignet-copy-dfs-rec id aignet eba copy strash gatesimp aignet2))
    :hints (("goal" :induct (aignet-copy-dfs-eba-rec id aignet eba copy strash gatesimp aignet2)
             :in-theory (disable (:d aignet-copy-dfs-eba-rec))
             :expand ((aignet-copy-dfs-eba-rec id aignet eba copy strash gatesimp aignet2)
                      (aignet-copy-dfs-rec id aignet eba copy strash gatesimp aignet2)))))

  (verify-guards aignet-copy-dfs-eba-rec))




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

  (defret aignet-copies-in-bounds-of-init-copy-comb
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
              (<= (num-regs aignet) (num-regs aignet2))
              (ec-call (aignet-po-copies-in-bounds copy aignet aignet2))
              (ec-call (aignet-nxst-copies-in-bounds copy aignet aignet2)))
  :returns (new-aignet2)
  (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                     :exec aignet2))
       (aignet2 (aignet-copy-outs-from-fanins aignet copy aignet2)))
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
                  (aignet-po-copies-in-bounds copy aignet aignet2))
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
                  (aignet-nxst-copies-in-bounds copy aignet aignet2))
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
                  (aignet-po-copies-in-bounds copy aignet aignet2)
                  (aignet-nxst-copies-in-bounds copy aignet aignet2))
             (comb-equiv new-aignet2 aignet))
    :hints(("Goal" :in-theory (e/d (comb-equiv) (finish-copy-comb))))))
