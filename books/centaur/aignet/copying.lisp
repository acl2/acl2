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
(include-book "lit-lists")
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))


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

(std::make-returnspec-config :hints-sub-returnnames t)

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
;;     (implies (and (aignet-copies-ok (+ 1 (fanin-count aignet1)) copy aignet)
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
            (ec-call (aignet-idp (lit->var (ec-call (nth-lit n copy))) aignet)))
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

  (defthm aignet-copies-in-bounds-lte
    (implies (aignet-copies-in-bounds copy aignet)
             (<= (lit->var (nth-lit n copy)) (fanin-count aignet)))
    :hints (("goal" :use ((:instance aignet-copies-in-bounds-necc))
             :in-theory (e/d (aignet-idp) (aignet-copies-in-bounds-necc)))))

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

  ;; (defmacro lit-copy (lit aignet-copyv)
  ;;   `(let ((lit-copy-lit ,lit))
  ;;      (lit-negate-cond (get-lit (lit-id lit-copy-lit) ,aignet-copyv)
  ;;                       (lit-neg lit-copy-lit))))

  (defiteration aignet-copy-comb (aignet copy gatesimp strash aignet2)
    (declare (xargs :stobjs (aignet copy strash aignet2)
                    :guard (and (<= (num-fanins aignet) (lits-length copy))
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
       :const (b* ((copy (set-lit nid 0 copy)))
                (mv copy strash aignet2))))
    :returns (mv copy strash aignet2)
    :index n
    :last (num-fanins aignet)
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
                    (<= (nfix n) (num-fanins aignet)))
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

  (defthm copy-length-of-aignet-copy-comb-iter
    (implies (and (<= (num-fanins aignet) (len copy))
                  (<= (nfix n) (num-fanins aignet)))
             (equal (len (mv-nth 0 (aignet-copy-comb-iter
                                    n aignet copy gatesimp strash
                                    aignet2)))
                    (len copy)))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy
                                    gatesimp strash aignet2))))

  (defthm copy-length-of-aignet-copy-comb
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len (mv-nth 0 (aignet-copy-comb aignet copy gatesimp strash aignet2)))
                    (len copy))))

  (defthm aignet-copy-sized-of-aignet-copy-comb-iter
    (implies (and (<= (num-fanins aignet) (lits-length copy))
                  (<= (nfix n) (num-fanins aignet)))
             (< (fanin-count aignet)
                (len (mv-nth 0 (aignet-copy-comb-iter
                                n aignet copy gatesimp strash
                                aignet2)))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-comb-iter n aignet copy
                                    gatesimp strash aignet2)))
    :rule-classes :linear)

  (defthm aignet-copy-sized-of-aignet-copy-comb
    (implies (<= (num-fanins aignet) (lits-length copy))
             (< (fanin-count aignet)
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


;; BOZO this is basically the same as aignet-copy-comb-in-vals
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

  (local (defthm nth-of-nil
           (equal (nth n nil) nil)
           :hints(("Goal" :in-theory (enable nth)))))

  (local (defret nth-of-input-copy-values-out-of-bounds-lemma
           (implies (<= (num-ins aignet) (nfix m))
                    (equal (nth (- (nfix m) (nfix n)) input-vals) nil))
           :hints(("Goal" :induct <call>
                   :expand ((:free (m a b) (nth m (cons a b))))))))

  (defret nth-of-input-copy-values-out-of-bounds
    (implies (<= (num-ins aignet) (+ (nfix m) (nfix n)))
             (equal (nth m input-vals) nil))
    :hints(("Goal" :use ((:instance nth-of-input-copy-values-out-of-bounds-lemma
                          (m (+ (nfix m) (nfix n)))))
            :in-theory (disable nth-of-input-copy-values-out-of-bounds-lemma
                                input-copy-values))))

  (defretd nth-of-input-copy-values-split
    (equal (nth m input-vals)
           (and (< (+ (nfix m) (nfix n)) (num-ins aignet))
                (lit-eval (nth-lit (innum->id (+ (nfix m) (nfix n)) aignet) copy)
                              invals regvals aignet2))))

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

  (defthm input-copy-values-of-aignet-copy-comb
    (b* (((mv new-copy & &)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (equal (input-copy-values n invals regvals aignet new-copy aignet22)
             (input-copy-values n invals regvals aignet copy aignet22)))))

;; BOZO this is basically the same as aignet-copy-comb-reg-vals
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

  (local (defthm nth-of-nil
           (equal (nth n nil) nil)
           :hints(("Goal" :in-theory (enable nth)))))

  (local (defret nth-of-reg-copy-values-out-of-bounds-lemma
           (implies (<= (num-regs aignet) (nfix m))
                    (equal (nth (- (nfix m) (nfix n)) reg-vals) nil))
           :hints(("Goal" :induct <call>
                   :expand ((:free (m a b) (nth m (cons a b))))))))

  (defret nth-of-reg-copy-values-out-of-bounds
    (implies (<= (num-regs aignet) (+ (nfix m) (nfix n)))
             (equal (nth m reg-vals) nil))
    :hints(("Goal" :use ((:instance nth-of-reg-copy-values-out-of-bounds-lemma
                          (m (+ (nfix m) (nfix n)))))
            :in-theory (disable nth-of-reg-copy-values-out-of-bounds-lemma
                                reg-copy-values))))

  (defretd nth-of-reg-copy-values-split
    (equal (nth m reg-vals)
           (and (< (+ (nfix m) (nfix n)) (num-regs aignet))
                (lit-eval (nth-lit (regnum->id (+ (nfix m) (nfix n)) aignet) copy)
                              invals regvals aignet2))))

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

  (defthm reg-copy-values-of-aignet-copy-comb
    (b* (((mv new-copy & &)
          (aignet-copy-comb aignet copy gatesimp strash aignet2)))
      (equal (reg-copy-values n invals regvals aignet new-copy aignet22)
             (reg-copy-values n invals regvals aignet copy aignet22)))))




;; (defsection aignet-copy-comb-in-vals
;;   (def-list-constructor aignet-copy-comb-in-vals
;;     (invals regvals aignet2 copy aignet)
;;     (declare (xargs :stobjs (aignet2 copy aignet invals regvals)
;;                     :guard (and (<= (num-fanins aignet) (lits-length copy))
;;                                 (aignet-copies-in-bounds
;;                                           copy aignet2)
;;                                 (<= (num-ins aignet2) (bits-length invals))
;;                                 (<= (num-regs aignet2) (bits-length regvals)))))
;;     (b* ((in-id (innum->id n aignet))
;;          (copy-lit (get-lit in-id copy)))
;;       (lit-eval copy-lit invals regvals aignet2))
;;     :length (num-ins aignet))

;;   (local (set-default-hints
;;           '((and stable-under-simplificationp
;;                  (acl2::equal-by-nths-hint)))))

;;   (defthm aignet-copy-in-vals-of-extension
;;     (implies (and (aignet-extension-binding :new new2
;;                                             :orig aignet2)
;;                   (aignet-copies-in-bounds
;;                                     copy aignet2))
;;              (equal (aignet-copy-comb-in-vals
;;                      invals regvals new2 copy aignet)
;;                     (aignet-copy-comb-in-vals
;;                      invals regvals aignet2 copy aignet))))

;;   ;; This holds because aignet-copy-comb doesn't touch the copy pointers of
;;   ;; CI nodes
;;   (defthm aignet-copy-in-vals-after-copy-comb-copy
;;     (b* (((mv aignet-copy2 & &)
;;           (aignet-copy-comb aignet copy gatesimp strash aignet2)))
;;       (equal (aignet-copy-comb-in-vals
;;               invals regvals aignet22 aignet-copy2 aignet)
;;              (aignet-copy-comb-in-vals
;;               invals regvals aignet22 copy aignet)))))


;; (defsection aignet-copy-comb-reg-vals
;;   (def-list-constructor aignet-copy-comb-reg-vals
;;     (invals regvals aignet2 copy aignet)
;;     (declare (xargs :stobjs (aignet2 copy aignet invals regvals)
;;                     :guard (and (<= (num-fanins aignet) (lits-length copy))
;;                                 (aignet-copies-in-bounds copy aignet2)
;;                                 (<= (num-ins aignet2) (bits-length invals))
;;                                 (<= (num-regs aignet2) (bits-length regvals)))))
;;     (b* ((reg-id (regnum->id n aignet))
;;          (copy-lit (get-lit reg-id copy)))
;;       (lit-eval copy-lit invals regvals aignet2))
;;     :length (num-regs aignet))


;;   (local (set-default-hints
;;           '((and stable-under-simplificationp
;;                  (acl2::equal-by-nths-hint)))))

;;   (defthm aignet-copy-reg-vals-of-extension
;;     (implies (and (aignet-extension-binding :new new2
;;                                             :orig aignet2)
;;                   (aignet-copies-in-bounds
;;                                     copy aignet2))
;;              (equal (aignet-copy-comb-reg-vals
;;                          invals regvals new2 copy aignet)
;;                         (aignet-copy-comb-reg-vals
;;                          invals regvals aignet2 copy aignet))))

;;   (defthm aignet-copy-reg-vals-after-copy-comb-copy
;;     (b* (((mv aignet-copy2 & &)
;;           (aignet-copy-comb aignet copy gatesimp strash aignet2)))
;;       (equal (aignet-copy-comb-reg-vals
;;               invals regvals aignet22 aignet-copy2 aignet)
;;              (aignet-copy-comb-reg-vals
;;               invals regvals aignet22 copy aignet)))))


(defsection aignet-copy-comb-correct

  (local
   (defun-sk eval-of-aignet-copy-comb-invariant
     (n invals regvals aignet-copy1 aignet21 aignet2 copy aignet)
     (forall m
             (implies (< (nfix m) (nfix n))
                      (equal (lit-eval (nth-lit m aignet-copy1)
                                       invals regvals aignet21)
                             (id-eval m
                                      (input-copy-values
                                       0 invals regvals aignet copy aignet2)
                                      (reg-copy-values
                                       0 invals regvals aignet copy aignet2)
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
                  (< (nfix m) (num-fanins aignet))
                  (<= (nfix n) (num-fanins aignet)))
             (b* (((mv copy & aignet2)
                   (aignet-copy-comb-iter
                    n aignet copy
                    gatesimp strash aignet2)))
               (aignet-litp (nth-lit m copy) aignet2)))
    :hints (("goal" :use ((:instance aignet-copies-ok-of-aignet-copy-comb-iter))
             :in-theory (disable aignet-copies-ok-of-aignet-copy-comb-iter))))

  (local
   (defthm eval-of-aignet-copy-comb-lemma
     (implies (and (<= (nfix n) (num-fanins aignet))
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
                              (lit-eval lit invals regvals aignet)))
                    :in-theory (enable lit-copy eval-and-of-lits eval-xor-of-lits))))))

  (defthm eval-of-aignet-copy-comb-iter
    (implies (and (<= (nfix n) (num-fanins aignet))
                  (aignet-copies-in-bounds copy aignet2)
                  (< (nfix m) (nfix n)))
             (b* (((mv aignet-copy1 & aignet21)
                   (aignet-copy-comb-iter
                    n aignet copy gatesimp strash aignet2)))
               (equal (lit-eval (nth-lit m aignet-copy1)
                                invals regvals aignet21)
                      (id-eval m
                               (input-copy-values
                                0 invals regvals aignet copy aignet2)
                               (reg-copy-values
                                0 invals regvals aignet copy aignet2)
                               aignet))))
    :hints (("goal" :use ((:instance eval-of-aignet-copy-comb-lemma))
             :in-theory (disable eval-of-aignet-copy-comb-lemma))))

  (defthm eval-of-aignet-copy-comb
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (< (nfix m) (num-fanins aignet)))
             (b* (((mv aignet-copy1 & aignet21)
                   (aignet-copy-comb aignet copy gatesimp strash aignet2)))
               (equal (lit-eval (nth-lit m aignet-copy1)
                                invals regvals aignet21)
                      (id-eval m
                               (input-copy-values
                                0 invals regvals aignet copy aignet2)
                               (reg-copy-values
                                0 invals regvals aignet copy aignet2)
                               aignet))))
    :hints(("Goal" :in-theory (enable aignet-copy-comb))))

  (defthm eval-of-aignet-copy-comb-lit-copy
    (implies (and (aignet-copies-in-bounds copy aignet2)
                  (aignet-litp m aignet))
             (b* (((mv aignet-copy1 & aignet21)
                   (aignet-copy-comb aignet copy gatesimp strash aignet2)))
               (equal (lit-eval (lit-copy m aignet-copy1)
                                invals regvals aignet21)
                      (lit-eval m
                                (input-copy-values
                                 0 invals regvals aignet copy aignet2)
                                (reg-copy-values
                                 0 invals regvals aignet copy aignet2)
                               aignet))))
    :hints (("goal" :in-theory (enable lit-copy aignet-idp)
             :expand ((:free (invals regvals) (lit-eval m invals regvals aignet)))))))


(local (in-theory (disable acl2::nfix-when-not-natp
                           acl2::natp-when-integerp)))

  ;; Utilities for copying IOs


(local (defthm len-of-update-nth-lit-preserved
         (implies (< (nfix n) (len x))
                  (equal (len (update-nth-lit n val x))
                         (len x)))
         :hints(("Goal" :in-theory (enable update-nth-lit)))))





(define aignet-copy-set-ins ((n natp)
                             (aignet)
                             (copy)
                             (aignet2))
  ;; Sets the copy of each PI ID of aignet to the corresponding PI lit of aignet2, beginning at input number N.
  :guard (and (<= n (num-ins aignet))
              (<= (num-ins aignet) (num-ins aignet2))
              (<= (num-fanins aignet) (lits-length copy)))
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
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (defret nth-lit-of-aignet-copy-set-ins
    (equal (nth-lit id new-copy)
           (if (and (eq (stype (car (lookup-id id aignet))) :pi)
                    (<= (nfix n) (stype-count :pi (cdr (lookup-id id aignet)))))
               (make-lit (fanin-count (lookup-stype (stype-count :pi (cdr (lookup-id id aignet))) :pi aignet2))
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

  ;; (local (defthm aignet-litp-of-lookup-stype
  ;;          (aignet-litp (make-lit (fanin-count (lookup-stype n :pi aignet)) neg) aignet)
  ;;          :hints(("Goal" :in-theory (enable aignet-litp)
  ;;                  :cases ((< (nfix n) (num-ins aignet)))))))

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
              (<= (num-fanins aignet) (lits-length copy)))
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
    (implies (<= (num-fanins aignet) (len copy))
             (equal (len new-copy) (len copy))))

  (defret nth-lit-of-aignet-copy-set-regs
    (equal (nth-lit id new-copy)
           (if (and (eq (stype (car (lookup-id id aignet))) :reg)
                    (<= (nfix n) (stype-count :reg (cdr (lookup-id id aignet)))))
               (make-lit (fanin-count (lookup-stype (stype-count :reg (cdr (lookup-id id aignet))) :reg aignet2))
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

  ;; (local (defthm aignet-litp-of-lookup-stype
  ;;          (aignet-litp (make-lit (fanin-count (lookup-stype n :reg aignet)) neg) aignet)
  ;;          :hints(("Goal" :in-theory (enable aignet-litp)
  ;;                  :cases ((< (nfix n) (num-regs aignet)))))))

  (defret aignet-copies-in-bounds-of-aignet-copy-set-regs
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy aignet2))))

(define aignet-copy-ins (aignet copy aignet2)
  :guard (<= (num-fanins aignet) (lits-length copy))
  :returns (mv new-copy new-aignet2)
  (b* ((aignet2 (aignet-add-ins (num-ins aignet) aignet2))
       (copy (aignet-copy-set-ins 0 aignet copy aignet2)))
    (mv copy aignet2))
  ///
  (def-aignet-preservation-thms aignet-copy-ins :stobjname aignet2)
  (defret stype-counts-presrved-of-<fn>
    (implies (not (equal (stype-fix stype) (pi-stype)))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret aignet-copy-size-of-<fn>
    (implies (<= (num-fanins aignet) (lits-length copy))
             (< (fanin-count aignet)
                (len new-copy)))
    :rule-classes :linear)

  (defret aignet-copy-len-of-<fn>
    (implies (<= (num-fanins aignet) (lits-length copy))
             (equal (len new-copy)
                    (len copy))))

  (defret aignet-copies-ok-of-aignet-copy-ins
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret num-ins-of-aignet-copy-ins
    (equal (stype-count (pi-stype) new-aignet2)
           (+ (nfix (stype-count (pi-stype) aignet))
              (stype-count (pi-stype) aignet2))))


  (defret lookup-copy-of-aignet-copy-ins
    (equal (nth-lit id new-copy)
           (if (or (not (equal (id->type id aignet) (in-type)))
                   (equal (id->regp id aignet) 1))
               (get-lit id copy)
             (mk-lit
              (fanin-count (lookup-stype (nfix (ci-id->ionum id aignet))
                                         (pi-stype) new-aignet2))
              0))))


  ;; (defret input-copy-values-of-aignet-copy-ins-nth
  ;;     (implies (equal (num-ins aignet2) 0)
  ;;              (bit-equiv (nth n (input-copy-values
  ;;                                 invals regvals new-aignet2 new-copy aignet))
  ;;                         (and (< (nfix n) (num-ins aignet))
  ;;                              (nth n invals)))))
;; :hints(("Goal" :in-theory (enable lit-eval id-eval))))

  (defret input-copy-values-of-aignet-copy-ins
    (bits-equiv (input-copy-values
                 0 invals regvals aignet new-copy new-aignet2)
                (take (num-ins aignet) invals))
    :hints (("goal" :in-theory (e/d (lit-eval
                                     nth-of-input-copy-values-split)
                                    (input-copy-values
                                     aignet-copy-ins
                                     bit->bool)))
            (and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                 `(:expand (,lit))))))

  ;; (defret reg-copy-values-of-aignet-copy-ins-nth
  ;;   (b* (((mv copy1 aignet21)
  ;;         (aignet-copy-ins aignet copy aignet2)))
  ;;     (implies (aignet-copies-in-bounds copy aignet2)
  ;;              (bit-equiv (nth n (reg-copy-values
  ;;                                 invals regvals aignet21 copy1 aignet))
  ;;                         (nth n (reg-copy-values
  ;;                                 invals regvals aignet2 copy aignet)))))
  ;;   :hints(("Goal" :expand ((:free (n copy aignet)
  ;;                            (lit-eval (nth-lit n copy)
  ;;                                      invals regvals aignet))
  ;;                           (:free (n copy aignet)
  ;;                            (id-eval (lit-id (nth-lit n copy))
  ;;                                      invals regvals aignet)))
  ;;           :in-theory (enable nth-of-reg-copy-values-split))))

  (defret reg-copy-values-of-aignet-copy-ins
    (implies (aignet-copies-in-bounds copy aignet2)
             (bits-equiv (reg-copy-values
                          0 invals regvals aignet new-copy new-aignet2)
                         (reg-copy-values
                          0 invals regvals aignet copy aignet2)))
    :hints (("goal" :in-theory (e/d (nth-of-reg-copy-values-split)
                                    (reg-copy-values
                                     aignet-copy-ins)))
            (and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   `(:expand (,lit)))))))

(define aignet-copy-regs (aignet copy aignet2)
  :guard (<= (num-fanins aignet) (lits-length copy))
  :returns (mv new-copy new-aignet2)
  (b* ((aignet2 (aignet-add-regs (num-regs aignet) aignet2))
       (copy (aignet-copy-set-regs 0 aignet copy aignet2)))
    (mv copy aignet2))
  ///
  (def-aignet-preservation-thms aignet-copy-regs :stobjname aignet2)
  (defret stype-counts-presrved-of-<fn>
    (implies (not (equal (stype-fix stype) (reg-stype)))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2))))

  (defret aignet-copy-size-of-<fn>
    (implies (<= (num-fanins aignet) (lits-length copy))
             (< (fanin-count aignet)
                (len new-copy)))
    :rule-classes :linear)

  (defret aignet-copy-len-of-<fn>
    (implies (<= (num-fanins aignet) (lits-length copy))
             (equal (len new-copy)
                    (len copy))))

  (defret aignet-copies-ok-of-aignet-copy-regs
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy new-aignet2)))

  (defret num-ins-of-aignet-copy-regs
    (equal (stype-count (reg-stype) new-aignet2)
           (+ (nfix (stype-count (reg-stype) aignet))
              (stype-count (reg-stype) aignet2))))


  (defret lookup-copy-of-aignet-copy-regs
    (equal (nth-lit id new-copy)
           (if (or (not (equal (id->type id aignet) (in-type)))
                   (equal (id->regp id aignet) 0))
               (get-lit id copy)
             (mk-lit
              (fanin-count (lookup-stype (nfix (ci-id->ionum id aignet))
                                         (reg-stype) new-aignet2))
              0))))


  ;; (defret input-copy-values-of-aignet-copy-regs-nth
  ;;     (implies (equal (num-ins aignet2) 0)
  ;;              (bit-equiv (nth n (input-copy-values
  ;;                                 invals regvals new-aignet2 new-copy aignet))
  ;;                         (and (< (nfix n) (num-ins aignet))
  ;;                              (nth n invals)))))
;; :hints(("Goal" :in-theory (enable lit-eval id-eval))))

  (defret reg-copy-values-of-aignet-copy-regs
    (bits-equiv (reg-copy-values
                 0 invals regvals aignet new-copy new-aignet2)
                (take (num-regs aignet) regvals))
    :hints (("goal" :in-theory (e/d (lit-eval
                                     nth-of-reg-copy-values-split)
                                    (reg-copy-values
                                     aignet-copy-regs
                                     bit->bool)))
            (and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                 `(:expand (,lit))))))

  ;; (defret reg-copy-values-of-aignet-copy-regs-nth
  ;;   (b* (((mv copy1 aignet21)
  ;;         (aignet-copy-regs aignet copy aignet2)))
  ;;     (implies (aignet-copies-in-bounds copy aignet2)
  ;;              (bit-equiv (nth n (reg-copy-values
  ;;                                 invals regvals aignet21 copy1 aignet))
  ;;                         (nth n (reg-copy-values
  ;;                                 invals regvals aignet2 copy aignet)))))
  ;;   :hints(("Goal" :expand ((:free (n copy aignet)
  ;;                            (lit-eval (nth-lit n copy)
  ;;                                      invals regvals aignet))
  ;;                           (:free (n copy aignet)
  ;;                            (id-eval (lit-id (nth-lit n copy))
  ;;                                      invals regvals aignet)))
  ;;           :in-theory (enable nth-of-reg-copy-values-split))))

  (defret input-copy-values-of-aignet-copy-regs
    (implies (aignet-copies-in-bounds copy aignet2)
             (bits-equiv (input-copy-values
                          0 invals regvals aignet new-copy new-aignet2)
                         (input-copy-values
                          0 invals regvals aignet copy aignet2)))
    :hints (("goal" :in-theory (e/d (nth-of-input-copy-values-split)
                                    (input-copy-values
                                     aignet-copy-regs)))
            (and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                 `(:expand (,lit))))))

  (defret input-copy-values-of-aignet-copy-regs-when-input-copies-in-bounds
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (bits-equiv (input-copy-values
                          0 invals regvals aignet new-copy new-aignet2)
                         (input-copy-values
                          0 invals regvals aignet copy aignet2)))
    :hints (("goal" :in-theory (e/d (nth-of-input-copy-values-split)
                                    (input-copy-values
                                     aignet-copy-regs)))
            (and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                 `(:expand (,lit)))))))





(defsection aignet-po-copies-in-bounds
  (defun-sk aignet-po-copies-in-bounds (copy aignet aignet2)
    (forall n
            (b* ((look (lookup-stype n :po aignet)))
              (implies (< (nfix n) (num-outs aignet))
                       (aignet-litp (nth-lit (lit-id (fanin 0 look)) copy) aignet2))))
    :rewrite :direct)

  (defthm aignet-po-copies-in-bounds-when-aignet-copies-in-bounds
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-po-copies-in-bounds copy aignet aignet2))) 

  (in-theory (disable aignet-po-copies-in-bounds))

  ;; (defthm lookup-po-in-bounds-by-aignet-po-copies-in-bounds
  ;;   (implies (and (aignet-po-copies-in-bounds copy aignet aignet2)
  ;;                 (< (nfix out) (num-outs aignet)))
  ;;            (aignet-litp (nth-lit (lit-id (fanin 0 (lookup-stype out :po aignet))) copy)
  ;;                         aignet2))
  ;;   :hints (("goal" :use ((:instance aignet-po-copies-in-bounds-necc
  ;;                          (n (fanin-count (lookup-stype out :po aignet)))))
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

(defsection aignet-copy-outs

  ;; Adds a aignet2 output for every output of aignet, using the stored copy
  ;; assumes the copy of each output ID is set to the fanin lit,
  ;; does not change this to the new node
  (defiteration aignet-copy-outs (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (and (<= (num-fanins aignet) (lits-length copy))
                                (ec-call (aignet-po-copies-in-bounds copy aignet aignet2)))))
    (b* ((fanin (lit-copy (outnum->fanin n aignet) copy)))
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
  ;;                 (fanin (nth-lit (fanin-count (lookup-stype m (po-stype) aignet))
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
    (implies (and (aignet-po-copies-in-bounds copy aignet aignet2)
                  (equal 0 (num-outs aignet2))
                  (< (nfix m) (nfix n))
                  (<= (nfix n) (num-outs aignet)))
             (b* ((aignet21 (aignet-copy-outs-iter n aignet copy aignet2))
                  (mth-out-look (lookup-stype m (po-stype) aignet21))
                  (fanin (lit-copy (fanin 0 (lookup-stype m (po-stype) aignet))
                                   copy)))
               (and ;; (consp mth-out-look)
                    (equal (fanin 0 mth-out-look) fanin)
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
    (implies (and (aignet-po-copies-in-bounds copy aignet aignet2)
                  (equal 0 (num-outs aignet2))
                  (< (nfix m) (num-outs aignet)))
             (b* ((aignet21 (aignet-copy-outs aignet copy aignet2))
                  (mth-out-look (lookup-stype m (po-stype) aignet21))
                  (fanin (lit-copy (fanin 0 (lookup-stype m (po-stype) aignet))
                                  copy)))
               (and ;; (consp mth-out-look)
                    (equal (fanin 0 mth-out-look) fanin)
                    ;; (equal (car mth-out-look)
                    ;;        (po-node fanin))
                    ;; (aignet-litp fanin (cdr mth-out-look))
                    ))))

  (fty::deffixequiv aignet-copy-outs-iter :args ((aignet aignet)))
  (fty::deffixequiv acl2::aignet-copy-outs$inline :args ((aignet aignet))))



(defsection aignet-nxst-copies-in-bounds
  (defun-sk aignet-nxst-copies-in-bounds (copy aignet aignet2)
    (forall n
            (b* ((look (lookup-reg->nxst n aignet)))
              (implies (< (nfix n) (num-regs aignet))
                       (aignet-litp (nth-lit (lit-id look) copy) aignet2))))
    :rewrite :direct)

  (defthm aignet-nxst-copies-in-bounds-when-aignet-copies-in-bounds
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-nxst-copies-in-bounds copy aignet aignet2))) 

  (in-theory (disable aignet-nxst-copies-in-bounds))

  ;; (defthm lookup-nxst-in-bounds-by-aignet-nxst-copies-in-bounds
  ;;   (implies (and (aignet-nxst-copies-in-bounds copy aignet aignet2)
  ;;                 (< (nfix out) (num-outs aignet)))
  ;;            (aignet-litp (nth-lit (lit-id (fanin 0 (lookup-stype out :nxst aignet))) copy)
  ;;                         aignet2))
  ;;   :hints (("goal" :use ((:instance aignet-nxst-copies-in-bounds-necc
  ;;                          (n (fanin-count (lookup-stype out :nxst aignet)))))
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

(defsection aignet-copy-nxsts


  ;; Adds a aignet2 regin for every register of aignet.
  ;; assumes the copy of each regin ID is set to the fanin lit,
  ;; does not change this to the new node.
  ;; Connects the regin to the corresponding reg in aignet2.  Therefore, we must
  ;; assume there are at least as many regs in aignet2 as in aignet.
  (defiteration aignet-copy-nxsts (aignet copy aignet2)
    (declare (xargs :stobjs (aignet copy aignet2)
                    :guard (and (<= (num-fanins aignet) (lits-length copy))
                                (<= (num-regs aignet) (num-regs aignet2))
                                (ec-call (aignet-nxst-copies-in-bounds copy aignet aignet2)))))
    (b* ((fanin (lit-copy (regnum->nxst n aignet) copy)))
      (aignet-set-nxst fanin n aignet2))
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

  (local (in-theory (enable aignet-extension-implies-fanin-count-gte
                            lookup-stype-in-bounds)))

  (defthm lookup-nxst-of-aignet-copy-nxsts-iter
    (implies (and (aignet-nxst-copies-in-bounds copy aignet aignet2)
                  (<= (nfix n) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2))
                  (< (nfix m) (nfix n))
                  ;; (aignet-extension-p aignet2 aignet2-orig)
                  )
             (b* ((aignet21 (aignet-copy-nxsts-iter n aignet copy aignet2))
                  (mth-nxst-look2 (lookup-reg->nxst m aignet21))
                  (mth-nxst-look (lookup-reg->nxst m aignet))
                  (fanin (lit-copy mth-nxst-look copy))
                  ;; (regid (fanin-count (lookup-stype m (reg-stype) aignet2)))
                  )
               (and ;; (consp mth-nxst-look2)
                (equal mth-nxst-look2 fanin)
                    ;; (equal (car mth-nxst-look2)
                    ;;        (nxst-node fanin regid))
                    ;; (aignet-litp fanin (cdr mth-nxst-look2))
                    ;; (aignet-idp regid (cdr mth-nxst-look2))
                    )))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (n a b) (lookup-reg->nxst n (Cons a b)))))))
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
    (implies (and (aignet-nxst-copies-in-bounds copy aignet aignet2)
                  (< (nfix m) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2))
                  ;; (aignet-extension-p aignet2 aignet2-orig)
                  )
             (b* ((aignet21 (aignet-copy-nxsts aignet copy aignet2))
                  ;; (regid (fanin-count (lookup-stype m (reg-stype) aignet2)))
                  (mth-nxst-look2 (lookup-reg->nxst m aignet21))
                  (mth-nxst-look (lookup-reg->nxst m aignet))
                  (fanin (lit-copy mth-nxst-look copy)))
               (and ;; (consp mth-nxst-look2)
                    ;; (equal (fanin 0 mth-nxst-look2) fanin)
                (equal  mth-nxst-look2 fanin)
                    ;; (equal (car mth-nxst-look2)
                    ;;        (nxst-node fanin regid))
                    ;; (aignet-litp fanin (cdr mth-nxst-look2))
                    ;; (aignet-idp regid (cdr mth-nxst-look2))
                    ))))

  (fty::deffixequiv aignet-copy-nxsts-iter :args ((aignet aignet)))
  (fty::deffixequiv aignet-copy-nxsts$inline :args ((aignet aignet))))



(defsection out-of-bounds-lookup-lemmas
  (defthmd fanin-count-lookup-stype-when-out-of-bounds
    (implies (<= (stype-count stype aignet) (nfix n))
             (equal (fanin-count (lookup-stype n stype aignet))
                    0))
    :hints(("Goal" :in-theory (enable lookup-stype fanin-count stype-count))))

  ;; (defthmd fanin-count-of-lookup-reg->nxst-0
  ;;   (equal (fanin-count (lookup-reg->nxst 0 aignet))
  ;;          0)
  ;;   :hints(("Goal" :in-theory (enable lookup-reg->nxst))))

  (defthmd lookup-reg->nxst-of-out-of-bounds-reg
    (implies (<= (stype-count :reg aignet) (nfix n))
             (equal (lookup-reg->nxst n aignet) 0))
    :hints(("Goal" :in-theory (enable lookup-reg->nxst stype-count))))
  )


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
                   (num-fanins aignet)
                   aignet2))
         (copy (resize-lits 0 copy))
         (strash (mbe :logic (non-exec '(nil))
                      :exec (strashtab-init (num-gates aignet) nil nil strash)))
         (copy (resize-lits (num-fanins aignet) copy))
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

    ;; (local (defthm id-eval-of-co-node
    ;;          (implies (equal (id->type id aignet) (out-type))
    ;;                   (equal (id-eval id invals regvals aignet)
    ;;                          (lit-eval (co-id->fanin id aignet)
    ;;                                    invals regvals aignet)))
    ;;          :hints(("Goal" :in-theory (enable id-eval)))))

    ;; (local (in-theory (enable co-node->fanin)))

    (defthm eval-output-of-aignet-complete-copy-aux
      (b* (((mv & & aignet2) (aignet-complete-copy-aux aignet copy gatesimp
                                                       strash aignet2)))
        (equal (lit-eval (fanin 0 (lookup-stype n (po-stype) aignet2))
                         invals regvals aignet2)
               (lit-eval (fanin 0 (lookup-stype n (po-stype) aignet))
                         invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-outs aignet)))
               :in-theory (enable fanin-count-lookup-stype-when-out-of-bounds)
               ;; :expand ((:free (x copy aignet)
               ;;           (lit-eval (lit-copy x copy) invals regvals aignet)))
               )))

    (defthm eval-nxst-of-aignet-complete-copy-aux
      (b* (((mv & & aignet2)
            (aignet-complete-copy-aux aignet copy gatesimp strash aignet2)))
        (equal (lit-eval (lookup-reg->nxst n aignet2)
                         invals regvals aignet2)
               (lit-eval (lookup-reg->nxst n aignet)
                         invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-regs aignet)))
               :in-theory (enable lookup-reg->nxst-of-out-of-bounds-reg))))

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
                                     (aignet-complete-copy-aux))))))

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
        (equal (lit-eval (fanin 0 (lookup-stype n (po-stype) aignet2))
                         invals regvals aignet2)
               (lit-eval (fanin 0 (lookup-stype n (po-stype) aignet))
                         invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-outs aignet)))
               :in-theory (enable fanin-count-lookup-stype-when-out-of-bounds))))

    (defthm eval-nxst-of-aignet-complete-copy
      (b* ((aignet2 (aignet-complete-copy aignet :gatesimp gatesimp)))
        (equal (lit-eval (lookup-reg->nxst n aignet2)
                         invals regvals aignet2)
               (lit-eval (lookup-reg->nxst n aignet)
                         invals regvals aignet)))
      :hints (("goal" :cases ((< (nfix n) (num-regs aignet)))
               :in-theory (enable lookup-reg->nxst-of-out-of-bounds-reg))))

    (defthm num-outs-of-aignet-complete-copy
      (equal (stype-count :po (aignet-complete-copy aignet :gatesimp gatesimp))
             (stype-count :po aignet)))

    (defthm num-regs-of-aignet-complete-copy
      (equal (stype-count :reg (aignet-complete-copy aignet :gatesimp gatesimp))
             (stype-count :reg aignet)))

    (defthm comb-equiv-of-aignet-complete-copy
      (comb-equiv (aignet-complete-copy aignet :gatesimp gatesimp)
                  aignet))))


(local (defthmd lits-equiv-redef
         (equal (lits-equiv x y)
                (let ((w (lits-equiv-witness x y)))
                  (equal (nth-lit w x) (nth-lit w y))))
         :hints(("Goal" :in-theory (enable lits-equiv lit-equiv nth-lit)))))

(define aignet-copy-set-regs-init ((n natp)
                                   aignet initsts copy aignet2)
  :guard (and (<= n (num-regs aignet))
              (<= (num-regs aignet) (num-regs aignet2))
              (<= (num-fanins aignet) (lits-length copy))
              (<= (num-regs aignet) (bits-length initsts)))
  :measure (nfix (- (num-regs aignet) (nfix n)))
  :returns new-copy
  (b* (((when (mbe :logic (zp (- (num-regs aignet) (nfix n)))
                   :exec (eql n (num-regs aignet))))
        copy)
       (copy (set-lit (regnum->id n aignet)
                      (make-lit (regnum->id n aignet2) (get-bit n initsts))
                      copy)))
    (aignet-copy-set-regs-init (1+ (lnfix n)) aignet initsts copy aignet2))
  ///
  (defret aignet-copy-size-of-<fn>
    (implies (<= (num-fanins aignet) (lits-length copy))
             (< (fanin-count aignet)
                (len new-copy)))
    :rule-classes :linear)

  (defret aignet-copies-ok-of-<fn>
    (implies (aignet-copies-in-bounds copy aignet2)
             (aignet-copies-in-bounds new-copy aignet2)))

  

  (defret lookup-copy-of-<fn>
    (equal (nth-lit id new-copy)
           (if (or (not (equal (id->type id aignet) (in-type)))
                   (not (equal (id->regp id aignet) 1))
                   (< (ci-id->ionum id aignet) (nfix n)))
               (get-lit id copy)
             (mk-lit
              (regnum->id (nfix (ci-id->ionum id aignet)) aignet2)
              (get-bit (ci-id->ionum id aignet) initsts))))
    :hints (("goal" :induct <call> :expand (<call>))))


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

  (defthm reg-copy-values-of-aignet-copy-set-regs-init
    (implies (<= (num-regs aignet) (num-regs aignet2))
             (bits-equiv (reg-copy-values
                          0 invals regvals aignet
                          (aignet-copy-set-regs-init 0 aignet initsts copy aignet2)
                          aignet2)
                         (take (num-regs aignet)
                               (b-xor-lst initsts regvals))))
    :hints (("goal" :in-theory (e/d (nth-of-reg-copy-values-split
                                     lit-eval)
                                    (reg-copy-values
                                     aignet-copy-set-regs-init))
             :do-not-induct t)
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defthm input-copy-values-of-aignet-copy-set-regs-init
    (bits-equiv (input-copy-values
                 0 invals regvals aignet
                 (aignet-copy-set-regs-init n aignet initsts copy aignet2)
                 aignet2)
                (input-copy-values
                 0 invals regvals aignet copy aignet2))
    :hints (("goal" :in-theory (e/d (nth-of-input-copy-values-split)
                                    (input-copy-values
                                     aignet-copy-set-regs-init)))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (local (defthm bit-equiv-of-nth-when-1-not-member
           (implies (not (member 1 x))
                    (bit-equiv (nth n x) 0))
           :hints(("Goal" :in-theory (enable nth)))))

  (defthm aignet-copy-set-regs-init-when-all-initsts-zero
    (implies (not (member 1 initsts))
             (equal (aignet-copy-set-regs-init n aignet initsts copy aignet2)
                    (aignet-copy-set-regs n aignet copy aignet2)))
    :hints(("Goal" :in-theory (e/d (aignet-copy-set-regs))))))

;; (defsection aignet-copy-regs-init

;;   ;; Adds a aignet2 reg for every reg of aignet, and sets the copy
;;   (defiteration aignet-copy-regs-init (aignet initsts copy aignet2)
;;     (declare (xargs :stobjs (aignet copy initsts aignet2)
;;                     :guard (and (<= (num-fanins aignet) (lits-length copy))
;;                                 (<= (num-regs aignet) (bits-length initsts)))))
;;     (b* ((ro (regnum->id n aignet))
;;          (inv (get-bit n initsts))
;;          (reglit (mk-lit (num-fanins aignet2) inv))
;;          (aignet2 (aignet-add-reg aignet2))
;;          (copy (set-lit ro reglit copy)))
;;       (mv copy aignet2))
;;     :returns (mv copy aignet2)
;;     :last (num-regs aignet)
;;     :index n
;;     :package aignet::bla)


;;   (in-theory (disable aignet-copy-regs-init))
;;   (local (in-theory (enable (:induction aignet-copy-regs-init-iter)
;;                             aignet-copy-regs-init)))

;;   (def-aignet-preservation-thms aignet-copy-regs-init-iter :stobjname aignet2)

;;   (local (set-default-hints
;;           '((acl2::just-induct-and-expand
;;              (aignet-copy-regs-init-iter n aignet initsts copy aignet2)
;;              :expand-others
;;              ((:free (aignet) (aignet-copy-regs-init-iter n aignet initsts copy aignet2))
;;               (:free (copy) (aignet-copy-regs-init-iter n aignet initsts copy aignet2))
;;               (:free (aignet2) (aignet-copy-regs-init-iter n aignet initsts copy
;;                                                       aignet2))))
;;             '(:do-not-induct t))))

;;   (defthm stype-counts-preserved-of-aignet-copy-regs-init-iter
;;     (implies (not (equal (stype-fix stype) (reg-stype)))
;;              (equal (stype-count stype (mv-nth 1 (aignet-copy-regs-init-iter
;;                                                   n aignet initsts copy aignet2)))
;;                     (stype-count stype aignet2))))

;;   (defthm aignet-copy-size-of-aignet-copy-regs-init-iter
;;     (implies (<= (num-fanins aignet) (lits-length copy))
;;              (< (fanin-count aignet)
;;                 (len (mv-nth 0 (aignet-copy-regs-init-iter n aignet initsts copy
;;                                                       aignet2)))))
;;     :rule-classes :linear)

;;   (defthm aignet-copies-ok-of-aignet-copy-regs-init-iter
;;     (implies (aignet-copies-in-bounds copy aignet2)
;;              (mv-let (copy aignet2)
;;                (aignet-copy-regs-init-iter n aignet initsts copy aignet2)
;;                (aignet-copies-in-bounds copy aignet2))))

;;   (local (defthmd dumb-num-regs-lemma
;;            (implies (<= n (stype-count (reg-stype) aignet))
;;                     (< (+ -1 n) (stype-count (reg-stype) aignet)))))

;;   (defthm num-regs-of-aignet-copy-regs-init-iter
;;     (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-regs-init-iter
;;                                                n aignet initsts copy aignet2)))
;;            (+ (nfix n)
;;               (stype-count (reg-stype) aignet2))))

;;   (defthm lookup-copy-of-aignet-copy-regs-init-iter
;;     (implies (and (<= (nfix n) (num-regs aignet)))
;;              (b* (((mv aignet-copy-new aignet2-new)
;;                    (aignet-copy-regs-init-iter n aignet initsts copy aignet2)))
;;                (equal (nth-lit id aignet-copy-new)
;;                       (if (or (not (equal (id->type id aignet) (in-type)))
;;                               (not (equal (id->regp id aignet) 1))
;;                               (<= (nfix n) (ci-id->ionum id aignet)))
;;                           (get-lit id copy)
;;                         (mk-lit
;;                          (regnum->id (+ (nfix (ci-id->ionum id aignet))
;;                                         (num-regs aignet2))
;;                                      aignet2-new)
;;                          (get-bit (ci-id->ionum id aignet) initsts))))))
;;     :hints ((and stable-under-simplificationp
;;                  '(:in-theory (enable satlink::equal-of-make-lit
;;                                       lookup-stype-in-bounds)
;;                    :expand ((:free (n stype a b)
;;                              (lookup-stype n stype (cons a b))))))))

;;   (local (set-default-hints nil))

;;   (def-aignet-preservation-thms aignet-copy-regs-init :stobjname aignet2)

;;   (defthm stype-counts-preserved-of-aignet-copy-regs-init
;;     (implies (not (equal (stype-fix stype) (reg-stype)))
;;              (equal (stype-count stype (mv-nth 1 (aignet-copy-regs-init
;;                                                   aignet initsts copy aignet2)))
;;                     (stype-count stype aignet2))))

;;   (defthm aignet-copy-size-of-aignet-copy-regs-init
;;     (implies (<= (num-fanins aignet) (lits-length copy))
;;              (< (fanin-count aignet)
;;                 (len (mv-nth 0 (aignet-copy-regs-init aignet initsts copy
;;                                                  aignet2)))))
;;     :rule-classes :linear)

;;   (defthm aignet-copies-ok-of-aignet-copy-regs-init
;;     (implies (aignet-copies-in-bounds copy aignet2)
;;              (mv-let (copy aignet2)
;;                (aignet-copy-regs-init aignet initsts copy aignet2)
;;                (aignet-copies-in-bounds copy aignet2))))

;;   (defthm num-regs-of-aignet-copy-regs-init
;;     (equal (stype-count (reg-stype) (mv-nth 1 (aignet-copy-regs-init
;;                                                aignet initsts copy aignet2)))
;;            (+ (nfix (num-regs aignet))
;;               (stype-count (reg-stype) aignet2))))

;;   (defthm lookup-copy-of-aignet-copy-regs-init
;;     (b* (((mv aignet-copy-new aignet2-new)
;;           (aignet-copy-regs-init aignet initsts copy aignet2)))
;;       (equal (nth-lit id aignet-copy-new)
;;              (if (or (not (equal (id->type id aignet) (in-type)))
;;                      (not (equal (id->regp id aignet) 1)))
;;                  (get-lit id copy)
;;                (mk-lit
;;                 (regnum->id (+ (nfix (ci-id->ionum id aignet))
;;                                (num-regs aignet2))
;;                             aignet2-new)
;;                 (get-bit (ci-id->ionum id aignet) initsts))))))

;;   (defthm reg-copy-values-of-aignet-copy-regs-init-nth
;;     (b* (((mv copy1 aignet21)
;;           (aignet-copy-regs-init aignet initsts copy aignet2)))
;;       (implies (equal (num-regs aignet2) 0)
;;                (bit-equiv (nth n (reg-copy-values
;;                                   0 invals regvals aignet copy1 aignet21))
;;                           (and (< (nfix n) (num-regs aignet))
;;                                (b-xor (get-bit n initsts)
;;                                       (nth n regvals))))))
;;     :hints(("Goal" :in-theory (enable lit-eval id-eval))))


;;   ;; (defthm len-of-b-xor-lst-1
;;   ;;   (<= (len a) (len (b-xor-lst a b)))
;;   ;;   :rule-classes :linear)
;;   ;; (defthm len-of-b-xor-lst-2
;;   ;;   (<= (len b) (len (b-xor-lst a b)))
;;   ;;   :rule-classes :linear)

;;   (defthm reg-copy-values-of-aignet-copy-regs-init
;;     (b* (((mv copy1 aignet21)
;;           (aignet-copy-regs-init aignet initsts copy aignet2)))
;;       (implies (equal (num-regs aignet2) 0)
;;                (bits-equiv (reg-copy-values
;;                             0 invals regvals aignet copy1 aignet21)
;;                            (take (num-regs aignet)
;;                                  (b-xor-lst initsts regvals)))))
;;     :hints (("goal" :in-theory (disable reg-copy-values
;;                                         aignet-copy-regs-init))
;;             (and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))))

;;   (defthm input-copy-values-of-aignet-copy-regs-init-nth
;;     (b* (((mv copy1 aignet21)
;;           (aignet-copy-regs-init aignet initsts copy aignet2)))
;;       (implies (aignet-copies-in-bounds copy aignet2)
;;                (bit-equiv (nth n (input-copy-values
;;                                   0 invals regvals aignet copy1 aignet21))
;;                           (nth n (input-copy-values
;;                                   0 invals regvals aignet copy aignet2)))))
;;     :hints(("Goal" :expand ((:free (n copy aignet)
;;                              (lit-eval (nth-lit n copy)
;;                                        invals regvals aignet))
;;                             (:free (n copy aignet)
;;                              (id-eval (lit-id (nth-lit n copy))
;;                                       invals regvals aignet)))
;;             :in-theory (enable nth-of-input-copy-values-split))))

;;   (defthm input-copy-values-of-aignet-copy-regs-init
;;     (b* (((mv copy1 aignet21)
;;           (aignet-copy-regs-init aignet initsts copy aignet2)))
;;       (implies (aignet-copies-in-bounds copy aignet2)
;;                (bits-equiv (input-copy-values
;;                             0 invals regvals aignet copy1 aignet21)
;;                            (input-copy-values
;;                             0 invals regvals aignet copy aignet2))))
;;     :hints (("goal" :in-theory (disable input-copy-values
;;                                         aignet-copy-regs-init))
;;             (and stable-under-simplificationp
;;                  `(:expand (,(car (last clause)))))))

;;   (local (defthm bit-equiv-of-nth-when-1-not-member
;;            (implies (not (member 1 x))
;;                     (bit-equiv (nth n x) 0))
;;            :hints(("Goal" :in-theory (enable nth)))))

;;   ;; (defthm aignet-copy-regs-init-iter-when-all-initsts-zero
;;   ;;   (implies (not (member 1 initsts))
;;   ;;            (equal (aignet-copy-regs-init-iter n aignet initsts copy aignet2)
;;   ;;                   (aignet-copy-regs-iter n aignet copy aignet2)))
;;   ;;   :hints(("Goal" :in-theory (enable aignet-copy-regs-iter aignet-copy-regs-init-iter))))

;;   (defthm aignet-copy-regs-init-iter-is-aignet-add-regs
;;     (node-list-equiv (mv-nth 1 (aignet-copy-regs-init-iter n aignet initsts copy aignet2))
;;                      (aignet-add-regs n aignet2))
;;     :hints(("Goal" :in-theory (enable aignet-copy-regs-init-iter)
;;             :induct (aignet-copy-regs-init-iter n aignet initsts copy aignet2)
;;             :expand ((aignet-add-regs n aignet2)
;;                      (aignet-add-regs 0 aignet2)))))

;;   (defthm aignet-copy-regs-init-when-all-initsts-zero
;;     (implies (and (not (member 1 initsts))
;;                   (equal 0 (num-regs aignet2)))
;;              (lits-equiv (mv-nth 0 (aignet-copy-regs-init aignet initsts copy aignet2))
;;                          (aignet-copy-set-regs 0 aignet copy (aignet-add-regs (num-regs aignet) aignet2))))
;;     :hints(("Goal" :in-theory (e/d (lits-equiv-redef)
;;                                    (aignet-copy-regs-init))
;;             :do-not-induct t))) ;;  aignet-copy-regs aignet-copy-regs-init))))
;;   )


(defsection aignet-copy-nxsts-init


  ;; Adds a aignet2 regin for every register of aignet.
  ;; assumes the copy of each regin ID is set to the fanin lit,
  ;; does not change this to the new node.
  ;; Connects the regin to the corresponding reg in aignet2.  Therefore, we must
  ;; assume there are at least as many regs in aignet2 as in aignet.
  (defiteration aignet-copy-nxsts-init (aignet initsts copy aignet2)
    (declare (xargs :stobjs (aignet initsts copy aignet2)
                    :guard (and (<= (num-fanins aignet) (lits-length copy))
                                (<= (num-regs aignet) (num-regs aignet2))
                                (<= (num-regs aignet) (bits-length initsts))
                                (ec-call (aignet-nxst-copies-in-bounds copy aignet aignet2)))))
    (b* ((nxst (regnum->nxst n aignet))
         (inv (get-bit n initsts))
         (fanin-copy (lit-negate-cond (lit-copy nxst copy) inv)))
      (aignet-set-nxst fanin-copy n aignet2))
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

  (local (in-theory (enable aignet-extension-implies-fanin-count-gte
                            lookup-stype-in-bounds)))

  (defthm lookup-nxst-of-aignet-copy-nxsts-init-iter
    (implies (and (aignet-nxst-copies-in-bounds copy aignet aignet2)
                  (<= (nfix n) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2))
                  (< (nfix m) (nfix n)))
             (b* ((aignet21 (aignet-copy-nxsts-init-iter n aignet initsts copy aignet2))
                  (mth-nxst-look2 (lookup-reg->nxst m aignet21))
                  (mth-nxst-look (lookup-reg->nxst m aignet))
                  (fanin (lit-copy mth-nxst-look copy)))
               (equal mth-nxst-look2
                      (lit-negate-cond fanin (get-bit m initsts)))))
    :hints ((and stable-under-simplificationp
                 '(:expand ((:free (n a b)
                             (lookup-reg->nxst n (cons a b))))))))

  (local (set-default-hints nil))

  (def-aignet-preservation-thms aignet-copy-nxsts-init :stobjname aignet2)

  (defthm stype-counts-preserved-of-aignet-copy-nxsts-init
    (implies (not (equal (stype-fix stype) (nxst-stype)))
             (equal (stype-count stype
                                 (aignet-copy-nxsts-init aignet initsts copy aignet2))
                    (stype-count stype aignet2))))

  (defthm lookup-nxst-of-aignet-copy-nxsts-init
    (implies (and (aignet-nxst-copies-in-bounds copy aignet aignet2)
                  (< (nfix m) (num-regs aignet))
                  (<= (num-regs aignet) (num-regs aignet2)))
             (b* ((aignet21 (aignet-copy-nxsts-init aignet initsts copy aignet2))
                  (mth-nxst-look2 (lookup-reg->nxst m aignet21))
                  (mth-nxst-look (lookup-reg->nxst m aignet))
                  (fanin (lit-copy mth-nxst-look copy)))
               (equal mth-nxst-look2
                      (lit-negate-cond fanin (get-bit m initsts))))))

  (local (defthm bit-equiv-of-nth-when-1-not-member
           (implies (not (member 1 x))
                    (bit-equiv (nth n x) 0))
           :hints(("Goal" :in-theory (enable nth)))))

  (local (defthm lit-negate-cond-0
           (lit-equiv (lit-negate-cond lit 0) lit)
           :hints(("Goal" :in-theory (enable lit-negate-cond)))))

  (defthm aignet-copy-nxsts-init-iter-when-all-initsts-zero
    (implies (not (member 1 initsts))
             (equal (aignet-copy-nxsts-init-iter n aignet initsts copy aignet2)
                    (aignet-copy-nxsts-iter n aignet copy aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-nxsts-iter aignet-copy-nxsts-init-iter))))

  (defthm aignet-copy-nxsts-init-when-all-initsts-zero
    (implies (not (member 1 initsts))
             (equal (aignet-copy-nxsts-init aignet initsts copy aignet2)
                    (aignet-copy-nxsts aignet copy aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-nxsts aignet-copy-nxsts-init)))))

(defsection aignet-copy-init
  :parents (aignet)
  :short "Set the initial state of an FSM to the all-0 convention."

  :long "<p>Some algorithms assume that an FSM's initial state is the one where
all registers are 0.  This normalizes an FSM that does not follow this
convention into one that does.  Given the aignet and an initial state vector,
this produces a new aignet that has registers toggled so that when its initial
value is 0, its sequential simulations produce the same values as the input
aignet when its initial value is the specified vector:</p>

@(def lit-eval-seq-of-aignet-copy-init)

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
                   (num-fanins aignet)
                   aignet2))
         (copy (resize-lits 0 copy))
         (strash (mbe :logic (non-exec '(nil))
                      :exec (strashtab-init (num-gates aignet) nil nil strash)))
         (copy (resize-lits (num-fanins aignet) copy))
         ((mv copy aignet2)
          (aignet-copy-ins aignet copy aignet2))
         (aignet2 (aignet-add-regs (num-regs aignet) aignet2))
         (copy
          (aignet-copy-set-regs-init 0 aignet initsts copy aignet2))
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

    ;; (local (defthm id-eval-of-co-node
    ;;          (implies (equal (id->type id aignet) (out-type))
    ;;                   (equal (id-eval id invals regvals aignet)
    ;;                          (lit-eval (co-id->fanin id aignet)
    ;;                                    invals regvals aignet)))
    ;;          :hints(("Goal" :in-theory (enable id-eval)))))

    ;; (local (in-theory (enable co-node->fanin)))


    (defthm eval-output-of-aignet-copy-init-aux
      (implies (< (nfix n) (num-outs aignet))
               (b* (((mv & & aignet2) (aignet-copy-init-aux aignet initsts copy gatesimp
                                                            strash aignet2)))
                 (equal (lit-eval (fanin 0 (lookup-stype n (po-stype) aignet2))
                                  invals regvals aignet2)
                        (lit-eval (fanin 0 (lookup-stype n (po-stype) aignet))
                                  invals
                                  (b-xor-lst initsts regvals)
                                  aignet))
                 ;; (equal (id-eval
                 ;;         (fanin-count (lookup-stype n (po-stype) aignet2))
                 ;;         invals regvals aignet2)
                 ;;        (id-eval
                 ;;         (fanin-count (lookup-stype n (po-stype) aignet))
                 ;;         invals
                 ;;         (b-xor-lst initsts regvals) aignet))
                 )))

    (defthm eval-nxst-of-aignet-copy-init-aux
      (implies (< (nfix n) (num-regs aignet))
               (b* (((mv & & aignet2)
                     (aignet-copy-init-aux aignet initsts copy gatesimp strash aignet2)))
                 (equal (lit-eval (lookup-reg->nxst n aignet2)
                                  invals regvals aignet2)
                        (b-xor (nth n initsts)
                               (lit-eval (lookup-reg->nxst n aignet)
                                         invals
                                         (b-xor-lst initsts regvals) aignet))))))

    (fty::deffixequiv aignet-copy-init-aux :args ((gatesimp gatesimp-p)))

    (defthm aignet-copy-init-aux-when-all-initsts-0
      (implies (not (member 1 initsts))
               (equal (aignet-copy-init-aux aignet initsts copy gatesimp strash aignet2)
                      (aignet-complete-copy-aux aignet copy gatesimp strash aignet2)))
      :hints(("Goal" :in-theory (enable aignet-complete-copy-aux
                                        aignet-copy-regs)
              :do-not-induct t))))

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
                 (equal (lit-eval (fanin 0 (lookup-stype n (po-stype) aignet2))
                                  invals regvals aignet2)
                        (lit-eval (fanin 0 (lookup-stype n (po-stype) aignet))
                                  invals
                                  (b-xor-lst initsts regvals)
                                  aignet)))))

    (defthm eval-nxst-of-aignet-copy-init
      (implies (< (nfix n) (num-regs aignet))
               (b* ((aignet2 (aignet-copy-init aignet initsts :gatesimp gatesimp)))
                 (equal (lit-eval (lookup-reg->nxst n aignet2)
                                  invals regvals aignet2)
                        (b-xor (nth n initsts)
                               (lit-eval (lookup-reg->nxst n aignet)
                                         invals
                                         (b-xor-lst initsts regvals) aignet))))))

    (defthm aignet-copy-init-when-all-initsts-0
      (implies (not (member 1 initsts))
               (equal (aignet-copy-init aignet initsts :gatesimp gatesimp)
                      (aignet-complete-copy aignet :gatesimp gatesimp)))
      :hints(("Goal" :in-theory (enable aignet-complete-copy)))))

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
           (equal (lit-eval lit ins
                           (b-xor-lst x (take (stype-count :reg aignet) y))
                           aignet)
                  (lit-eval lit ins
                            (b-xor-lst x y) aignet))
           :hints (("goal" :use ((:instance lit-eval-of-take-num-regs
                                  (invals ins)
                                  (n (num-regs aignet))
                                  (regvals
                                   (b-xor-lst x (take (stype-count :reg aignet) y)))))
                    :do-not-induct t))))


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
                  :in-theory (enable lit-eval-seq-in-terms-of-lit-eval
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

  ;; (defthm id-eval-seq-of-aignet-copy-init
  ;;   (b* ((aignet2 (aignet-copy-init aignet initsts :gatesimp gatesimp)))
  ;;     (equal (id-eval-seq k (fanin 0 (lookup-stype n :po aignet2))
  ;;                         frames nil aignet2)
  ;;            (id-eval-seq k (fanin 0 (lookup-stype n :po aignet))
  ;;                         frames initsts aignet)))
  ;;   :hints(("Goal" :in-theory (enable id-eval-seq-in-terms-of-id-eval)
  ;;           :cases ((< (nfix n) (num-outs aignet))))))

  (defthm lit-eval-seq-of-aignet-copy-init
    (b* ((aignet2 (aignet-copy-init aignet initsts :gatesimp gatesimp)))
      (equal (lit-eval-seq k (fanin 0 (lookup-stype n :po aignet2))
                          frames nil aignet2)
             (lit-eval-seq k (fanin 0 (lookup-stype n :po aignet))
                           frames initsts aignet)))
    :hints(("Goal" :in-theory (enable lit-eval-seq-in-terms-of-lit-eval)
            :cases ((< (nfix n) (num-outs aignet))))))

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
                           (n (aignet-marked-copies-in-bounds-witness . ,(cdr lit))))))))))

  (defthm aignet-lit-listp-of-lit-list-copies-when-marked
    (implies (and (aignet-marked-copies-in-bounds copy mark aignet)
                  (lit-list-marked lits mark))
             (aignet-lit-listp (lit-list-copies lits copy) aignet))
    :hints(("Goal" :in-theory (enable lit-list-copies lit-list-marked)))))


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

(encapsulate nil
  (local (in-theory (disable lookup-id-out-of-bounds)))

  (local (defthm ctype-is-input-fwd
           (implies (equal (ctype (stype x)) :input)
                    (or (equal (stype x) :pi)
                        (equal (stype x) :reg)))
           :hints(("Goal" :in-theory (enable ctype)))
           :rule-classes :forward-chaining))

  (local (defthm input-ctype-of-extension-when-stype-counts-preserved
           (implies (and (aignet-extension-binding)
                         (equal (stype-count :pi new) (stype-count :pi orig))
                         (equal (stype-count :reg new) (stype-count :reg orig)))
                    (equal (equal (ctype (stype (car (lookup-id id new)))) :input)
                           (equal (ctype (stype (car (lookup-id id orig)))) :input)))
           :hints(("Goal" :in-theory (enable ;; aignet-extension-p
                                      lookup-id)
                   :expand ((stype-count :pi new)
                            (stype-count :reg new)
                            (aignet-extension-p new orig))
                   :induct (lookup-id id new)))))

  (defthm aignet-input-copies-in-bounds-of-extension-1
    (implies (and (aignet-extension-binding)
                  (equal (stype-count :pi new) (stype-count :pi orig))
                  (equal (stype-count :reg new) (stype-count :reg orig)))
             (iff (aignet-input-copies-in-bounds copy new aignet2)
                  (aignet-input-copies-in-bounds copy orig aignet2)))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(assoc 'aignet-input-copies-in-bounds clause))))))

  (defthm aignet-input-copies-in-bounds-of-extension-2
    (implies (and (aignet-extension-binding)
                  (aignet-input-copies-in-bounds copy aignet orig))
             (aignet-input-copies-in-bounds copy aignet new))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(assoc 'aignet-input-copies-in-bounds clause)))))))

;; (local (defthm lookup-id-of-aignet-id-fix
;;          (equal (lookup-id (aignet-id-fix id aignet) aignet)
;;                 (lookup-id id aignet))
;;          :hints(("Goal" :in-theory (enable aignet-id-fix)))))


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
                      (aignet-copy-dfs-rec id-equiv aignet mark
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

  

  (defret stype-counts-preserved-of-aignet-copy-dfs-rec
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand <call>)))

  ;; (defthm id-in-bounds-when-memo-tablep-bind-free
  ;;   (implies (and (bind-free '((aignet . aignet)) (aignet))
  ;;                 (< (fanin-count aignet) (len arr))
  ;;                 (double-rewrite (aignet-idp n aignet)))
  ;;            (id-in-bounds n arr)))

  ;; (defthm aignet-copies-ok-implies-special-bind-free
  ;;   (implies (and (bind-free '((aignet1 . aignet)) (aignet1))
  ;;                 (aignet-copies-in-bounds copy aignet)
  ;;                 (aignet-idp k aignet1))
  ;;            (aignet-litp (nth-lit k copy) aignet)))

  (local (in-theory (enable lit-negate-cond)))

  (defret aignet-input-copies-in-bounds-of-aignet-copy-dfs-rec
    (implies (and ;; (aignet-idp id aignet)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-input-copies-in-bounds new-copy aignet new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))

  (local (defthm input-when-not-gate-or-const
           (or (equal (stype (car (lookup-id id aignet))) :const)
               (equal (ctype (stype (car (lookup-id id aignet)))) :gate)
               (equal (ctype (stype (car (lookup-id id aignet)))) :input))
           :hints(("Goal" :in-theory (enable ctype)))
           :rule-classes ((:forward-chaining :trigger-terms ((stype (car (lookup-id id aignet))))))))

  (defret aignet-marked-copies-in-bounds-of-aignet-copy-dfs-rec
    (implies (and ;; (aignet-idp id aignet)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-marked-copies-in-bounds new-copy new-mark new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))


  (defret aignet-copies-in-bounds-of-aignet-copy-dfs-rec
    (implies (and ;; (aignet-idp id aignet)
                  (aignet-copies-in-bounds copy aignet2))
             (aignet-copies-in-bounds new-copy new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-input-copies-in-bounds-of-aignet-copy-dfs-rec-rw
    (implies (and ;; (aignet-idp id aignet)
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
    (implies (and ;; (aignet-idp id aignet)
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
    :hints((and stable-under-simplificationp
                '(:in-theory (enable aignet-idp)))))


  (defthm input-copy-values-of-aignet-copy-dfs-rec
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (b* (((mv ?new-mark ?new-copy ?new-strash ?new-aignet2)
                   (aignet-copy-dfs-rec id aignet mark copy strash gatesimp aignet2)))
               (equal (input-copy-values n invals regvals aignet new-copy new-aignet2)
                      (input-copy-values n invals regvals aignet copy aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-rec
              id aignet mark copy
              strash gatesimp aignet2))))

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
            (implies (and ;; (aignet-idp id aignet)
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
                         ;; (aignet-idp id aignet)
                         (equal 1 (get-bit id mark)))
                    (equal (id-eval (lit->var (nth-lit id copy)) invals regvals aignet2)
                           (b-xor (lit->neg (nth-lit id copy))
                                  (id-eval id
                                           (input-copy-values 0 invals regvals aignet copy aignet2)
                                           (reg-copy-values 0 invals regvals aignet copy aignet2)
                                           aignet))))
           :hints (("goal" :use dfs-copy-onto-invar-necc
                    :in-theory (e/d (lit-eval) (dfs-copy-onto-invar-necc))))))

  (local (defthm dfs-copy-onto-invar-implies-eval-lit-copy
           (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                         ;; (aignet-idp id aignet)
                         (equal 1 (get-bit (lit->var lit) mark)))
                    (equal (lit-eval (lit-copy lit copy) invals regvals aignet2)
                           (lit-eval lit
                                     (input-copy-values 0 invals regvals aignet copy aignet2)
                                     (reg-copy-values 0 invals regvals aignet copy aignet2)
                                     aignet)))
           :hints (("goal" :use ((:instance dfs-copy-onto-invar-necc
                                  (id (lit->var lit))))
                    :in-theory (e/d (lit-eval lit-copy) (dfs-copy-onto-invar-necc))))))

  ;; (local (defthm input-when-not-gate-or-const
  ;;          (or (equal (stype (car (lookup-id id aignet))) :const)
  ;;              (equal (ctype (stype (car (lookup-id id aignet)))) :gate)
  ;;              (equal (ctype (stype (car (lookup-id id aignet)))) :input))
  ;;          :hints(("Goal" :in-theory (enable ctype)))
  ;;          :rule-classes ((:forward-chaining :trigger-terms ((stype (car (lookup-id id aignet))))))))
  
  (local (include-book "std/util/termhints" :dir :system))

  (defthm dfs-copy-onto-invar-holds-of-aignet-copy-dfs-rec
    (implies (and ;; (aignet-idp id aignet)
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
            (and stable-under-simplificationp
                 (acl2::use-termhint
                  (acl2::termhint-seq
                   `(:expand ((:free (invals regvals) (id-eval id invals regvals aignet)))
                                   :in-theory (enable eval-xor-of-lits
                                                      eval-and-of-lits))
                   (b* ((suff (lookup-id id aignet)))
                     (case (stype (car suff))
                       (:and (b* ((f0 (fanin 0 suff))
                                  ((mv mark1 copy1 & aignet21)
                                   (aignet-copy-dfs-rec (lit->var f0) aignet mark copy strash gatesimp aignet2)))
                               (and (equal (lit-copy f0 copy1) 0)
                                    `(:use ((:instance dfs-copy-onto-invar-implies-eval-lit-copy
                                             (lit ,(acl2::hq f0))
                                             (mark ,(acl2::hq mark1))
                                             (copy ,(acl2::hq copy1))
                                             (aignet2 ,(acl2::hq aignet21))))
                                      :in-theory (disable dfs-copy-onto-invar-implies-eval-lit-copy)))))
                       (:pi `(:use ((:instance acl2::mark-clause-is-true (x :pi)))))
                       (:reg `(:use ((:instance acl2::mark-clause-is-true (x :reg)))))
                       (:xor `(:use ((:instance acl2::mark-clause-is-true (x :xor)))))
                       (:const `(:use ((:instance acl2::mark-clause-is-true (x :const))))))))))))
  

  (defthm lit-eval-of-aignet-copy-dfs-rec
    (implies (and ;; (aignet-idp id aignet)
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
             :in-theory (disable dfs-copy-onto-invar-holds-of-aignet-copy-dfs-rec))))

  (defthm lit-eval-lit-copy-of-aignet-copy-dfs-rec
    (implies (and ;; (aignet-idp id aignet)
                  (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2))
             (b* (((mv ?mark copy ?strash aignet2)
                   (aignet-copy-dfs-rec
                    (lit->var lit) aignet mark copy
                    strash gatesimp aignet2)))
               (equal (lit-eval (lit-copy lit copy) invals regvals aignet2)
                      (lit-eval lit
                                (input-copy-values 0 invals regvals aignet copy aignet2)
                                (reg-copy-values 0 invals regvals aignet copy aignet2)
                                aignet))))
    :hints (("goal" :use ((:instance dfs-copy-onto-invar-holds-of-aignet-copy-dfs-rec (id (lit->var lit))))
             :in-theory (disable dfs-copy-onto-invar-holds-of-aignet-copy-dfs-rec))))

  (defthm lit-eval-list-of-copies-when-dfs-copy-onto-invar
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (lit-list-marked lits mark))
             (equal (lit-eval-list (lit-list-copies lits copy) invals regvals aignet2)
                    (lit-eval-list lits
                                   (input-copy-values 0 invals regvals aignet copy aignet2)
                                   (reg-copy-values 0 invals regvals aignet copy aignet2)
                                   aignet)))
    :hints(("Goal" :in-theory (enable lit-list-copies lit-eval-list lit-copy lit-list-marked)
            :expand ((:free (invals regvals) (lit-eval (car lits) invals regvals aignet))))))

  (local (defun nth-of-repeat-ind (n m)
           (if (zp n)
               m
             (nth-of-repeat-ind (1- n) (1- m)))))
  (local (defthmd nth-of-repeat-split
           (equal (nth n (acl2::repeat m x))
                  (and (< (nfix n) (nfix m))
                       x) )
           :hints(("Goal" :in-theory (enable nth acl2::repeat)
                   :induct (nth-of-repeat-ind n m)))))

  (defthm dfs-copy-onto-invar-of-empty-marks
    (dfs-copy-onto-invar aignet (acl2::repeat n 0) copy aignet2)
    :hints(("Goal" :in-theory (enable dfs-copy-onto-invar
                                      nth-of-repeat-split)))))



(define aignet-copy-dfs-list ((lits lit-listp)
                              aignet
                              mark
                              copy
                              strash
                              (gatesimp gatesimp-p)
                              aignet2)
  :guard (and (aignet-lit-listp lits aignet)
              (<= (num-fanins aignet) (bits-length mark))
              (<= (num-fanins aignet) (lits-length copy))
              (ec-call (aignet-marked-copies-in-bounds copy mark aignet2))
              (ec-call (aignet-input-copies-in-bounds copy aignet aignet2)))
  :returns (mv new-mark new-copy new-strash new-aignet2)
  :verify-guards nil
  (if (atom lits)
      (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                         :exec aignet2)))
        (mv mark copy strash aignet2))
    (b* (((mv mark copy strash aignet2)
          (aignet-copy-dfs-rec (lit->var (car lits)) aignet mark copy strash gatesimp aignet2)))
      (aignet-copy-dfs-list (cdr lits) aignet mark copy strash gatesimp aignet2)))
  ///
  
  (def-aignet-preservation-thms aignet-copy-dfs-list :stobjname aignet2)

  (defret mark-preserved-of-aignet-copy-dfs-list
    (implies (equal 1 (nth n mark))
             (equal (nth n new-mark) 1))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret mark-set-of-aignet-copy-dfs-list
    (implies (member-equal (lit-fix lit) (lit-list-fix lits))
             (equal (nth (lit->var lit) new-mark) 1))
    :hints (("goal" :expand (<call>))))


  (local (defthm member-lit-fix
           (implies (member k x)
                    (member-equal (lit-fix k) (lit-list-fix x)))))

  (local (defthm member-nth
           (implies (< (nfix n) (len x))
                    (member-equal (nth n x) x))
           :hints(("Goal" :in-theory (enable nth)))))

  (defret nth-lit-mark-set-of-<fn>
    (implies (< (nfix n) (len lits))
             (equal (nth (lit->var (nth n lits)) new-mark) 1)))

  (defret copies-sized-of-aignet-copy-dfs-list
    (<= (len copy)
        (len new-copy))
    :hints ((acl2::just-induct-and-expand <call>))
    :rule-classes :linear)

  (defret mark-sized-of-aignet-copy-dfs-list
    (<= (len mark)
        (len new-mark))
    :hints ((acl2::just-induct-and-expand <call>))
    :rule-classes :linear)


  (defret copy-length-of-<fn>
    (implies (< (lits-max-id-val lits) (len copy))
             (equal (len new-copy) (len copy))))

  (defret mark-length-of-<fn>
    (implies (< (lits-max-id-val lits) (len mark))
             (equal (len new-mark) (len mark))))

  (defret stype-counts-preserved-of-aignet-copy-dfs-list
    (implies (and (not (equal (stype-fix stype) (and-stype)))
                  (not (equal (stype-fix stype) (xor-stype))))
             (equal (stype-count stype new-aignet2)
                    (stype-count stype aignet2)))
    :hints ((acl2::just-induct-and-expand <call>)))

  ;; (defthm id-in-bounds-when-memo-tablep-bind-free
  ;;   (implies (and (bind-free '((aignet . aignet)) (aignet))
  ;;                 (< (fanin-count aignet) (len arr))
  ;;                 (double-rewrite (aignet-idp n aignet)))
  ;;            (id-in-bounds n arr)))

  ;; (defthm aignet-copies-ok-implies-special-bind-free
  ;;   (implies (and (bind-free '((aignet1 . aignet)) (aignet1))
  ;;                 (aignet-copies-in-bounds copy aignet)
  ;;                 (aignet-idp k aignet1))
  ;;            (aignet-litp (nth-lit k copy) aignet)))

  (local (in-theory (enable lit-negate-cond)))

  (defret aignet-input-copies-in-bounds-of-aignet-copy-dfs-list
    (implies (and ;; (aignet-idp id aignet)
              (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-input-copies-in-bounds new-copy aignet new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))

  (local (defthm input-when-not-gate-or-const
           (or (equal (stype (car (lookup-id id aignet))) :const)
               (equal (ctype (stype (car (lookup-id id aignet)))) :gate)
               (equal (ctype (stype (car (lookup-id id aignet)))) :input))
           :hints(("Goal" :in-theory (enable ctype)))
           :rule-classes ((:forward-chaining :trigger-terms ((stype (car (lookup-id id aignet))))))))

  (defret aignet-marked-copies-in-bounds-of-aignet-copy-dfs-list
    (implies (and ;; (aignet-idp id aignet)
              (aignet-marked-copies-in-bounds copy mark aignet2)
              (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-marked-copies-in-bounds new-copy new-mark new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))


  (defret aignet-copies-in-bounds-of-aignet-copy-dfs-list
    (implies (and ;; (aignet-idp id aignet)
              (aignet-copies-in-bounds copy aignet2))
             (aignet-copies-in-bounds new-copy new-aignet2))
    :hints ((acl2::just-induct-and-expand <call>)))

  (defret aignet-input-copies-in-bounds-of-aignet-copy-dfs-list-rw
    (implies (and ;; (aignet-idp id aignet)
              (equal (id->type n aignet) (in-type))
              (aignet-input-copies-in-bounds copy aignet aignet2))
             (aignet-litp (nth-lit n new-copy) new-aignet2))
    :hints (("goal" :use ((:instance aignet-input-copies-in-bounds-necc
                           (aignet2 new-aignet2)
                           (copy new-copy)
                           (n n)))
             :in-theory (e/d ()
                             (aignet-input-copies-in-bounds-necc
                              aignet-copy-dfs-list)))))

  (defret aignet-marked-copies-in-bounds-of-aignet-copy-dfs-list-rw
    (implies (and ;; (aignet-idp id aignet)
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
                              aignet-copy-dfs-list)))))

  (verify-guards aignet-copy-dfs-list
    :hints((and stable-under-simplificationp
                '(:in-theory (enable aignet-idp)))))


  (defthm input-copy-values-of-aignet-copy-dfs-list
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (b* (((mv ?new-mark ?new-copy ?new-strash ?new-aignet2)
                   (aignet-copy-dfs-list lits aignet mark copy strash gatesimp aignet2)))
               (equal (input-copy-values n invals regvals aignet new-copy new-aignet2)
                      (input-copy-values n invals regvals aignet copy aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-list
              lits aignet mark copy
              strash gatesimp aignet2))))

  (defthm reg-copy-values-of-aignet-copy-dfs-list
    (implies (aignet-input-copies-in-bounds copy aignet aignet2)
             (b* (((mv ?new-mark ?new-copy ?new-strash ?new-aignet2)
                   (aignet-copy-dfs-list lits aignet mark copy strash gatesimp aignet2)))
               (equal (reg-copy-values n invals regvals aignet new-copy new-aignet2)
                      (reg-copy-values n invals regvals aignet copy aignet2))))
    :hints ((acl2::just-induct-and-expand
             (aignet-copy-dfs-list
              lits aignet mark copy
              strash gatesimp aignet2))))

  (defthm dfs-copy-onto-invar-of-node-list-fix
    (implies (dfs-copy-onto-invar aignet mark copy aignet2)
             (dfs-copy-onto-invar aignet mark copy (node-list-fix aignet2)))
    :hints (("goal" :expand ((dfs-copy-onto-invar aignet mark copy (node-list-fix aignet2))))))

  (defthm dfs-copy-onto-invar-holds-of-aignet-copy-dfs-list
    (implies (and ;; (aignet-idp id aignet)
              (dfs-copy-onto-invar aignet mark copy aignet2)
              (aignet-input-copies-in-bounds copy aignet aignet2)
              (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-list
                    lits aignet mark copy
                    strash gatesimp aignet2)))
               (dfs-copy-onto-invar aignet mark copy aignet2))))

  (defthm lit-eval-lit-copy-of-aignet-copy-dfs-list
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-list
                    lits aignet mark copy
                    strash gatesimp aignet2)))
               (implies (equal 1 (get-bit (lit->var lit) mark))
                        (equal (lit-eval (lit-copy lit copy) invals regvals aignet2)
                               (lit-eval lit
                                         (input-copy-values 0 invals regvals aignet copy aignet2)
                                         (reg-copy-values 0 invals regvals aignet copy aignet2)
                                         aignet)))))
    :hints (("goal" :use ((:instance dfs-copy-onto-invar-holds-of-aignet-copy-dfs-list))
             :in-theory (e/d (lit-copy lit-eval)
                             (dfs-copy-onto-invar-holds-of-aignet-copy-dfs-list))
             :do-not-induct t)))

  (defthm lit-list-marked-preserved-by-aignet-copy-dfs-list
    (implies (lit-list-marked lits mark)
             (lit-list-marked lits (mv-nth 0 (aignet-copy-dfs-list lits1 aignet mark copy strash gatesimp aignet2))))
    :hints(("Goal" :in-theory (enable lit-list-marked)
            :induct (lit-list-marked lits mark))))

  (defthm lit-list-marked-of-aignet-copy-dfs-list
    (lit-list-marked lits (mv-nth 0 (aignet-copy-dfs-list lits aignet mark copy strash gatesimp aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-list lit-list-marked))))

  (defthm aignet-lit-list-copies-in-bounds-of-aignet-copy-dfs-list
    (implies (and (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv ?mark copy ?strash aignet2)
                   (aignet-copy-dfs-list
                    lits aignet mark copy
                    strash gatesimp aignet2)))
               (aignet-lit-listp (lit-list-copies lits copy) aignet2)))
    :hints(("Goal" :in-theory (enable aignet-copy-dfs-list lit-list-copies aignet-lit-listp))))

  (defthm aignet-eval-conjunction-of-lit-list-copies-when-dfs-copy-onto-invar
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (lit-list-marked lits mark))
             (equal (aignet-eval-conjunction (lit-list-copies lits copy) invals regvals aignet2)
                    (aignet-eval-conjunction lits
                                             (input-copy-values 0 invals regvals aignet copy aignet2)
                                             (reg-copy-values 0 invals regvals aignet copy aignet2)
                                             aignet)))
    :hints(("Goal" :in-theory (enable aignet-eval-conjunction
                                      lit-list-marked
                                      lit-list-copies
                                      lit-copy)
            :expand ((:free (lit invals regvals) (lit-eval lit invals regvals aignet))))))

  (defthm aignet-eval-conjunction-of-lit-list-copies-dfs
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-list
                    lits1 aignet mark copy
                    strash gatesimp aignet2)))
               (implies (lit-list-marked lits mark)
                        (equal (aignet-eval-conjunction (lit-list-copies lits copy) invals regvals aignet2)
                               (aignet-eval-conjunction lits
                                                        (input-copy-values 0 invals regvals aignet copy aignet2)
                                                        (reg-copy-values 0 invals regvals aignet copy aignet2)
                                                        aignet)))))
    :hints (("goal" :use ((:instance aignet-eval-conjunction-of-lit-list-copies-when-dfs-copy-onto-invar
                           (mark (mv-nth 0 (aignet-copy-dfs-list
                                            lits1 aignet mark copy
                                            strash gatesimp aignet2)))
                           (copy (mv-nth 1 (aignet-copy-dfs-list
                                            lits1 aignet mark copy
                                            strash gatesimp aignet2)))
                           (aignet2 (mv-nth 3 (aignet-copy-dfs-list
                                               lits1 aignet mark copy
                                               strash gatesimp aignet2)))))
             :in-theory (disable aignet-eval-conjunction-of-lit-list-copies-when-dfs-copy-onto-invar))))

  (defthm lit-eval-list-of-lit-list-copies-when-dfs-copy-onto-invar
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (lit-list-marked lits mark))
             (equal (lit-eval-list (lit-list-copies lits copy) invals regvals aignet2)
                    (lit-eval-list lits
                                             (input-copy-values 0 invals regvals aignet copy aignet2)
                                             (reg-copy-values 0 invals regvals aignet copy aignet2)
                                             aignet)))
    :hints(("Goal" :in-theory (enable lit-eval-list
                                      lit-list-marked
                                      lit-list-copies
                                      lit-copy)
            :expand ((:free (lit invals regvals) (lit-eval lit invals regvals aignet))))))

  (defthm lit-eval-list-of-lit-list-copies-of-dfs
    (implies (and (dfs-copy-onto-invar aignet mark copy aignet2)
                  (aignet-input-copies-in-bounds copy aignet aignet2)
                  (aignet-marked-copies-in-bounds copy mark aignet2))
             (b* (((mv mark copy ?strash aignet2)
                   (aignet-copy-dfs-list
                    lits1 aignet mark copy
                    strash gatesimp aignet2)))
               (implies (lit-list-marked lits mark)
                        (equal (lit-eval-list (lit-list-copies lits copy) invals regvals aignet2)
                               (lit-eval-list lits
                                              (input-copy-values 0 invals regvals aignet copy aignet2)
                                              (reg-copy-values 0 invals regvals aignet copy aignet2)
                                              aignet)))))
    :hints (("goal" :use ((:instance lit-eval-list-of-lit-list-copies-when-dfs-copy-onto-invar
                           (mark (mv-nth 0 (aignet-copy-dfs-list
                                            lits1 aignet mark copy
                                            strash gatesimp aignet2)))
                           (copy (mv-nth 1 (aignet-copy-dfs-list
                                            lits1 aignet mark copy
                                            strash gatesimp aignet2)))
                           (aignet2 (mv-nth 3 (aignet-copy-dfs-list
                                               lits1 aignet mark copy
                                               strash gatesimp aignet2)))))
             :in-theory (disable lit-eval-list-of-lit-list-copies-when-dfs-copy-onto-invar)))))




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
       (copy (resize-lits (num-fanins aignet) copy))
       ((mv copy aignet2) (aignet-copy-ins aignet copy aignet2)))
    (aignet-copy-regs aignet copy aignet2))
  ///
  
  (defret copy-length-of-init-copy-comb
    (equal (len new-copy) (num-fanins aignet)))

  ;; (defret aignet-copies-ok-of-init-copy-comb
  ;;   (aignet-copies-ok (+ 1 (fanin-count (find-max-fanin aignet))) new-copy new-aignet2))

  (local (defthm nth-lit-of-nil
           (equal (nth-lit n nil) 0)
           :hints(("Goal" :in-theory (enable nth-lit)))))

  (defret aignet-copies-in-bounds-of-init-copy-comb
    (aignet-copies-in-bounds new-copy new-aignet2)
    :hints (("goal" :in-theory (enable aignet-copies-in-bounds))
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
                    (init-copy-comb aignet nil nil))))

  (defret input-copy-values-of-init-copy-comb
    (bits-equiv (input-copy-values 0 invals regvals aignet new-copy new-aignet2)
                (take (num-ins aignet) invals)))

  (defret reg-copy-values-of-init-copy-comb
    (bits-equiv (reg-copy-values 0 invals regvals aignet new-copy new-aignet2)
                (take (num-regs aignet) regvals))))




(defsection output-fanins-comb-equiv
  (defun-sk output-fanins-comb-equiv (aignet copy aignet2)
    (forall (n invals regvals)
            (implies (< (nfix n) (num-outs aignet))
                     (equal (lit-eval (lit-copy (fanin 0 (lookup-stype n :po aignet)) copy)
                                      invals regvals aignet2)
                            (lit-eval (fanin 0 (lookup-stype n :po aignet))
                                      invals regvals aignet))))
    :rewrite :direct)
  (in-theory (disable output-fanins-comb-equiv)))

(defsection nxst-fanins-comb-equiv
  (defun-sk nxst-fanins-comb-equiv (aignet copy aignet2)
    (forall (n invals regvals)
            (implies (< (nfix n) (num-regs aignet))
                     (equal (lit-eval (lit-copy (lookup-reg->nxst n aignet) copy)
                                      invals regvals aignet2)
                            (lit-eval (lookup-reg->nxst n aignet)
                                      invals regvals aignet))))
    :rewrite :direct)
  (in-theory (disable nxst-fanins-comb-equiv)))




(define finish-copy-comb ((aignet)
                          (copy)
                          (aignet2))
  :guard (and (<= (num-fanins aignet) (lits-length copy))
              (<= (num-regs aignet) (num-regs aignet2))
              (ec-call (aignet-po-copies-in-bounds copy aignet aignet2))
              (ec-call (aignet-nxst-copies-in-bounds copy aignet aignet2)))
  :returns (new-aignet2)
  (b* ((aignet2 (mbe :logic (non-exec (node-list-fix aignet2))
                     :exec aignet2))
       (aignet2 (aignet-copy-outs aignet copy aignet2)))
    (aignet-copy-nxsts aignet copy aignet2))
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
                '(:cases ((< (nfix n) (num-outs aignet)))))))

  (local (acl2::use-trivial-ancestors-check))

  (defret nxsts-comb-equiv-of-finish-copy-comb
    (implies (and (nxst-fanins-comb-equiv aignet copy aignet2)
                  (equal (stype-count :nxst aignet2) 0)
                  (equal (stype-count :reg aignet) (stype-count :reg aignet2))
                  (aignet-nxst-copies-in-bounds copy aignet aignet2))
             (nxsts-comb-equiv new-aignet2 aignet))
    :hints(("Goal" :in-theory (e/d (nxsts-comb-equiv nxst-eval
                                                     lookup-reg->nxst-of-out-of-bounds-reg)
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
                '(:cases ((< (nfix n) (num-regs aignet)))))))

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
