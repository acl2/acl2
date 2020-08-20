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
(include-book "semantics")
(include-book "lit-lists")
(include-book "refcounts")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (include-book "centaur/aignet/bit-lemmas" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))

(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(local (std::add-default-post-define-hook :fix))



(local (in-theory (disable lookup-id-in-bounds-when-positive
                           ;; lookup-id-out-of-bounds
                           satlink::equal-of-lit-negate-backchain
                           satlink::lit-negate-not-equal-when-vars-mismatch
                           )))

;; Returns (mv is-mux cond-lit tb-lit fb-lit).
;; A mux node is of the form
;; (and (not (and c (not tb))) (not (and (not c) (not fb))))
;; or a permutation.
(define id-is-mux ((id natp) aignet)
  :guard (id-existsp id aignet)
  :returns (mv is-mux
               (cond-lit litp)
               (true-branch litp)
               (false-branch litp))

  (b* (((unless (int= (id->type id aignet) (gate-type)))
        (mv nil 0 0 0))
       (f0 (gate-id->fanin0 id aignet))
       (f1 (gate-id->fanin1 id aignet))
       ((when (int= (id->regp id aignet) 1))
        ;; XOR gate can be viewed as a type of mux -- (if f0 (not f1) f1)
        (mv t f0 (lit-negate f1) f1))
       ((unless (and (int= (lit-neg f0) 1)
                     (int= (lit-neg f1) 1)
                     (int= (id->type (lit-id f0) aignet) (gate-type))
                     (int= (id->regp (lit-id f0) aignet) 0)
                     (int= (id->type (lit-id f1) aignet) (gate-type))
                     (int= (id->regp (lit-id f1) aignet) 0)))
        (mv nil 0 0 0))
       (f00 (gate-id->fanin0 (lit-id f0) aignet))
       (f10 (gate-id->fanin1 (lit-id f0) aignet))
       (f01 (gate-id->fanin0 (lit-id f1) aignet))
       (f11 (gate-id->fanin1 (lit-id f1) aignet))
       (nf01 (lit-negate f01))
       (nf11 (lit-negate f11))
       ((when (int= f00 nf01))
        (mv t f00 (lit-negate f10) nf11))
       ((when (int= f00 nf11))
        (mv t f00 (lit-negate f10) nf01))
       ((when (int= f10 nf01))
        (mv t f10 (lit-negate f00) nf11))
       ((when (int= f10 nf11))
        (mv t f10 (lit-negate f00) nf01)))
    (mv nil 0 0 0))
  ///

  (defcong nat-equiv equal (id-is-mux id aignet) 1)

  (defthm id-is-mux-produces-aignet-lits
    (b* (((mv ?muxp c tb fb) (id-is-mux id aignet)))
      (and (aignet-litp c aignet)
           (aignet-litp tb aignet)
           (aignet-litp fb aignet))))

  (defthmd lit-eval-of-mk-lit-split-rw
    (implies (equal lit1 (mk-lit (lit-id lit) neg))
             (equal (lit-eval lit1 in-vals reg-vals aignet)
                    (acl2::b-xor (acl2::b-xor neg (lit-neg lit))
                                 (lit-eval lit in-vals reg-vals aignet))))
    :hints(("Goal" :in-theory (enable lit-eval acl2::B-xor))))

  (local (defthm bit-mux-rws
           (and (equal (b-and (b-not (b-and a b)) (b-not (b-and (b-not a) d)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and a b)) (b-not (b-and d (b-not a))))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and b a)) (b-not (b-and d (b-not a))))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and b a)) (b-not (b-and (b-not a) d)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and (b-not a) d)) (b-not (b-and a b)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and d (b-not a))) (b-not (b-and a b)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and d (b-not a))) (b-not (b-and b a)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d))))
                (equal (b-and (b-not (b-and (b-not a) d)) (b-not (b-and b a)))
                       (b-ior (b-and a (b-not b)) (b-and (b-not a) (b-not d)))))
           :hints(("Goal" :in-theory (enable b-and b-ior)))))

  ;; This is a pretty awkward rewrite rule, but maybe not as bad as it
  ;; appears.  The first hyp will basically fail immediately if we don't know
  ;; that the ID is a mux.  Might need other tricks to prevent it from opening
  ;; when we don't want it to.
  (defthmd id-eval-when-id-is-mux
    (b* (((mv muxp c tb fb) (id-is-mux id aignet)))
      (implies (and muxp
                    (aignet-idp id aignet))
               (equal (id-eval id in-vals reg-vals aignet)
                      (acl2::b-ior (acl2::b-and
                                    (lit-eval c in-vals reg-vals aignet)
                                    (lit-eval tb in-vals reg-vals aignet))
                                   (acl2::b-and
                                    (acl2::b-not (lit-eval c in-vals reg-vals aignet))
                                    (lit-eval fb in-vals reg-vals aignet))))))
    :hints (("goal" :in-theory (e/d ;; (lit-eval-of-mk-lit-split-rw
                                    ;;  equal-1-by-bitp
                                    ;;  eval-and-of-lits)
                                (id-eval eval-and-of-lits eval-xor-of-lits
                                         lit-eval-of-mk-lit-split-rw)
                                ( acl2::b-xor acl2::b-and
                                              acl2::b-ior acl2::b-not))
             :expand ((:free (ftype) (lit-eval (fanin ftype (lookup-id id aignet))
                                               in-vals reg-vals aignet))))
            (and stable-under-simplificationp
                 '(:in-theory (enable b-ior b-and b-xor))))))

(defsection aignet-eval-conjunction-set-congruence

  (local (defthm aignet-eval-conjunction-when-member
           (implies (And (member lit lits)
                         (equal (lit-eval lit invals regvals aignet) 0))
                    (equal (aignet-eval-conjunction lits invals regvals aignet) 0))
           :hints(("Goal" :in-theory (enable member aignet-eval-conjunction)))))

  (local (defthm aignet-eval-conjunction-of-subset
           (implies (and (subsetp lits1 lits2)
                         (equal 1 (aignet-eval-conjunction lits2 invals regvals aignet)))
                    (equal (aignet-eval-conjunction lits1 invals regvals aignet) 1))
           :hints(("Goal" :in-theory (enable subsetp aignet-eval-conjunction)))))

  (defcong acl2::set-equiv equal (aignet-eval-conjunction lits invals regvals aignet) 1
    :hints(("Goal" :in-theory (enable acl2::set-equiv)
            :cases ((equal 1 (aignet-eval-conjunction lits invals regvals aignet)))))))

(defsection aignet-lit-listp-set-congruence
  (defthmd aignet-lit-listp-when-member
    (implies (And (not (aignet-litp lit aignet))
                  (member lit lits))
             (not (aignet-lit-listp lits aignet)))
    :hints(("Goal" :in-theory (enable member aignet-lit-listp))))

  (defthmd aignet-lit-listp-when-subsetp
    (implies (and (aignet-lit-listp lits2 aignet)
                  (subsetp lits1 lits2))
             (aignet-lit-listp lits1 aignet))
    :hints(("Goal" :in-theory (enable subsetp aignet-lit-listp
                                      aignet-lit-listp-when-member))))

  (defcong acl2::set-equiv equal (aignet-lit-listp lits aignet) 1
    :hints(("Goal" :in-theory (enable acl2::set-equiv
                                      aignet-lit-listp-when-subsetp)
            :cases ((aignet-lit-listp lits aignet))))))


(defsection collect-supergate


  (defthm aignet-lit-listp-of-append
    (implies (and (aignet-lit-listp a aignet)
                  (aignet-lit-listp b aignet))
             (aignet-lit-listp (append a b) aignet)))

  (local (defthmd equal-1-by-bitp
         (implies (acl2::bitp x)
                  (equal (equal x 1) (not (equal x 0))))
         :hints(("Goal" :in-theory (enable acl2::bitp)))))
  

  (local
   (progn

     (in-theory (enable aignet-eval-conjunction))

     (defthm b-and-associative
       (equal (acl2::b-and (acl2::b-and a b) c)
              (acl2::b-and a (acl2::b-and b c)))
       :hints(("Goal" :in-theory (enable acl2::b-and))))

     (defthm b-and-commute-2
       (equal (acl2::b-and b (acl2::b-and a c))
              (acl2::b-and a (acl2::b-and b c)))
       :hints(("Goal" :in-theory (enable acl2::b-and))))

     (defthm aignet-eval-conjunction-of-append
       (equal (aignet-eval-conjunction (append a b) invals regvals aignet)
              (acl2::b-and (aignet-eval-conjunction a invals regvals aignet)
                           (aignet-eval-conjunction b invals regvals aignet))))

     (local (in-theory (enable equal-1-by-bitp)))

     (defthm acl2::b-xor-of-nonzero
       (implies (equal x 1)
                (equal (acl2::b-xor x y)
                       (acl2::b-not y))))

     (defthm acl2::b-xor-of-zero
       (implies (not (equal x 1))
                (equal (acl2::b-xor x y)
                       (acl2::bfix y)))
       :hints(("Goal" :in-theory (enable acl2::b-xor))))

     (defthm acl2::b-and-collapse
       (equal (acl2::b-and x (acl2::b-and x y))
              (acl2::b-and x y))
       :hints(("Goal" :in-theory (enable acl2::b-and))))

     (defthm and-of-eval-list-when-member
       (implies (member lit lst)
                (equal (acl2::b-and (lit-eval lit invals regvals aignet)
                                    (aignet-eval-conjunction lst invals regvals aignet))
                       (aignet-eval-conjunction lst invals regvals aignet))))

     (defthm and-of-eval-list-when-fix-member
       (implies (member (lit-fix lit) (lit-list-fix lst))
                (equal (acl2::b-and (lit-eval lit invals regvals aignet)
                                    (aignet-eval-conjunction lst invals regvals aignet))
                       (aignet-eval-conjunction lst invals regvals aignet))))))

  (defthm aignet-eval-conjunction-when-0
    (implies (member 0 lst)
             (equal (aignet-eval-conjunction lst invals regvals aignet)
                    0)))

  (local (defthm and-of-eval-list-when-complement-member
           (implies (member (lit-negate lit) lst)
                    (equal (acl2::b-and (lit-eval lit invals regvals aignet)
                                        (aignet-eval-conjunction lst invals regvals aignet))
                           0))
           :hints(("Goal" :induct t)
                  (and stable-under-simplificationp
                       '(:in-theory (enable acl2::b-and b-xor lit-eval))))))

  (local (defthmd lit-eval-when-negate-equal
           (implies (equal (lit-negate a) b)
                    (equal (lit-eval a invals regvals aignet)
                           (b-not (lit-eval b invals regvals aignet))))
           :hints (("goal" :expand ((lit-eval a invals regvals aignet)
                                    (lit-eval b invals regvals aignet))))))

  (local (defthm and-of-eval-list-when-complement-member-fix
           (implies (member (lit-negate lit) (lit-list-fix lst))
                    (equal (acl2::b-and (lit-eval lit invals regvals aignet)
                                        (aignet-eval-conjunction lst invals regvals aignet))
                           0))
           :hints(("Goal" :induct t :in-theory (enable lit-list-fix))
                  (and stable-under-simplificationp
                       '(:in-theory (enable acl2::b-and b-xor lit-eval
                                            lit-eval-when-negate-equal))))))
  
  (define lit-collect-supergate ((lit litp)
                                 top use-muxes
                                 (limit natp)
                                 (supergate lit-listp)
                                 aignet-refcounts aignet)
    :guard (and (< (lit-id lit) (u32-length aignet-refcounts))
                (fanin-litp lit aignet)
                (true-listp supergate))
    :measure (lit-id lit)
    :verify-guards nil
    :returns (mv (res lit-listp :hyp (and (lit-listp supergate) (litp lit)))
                 (rem-limit natp :rule-classes :type-prescription))
    (b* ((lit (lit-fix lit))
         (supergate (lit-list-fix supergate))
         (limit (lnfix limit))
         ((when (or (int= (lit-neg lit) 1)
                    (not (int= (id->type (lit-id lit) aignet) (gate-type)))
                    (int= (id->regp (lit-id lit) aignet) 1) ;; xor
                    (and (not top) (< 1 (get-u32 (lit-id lit) aignet-refcounts)))
                    (and use-muxes
                         (b* (((mv muxp & & &) (id-is-mux (lit-id lit) aignet)))
                           muxp))
                    (eql 0 limit)))
          (mv ;; (cond ;; ((or (member (lit-negate lit) supergate)
              ;;       ;;      (int= (lit-fix lit) 0))
              ;;       ;;  ;; Complementary literal is in the supergate, so add 0.
              ;;       ;;  (list 0))
              ;;  ;; ((member lit supergate) supergate)
              ;;  (t (cons lit supergate)))
           (cons lit supergate)
           (if (eql 0 limit) limit (1- limit))))
         ((mv supergate limit)
          (lit-collect-supergate (gate-id->fanin0 (lit-id lit) aignet)
                                 nil use-muxes limit supergate aignet-refcounts aignet)))
      (lit-collect-supergate (gate-id->fanin1 (lit-id lit) aignet)
                             nil use-muxes limit supergate aignet-refcounts aignet))
    ///
  ;; (defthm true-listp-of-collect-supergate
  ;;   (implies (true-listp supergate)
  ;;            (true-listp (lit-collect-supergate lit top use-muxes supergate
  ;;                                               aignet-refcounts aignet)))
  ;;   :hints (("goal" :induct (lit-collect-supergate lit top use-muxes supergate
  ;;                                                  aignet-refcounts aignet)
  ;;            :do-not-induct t
  ;;            :in-theory (enable (:induction lit-collect-supergate))
  ;;            :expand ((:free (top use-muxes)
  ;;                      (lit-collect-supergate lit top use-muxes supergate
  ;;                                             aignet-refcounts aignet))))))
    (local (defthm lit-listp-true-listp
             (implies (lit-listp x) (true-listp x))
             :rule-classes :forward-chaining))
    (verify-guards lit-collect-supergate)
    (defret aignet-lit-listp-of-collect-supergate
      (implies (and (aignet-litp lit aignet)
                    (aignet-lit-listp supergate aignet))
               (aignet-lit-listp res aignet))
      :hints (("goal" :induct <call>
               :do-not-induct t
               :in-theory (disable (:definition lit-collect-supergate))
               :expand ((:free (top use-muxes) <call>)))))

    (defret collect-supergate-correct
      (equal (aignet-eval-conjunction res invals regvals aignet)
             (acl2::b-and (lit-eval lit invals regvals aignet)
                          (aignet-eval-conjunction supergate invals regvals aignet)))
      :hints (("goal" :induct <call>
               :do-not-induct t
               :in-theory (e/d (eval-and-of-lits)
                               ((:definition lit-collect-supergate)))
               :expand ((:free (top use-muxes) <call>)))
              (and stable-under-simplificationp
                   '(:expand ((lit-eval lit invals regvals aignet)
                              (id-eval (lit-id lit) invals regvals aignet))))))

    (defret true-listp-of-<fn>
      (implies (true-listp supergate)
               (true-listp res)))
    
    (local (in-theory (disable lookup-id-out-of-bounds
                               member
                               (:d lit-collect-supergate))))

    (defsection lits-max-id-val-supergate
      (local (in-theory (enable lits-max-id-val)))
      (defthmd lits-max-id-val-of-supergate
        (<= (lits-max-id-val (mv-nth 0 (lit-collect-supergate
                                        lit top use-muxes limit supergate aignet-refcounts aignet)))
            (max (lit-id lit)
                 (lits-max-id-val supergate)))
        :hints(("Goal" :in-theory (enable lit-collect-supergate))))


      ;; measure decreases on children of a supergate
      (defthm supergate-decr-top
        (implies (and (int= (id->type id aignet) (gate-type))
                      (not (and (or use-muxes
                                    (eql (id->regp id aignet) 1))
                                (mv-nth 0 (id-is-mux id aignet))))
                      (not (zp limit)))
                 (< (lits-max-id-val (mv-nth 0 (lit-collect-supergate
                                                (mk-lit id 0)
                                                t use-muxes limit nil aignet-refcounts aignet)))
                    (nfix id)))
        :hints (("goal" :expand ((:free (use-muxes)
                                  (lit-collect-supergate
                                   (mk-lit id 0)
                                   t use-muxes limit nil aignet-refcounts aignet)))
                 :use ((:instance lits-max-id-val-of-supergate
                        (lit (gate-id->fanin0 id aignet))
                        (top nil)
                        (supergate nil))
                       (:instance lits-max-id-val-of-supergate
                        (lit (gate-id->fanin1 id aignet))
                        (top nil)
                        (supergate (mv-nth 0 (lit-collect-supergate
                                              (gate-id->fanin0 id aignet)
                                              nil use-muxes limit nil aignet-refcounts aignet)))
                        (limit (mv-nth 1 (lit-collect-supergate
                                          (gate-id->fanin0 id aignet)
                                          nil use-muxes limit nil aignet-refcounts aignet)))))
                 :in-theory (e/d () (lits-max-id-val-of-supergate)))
                (and stable-under-simplificationp
                     '(:in-theory (e/d (id-is-mux)
                                       ;; (id-type-when-is-mux)
                                       ))))
        :rule-classes (:rewrite :linear)))))


(define aignet-eval-parity ((lits lit-listp) invals regvals aignet)
  :guard (and (aignet-lit-listp lits aignet)
              (<= (num-ins aignet) (bits-length invals))
              (<= (num-regs aignet) (bits-length regvals)))
  :returns (res bitp)
  (if (atom lits)
      0
    (b-xor (lit-eval (car lits) invals regvals aignet)
           (aignet-eval-parity (cdr lits) invals regvals aignet)))
  ///
  (defthm aignet-eval-parity-preserved-by-extension
    (implies (and (aignet-extension-binding)
                  (aignet-lit-listp lits orig))
             (equal (aignet-eval-parity lits invals regvals new)
                    (aignet-eval-parity lits invals regvals orig)))))



(define lit-collect-superxor ((lit litp)
                              top
                              (limit natp)
                              (superxor lit-listp)
                              aignet-refcounts aignet)
  :guard (and (< (lit-id lit) (u32-length aignet-refcounts))
              (fanin-litp lit aignet)
              (true-listp superxor))
  :measure (lit-id lit)
  :verify-guards nil
  :returns (mv (res lit-listp :hyp (and (lit-listp superxor) (litp lit)))
               (rem-limit natp :rule-classes :type-prescription))
  (b* ((lit (lit-fix lit))
       (superxor (lit-list-fix superxor))
       ((when (or (int= (lit-neg lit) 1)
                  (not (int= (id->type (lit-id lit) aignet) (gate-type)))
                  (int= (id->regp (lit-id lit) aignet) 0) ;; and
                  (and (not top) (< 1 (get-u32 (lit-id lit) aignet-refcounts)))
                  (zp limit)))
        (mv (cons lit superxor)
            (if (zp limit) 0 (1- limit))))
       ((mv superxor limit)
        (lit-collect-superxor (gate-id->fanin0 (lit-id lit) aignet)
                              nil limit superxor aignet-refcounts aignet)))
    (lit-collect-superxor (gate-id->fanin1 (lit-id lit) aignet)
                          nil limit superxor aignet-refcounts aignet))
  ///
  ;; (defthm true-listp-of-collect-superxor
  ;;   (implies (true-listp superxor)
  ;;            (true-listp (lit-collect-superxor lit top use-muxes superxor
  ;;                                               aignet-refcounts aignet)))
  ;;   :hints (("goal" :induct (lit-collect-superxor lit top use-muxes superxor
  ;;                                                  aignet-refcounts aignet)
  ;;            :do-not-induct t
  ;;            :in-theory (enable (:induction lit-collect-superxor))
  ;;            :expand ((:free (top use-muxes)
  ;;                      (lit-collect-superxor lit top use-muxes superxor
  ;;                                             aignet-refcounts aignet))))))
  (local (defthm lit-listp-true-listp
           (implies (lit-listp x) (true-listp x))))
  (verify-guards lit-collect-superxor)
  (defret aignet-lit-listp-of-collect-superxor
    (implies (and (aignet-litp lit aignet)
                  (aignet-lit-listp superxor aignet))
             (aignet-lit-listp res
              aignet))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :in-theory (disable (:definition lit-collect-superxor))
             :expand ((:free (top) <call>)))))

  (defret collect-superxor-correct
    (equal (aignet-eval-parity res invals regvals aignet)
           (acl2::b-xor (lit-eval lit invals regvals aignet)
                        (aignet-eval-parity superxor invals regvals aignet)))
    :hints (("goal" :induct <call>
             :do-not-induct t
             :in-theory (e/d (eval-xor-of-lits)
                             ((:definition lit-collect-superxor)))
             :expand ((:free (top) <call>)))
            (and stable-under-simplificationp
                 '(:expand ((lit-eval lit invals regvals aignet)
                            (aignet-eval-parity (cons lit superxor) invals regvals aignet)
                            (id-eval (lit-id lit) invals regvals aignet))))))

  (defret true-listp-of-<fn>
      (implies (true-listp superxor)
               (true-listp res)))

  (local (in-theory (disable lookup-id-out-of-bounds
                             lookup-id-in-bounds-when-positive
                             member
                             (:d lit-collect-superxor))))

  (defretd lits-max-id-val-of-lit-collect-superxor
    (<= (lits-max-id-val res)
        (max (lit-id lit) (lits-max-id-val superxor)))
    :hints(("Goal" :in-theory (enable lits-max-id-val)
            :induct <call>
            :expand ((:free (top) <call>)))))

  (defret superxor-decr-top
    (implies (and (int= (id->type id aignet) (gate-type))
                  (eql (id->regp id aignet) 1)
                  (not (zp limit)))
             (< (lits-max-id-val
                 (mv-nth 0 (lit-collect-superxor
                            (mk-lit id 0)
                            t limit nil aignet-refcounts aignet)))
                (nfix id)))
    :hints (("goal" :expand ((:free (use-muxes)
                              (lit-collect-superxor
                               (mk-lit id 0)
                               t limit nil aignet-refcounts aignet)))
             :use ((:instance lits-max-id-val-of-lit-collect-superxor
                    (lit (gate-id->fanin0 id aignet))
                    (top nil)
                    (superxor nil))
                   (:instance lits-max-id-val-of-lit-collect-superxor
                    (lit (gate-id->fanin1 id aignet))
                    (top nil)
                    (superxor (mv-nth 0 (lit-collect-superxor
                                          (gate-id->fanin0 id aignet)
                                          nil limit nil aignet-refcounts aignet)))
                    (limit  (mv-nth 1 (lit-collect-superxor
                                       (gate-id->fanin0 id aignet)
                                       nil limit nil aignet-refcounts aignet)))))
             :in-theory (e/d () (lits-max-id-val-of-lit-collect-superxor
                                 lit-collect-superxor)))
            (and stable-under-simplificationp
                 '(:in-theory (enable id-is-mux))))
    :rule-classes (:rewrite :linear)))
